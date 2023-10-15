#include "llvm/Pass.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <map>
#include <set>
#include <vector>

enum CAT_API {
  CAT_new,
  CAT_add,
  CAT_sub,
  CAT_get,
  CAT_set,
  CAT_destroy
};

using namespace llvm;

namespace {
  struct CAT : public FunctionPass {
    static char ID; 
    Module* currentModule;
    std::map<Function *, CAT_API> CATMap;

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      currentModule = &M;
      CATMap[M.getFunction("CAT_new")] = CAT_new;
      CATMap[M.getFunction("CAT_add")] = CAT_add;
      CATMap[M.getFunction("CAT_sub")] = CAT_sub;
      CATMap[M.getFunction("CAT_get")] = CAT_get;
      CATMap[M.getFunction("CAT_set")] = CAT_set;
      CATMap[M.getFunction("CAT_destroy")] = CAT_destroy;
      return false;
    }

    void createReachingDefinitions(Function &F, 
                                   std::map<Instruction *, std::set<Instruction *>> &inSets, 
                                   std::map<Instruction *, std::set<Instruction *>> &outSets) {
      std::vector<Instruction *> numToInst;
      std::map<Instruction *, unsigned> instToNum;
      std::map<Instruction *, BitVector> gen;
      std::map<Instruction *, BitVector> kill;
      std::vector<Instruction *> toKill;
      std::map<Instruction *, BitVector> in;
      std::map<Instruction *, BitVector> out;

      unsigned num = 0;
      unsigned size = 0;
      for (auto &B : F) {
        size += B.size();
      }

      for (auto &I : instructions(F)) {
        numToInst.push_back(&I);
        instToNum[&I] = num;
        in[&I] = BitVector(size);
        out[&I] = BitVector(size);
        BitVector genSet = BitVector(size);
        BitVector killSet = BitVector(size);
        
        if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          switch (CATMap[callee]) {
            case CAT_new:
              genSet.set(num);
              break;
            case CAT_add:
            case CAT_sub:
            case CAT_set:
              genSet.set(num);
              toKill.push_back(&I);
              break;
            default:
              break;
          }
        }

        gen[&I] = genSet;
        kill[&I] = killSet;
        num++;
      }

      for (auto inst : toKill) {
        CallInst *call = cast<CallInst>(inst);
        Instruction *arg = cast<Instruction>(call->getArgOperand(0));

        kill[inst].set(instToNum[arg]);
        kill[inst] |= kill[arg];
        for (auto bit : kill[inst].set_bits()) {
          kill[numToInst[bit]].set(instToNum[inst]);
        }
      }

      bool done;
      do {
        done = true;

        for (auto &B : F) {
          for (auto &I : B) {
            Instruction *prev = I.getPrevNode();
            if (!prev) {
              for (auto pred : predecessors(&B)) {
                in[&I] |= out[pred->getTerminator()];
              }
            } else {
              in[&I] |= out[prev];
            }

            BitVector tempOut = BitVector(size);
            tempOut |= in[&I];
            tempOut.reset(kill[&I]);
            tempOut |= gen[&I];

            done = done && (out[&I] == tempOut);
            out[&I] = tempOut;
          }
        }
      } while (!done);

      for (auto &I : instructions(F)) {
          std::set<Instruction *> inSet;
          std::set<Instruction *> outSet;

          for (auto bit : in[&I].set_bits()) {
            inSet.insert(numToInst[bit]);
          }
          for (auto bit : out[&I].set_bits()) {
            outSet.insert(numToInst[bit]);
          }

          inSets[&I] = inSet;
          outSets[&I] = outSet;
      }
      return;
    }

    Value *isConstant(std::set<Instruction *> inSet, Value *v) {
      Instruction *valInst = cast<Instruction>(v);
      Value *valPtr = nullptr;
      bool initialized = false;
      int64_t c;

      for (auto inst : inSet) {
        if (CallInst *call = dyn_cast<CallInst>(inst)) {
          Function *callee = call->getCalledFunction();
          switch (CATMap[callee]) {
            case CAT_new:
              if (valInst == inst) {
                if (ConstantInt *constant = dyn_cast<ConstantInt>(call->getArgOperand(0))) {
                  if (!initialized) {
                    c = constant->getSExtValue();
                    valPtr = call->getArgOperand(0);
                    initialized = true;
                  } else if (c != constant->getSExtValue()) {
                    return nullptr;
                  }
                }
              }
              break;
            case CAT_add:
            case CAT_sub:
              if (valInst == call->getArgOperand(0)) {
                return nullptr;
              }
              break;
            case CAT_set:
              if (valInst == call->getArgOperand(0)) {
                if (ConstantInt *constant = dyn_cast<ConstantInt>(call->getArgOperand(1))) {
                  if (!initialized) {
                    c = constant->getSExtValue();
                    valPtr = call->getArgOperand(1);
                    initialized = true;
                  } else if (c != constant->getSExtValue()) {
                    return nullptr;
                  }
                }                
              }
              break;
            default:
              break;
          }
        }
      }
      
      return valPtr;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      bool modified = false;
      std::map<Instruction *, std::set<Instruction *>> inSets;
      std::map<Instruction *, std::set<Instruction *>> outSets;
      createReachingDefinitions(F, inSets, outSets);

      // Constant propagation
      for (auto &B : F) {
        std::map<Instruction *, Value *> toReplace;

        for (auto &I : B) {
          if (CallInst *call = dyn_cast<CallInst>(&I)) {
            Function *callee = call->getCalledFunction();
            if (currentModule->getFunction("CAT_get") == callee) {
              if (Value* c = isConstant(inSets[&I], call->getArgOperand(0))) {
                toReplace[&I] = c;
                modified = true;
              }
            }
          }
          if (PHINode *phi = dyn_cast<PHINode>(&I)) {
            for (unsigned j = 0; j < phi->getNumIncomingValues(); j++) {
              Value *phiVal = phi->getIncomingValue(j);
              errs() << *phiVal << "\n";
            }
          }
        }

        for (auto [I, constValue] : toReplace) {
          BasicBlock::iterator ii(I);
          ReplaceInstWithValue(B.getInstList(), ii, constValue);
        }
      }
      
      // Constant folding
      std::vector<Instruction *> toDelete;
      std::map<Instruction *, Value *> toSimplify;

      for (auto &I : instructions(F)) {
        if (CallInst *call = dyn_cast<CallInst>(&I)) {
          IRBuilder<> builder(call);
          
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            Value* arg1 = isConstant(inSets[&I], call->getArgOperand(1));
            Value* arg2 = isConstant(inSets[&I], call->getArgOperand(2));

            if (arg1 && arg2) {
              ConstantInt *const1 = cast<ConstantInt>(arg1);
              ConstantInt *const2 = cast<ConstantInt>(arg2);

              IntegerType *intType = IntegerType::get(currentModule->getContext(), 64);
              Value *sum = ConstantInt::get(intType, const1->getSExtValue() + const2->getSExtValue(), true);

              builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), sum});

              toDelete.push_back(&I);
              modified = true;
            } else if (arg1) {
              ConstantInt *const1 = cast<ConstantInt>(arg1);
              if (const1->getSExtValue() == 0) {
                toSimplify[&I] = call->getArgOperand(2);
              }
            } else if (arg2) {
              ConstantInt *const2 = cast<ConstantInt>(arg2);
              if (const2->getSExtValue() == 0) {
                toSimplify[&I] = call->getArgOperand(1);
              }
            }
          } else if (currentModule->getFunction("CAT_sub") == callee) {
            Value* arg1 = isConstant(inSets[&I], call->getArgOperand(1));
            Value* arg2 = isConstant(inSets[&I], call->getArgOperand(2));

            if (arg1 && arg2) {
              ConstantInt *const1 = cast<ConstantInt>(arg1);
              ConstantInt *const2 = cast<ConstantInt>(arg2);

              IntegerType *intType = IntegerType::get(currentModule->getContext(), 64);
              Value *diff = ConstantInt::get(intType, const1->getSExtValue() - const2->getSExtValue(), true);

              builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), diff});

              toDelete.push_back(&I);
              modified = true;
            } else if (arg2) {
              ConstantInt *const2 = cast<ConstantInt>(arg2);
              if (const2->getSExtValue() == 0) {
                toSimplify[&I] = call->getArgOperand(1);
              }
            }
          }
        }
      }

      for (auto I : toDelete) {
        I->eraseFromParent();
      }
      toDelete.clear();
      
      // Algebraic simplification
      for (auto [I, variable] : toSimplify) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);

          Value *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {variable});
          builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});

          toDelete.push_back(I);
          modified = true;
        }
      }

      for (auto I : toDelete) {
        I->eraseFromParent();
      }

      return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override { }
  };
}

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT());}}); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); }}); // ** for -O0
