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

using namespace llvm;

namespace {
  struct CAT : public FunctionPass {
    static char ID; 

    CAT() : FunctionPass(ID) {}

    std::map<Function *, std::map<Instruction *, std::set<Instruction *>>> inSets;
    std::map<Function *, std::map<Instruction *, std::set<Instruction *>>> outSets;

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      return false;
    }

    void createReachingDefs(Function &F) {
      std::vector<Instruction *> numToInst;
      std::map<Instruction *, unsigned> instToNum;
      std::map<Instruction *, BitVector> gen;
      std::map<Instruction *, BitVector> kill;
      std::vector<Instruction *> toKill;
      std::map<Instruction *, BitVector> in;
      std::map<Instruction *, BitVector> out;

      Module *M = F.getParent();
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
          if (M->getFunction("CAT_new") == callee) {
            genSet.set(num);
          } else if (M->getFunction("CAT_add") == callee || 
                     M->getFunction("CAT_sub") == callee || 
                     M->getFunction("CAT_set") == callee) {
            genSet.set(num);
            toKill.push_back(&I);
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

          inSets[&F][&I] = inSet;
          outSets[&F][&I] = outSet;
      }
      return;
    }

    Value *isConstant(Function &F, Instruction &I, Value *v) {
      Instruction *valInst = cast<Instruction>(v);
      std::set<Instruction *> inSet = inSets[&F][&I];
      Value *valPtr = nullptr;
      bool initialized = false;
      int64_t c;

      for (auto inst : inSet) {
        if (CallInst *call = dyn_cast<CallInst>(inst)) {
          Module *M = F.getParent();
          Function *callee = call->getCalledFunction();

          if ((M->getFunction("CAT_new") == callee) && (valInst == inst)) {
            if (ConstantInt *constant = dyn_cast<ConstantInt>(call->getArgOperand(0))) {
              if (!initialized) {
                c = constant->getSExtValue();
                valPtr = call->getArgOperand(0);
                initialized = true;
              } else if (c != constant->getSExtValue()) {
                return nullptr;
              }
            }
          } else if ((M->getFunction("CAT_set") == callee) && (valInst == call->getArgOperand(0))) {
            if (ConstantInt *constant = dyn_cast<ConstantInt>(call->getArgOperand(1))) {
              if (!initialized) {
                c = constant->getSExtValue();
                valPtr = call->getArgOperand(1);
                initialized = true;
              } else if (c != constant->getSExtValue()) {
                return nullptr;
              }
            }
          } else if (((M->getFunction("CAT_add") == callee) || (M->getFunction("CAT_sub") == callee)) &&
                     (valInst == call->getArgOperand(0))) {
            return nullptr;
          }
        }
      }
      
      return valPtr;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      bool modified = false;
      createReachingDefs(F);

      // Constant propagation
      for (auto &B : F) {
        std::map<Instruction *, Value *> toReplace;

        for (auto &I : B) {
          if (CallInst *call = dyn_cast<CallInst>(&I)) {
            Function *callee = call->getCalledFunction();
            Module *M = F.getParent();

            if (M->getFunction("CAT_get") == callee) {
              if (Value* c = isConstant(F, I, call->getArgOperand(0))) {
                toReplace[&I] = c;
                modified = true;
              }
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
      std::vector<Instruction *> toSimplify;

      for (auto &B : F) {
        for (auto &I : B) {
          if (CallInst *call = dyn_cast<CallInst>(&I)) {
            IRBuilder<> builder(call);
            
            Function *callee = call->getCalledFunction();
            Module *M = F.getParent();

            if (M->getFunction("CAT_add") == callee) {
              Value* arg1 = isConstant(F, I, call->getArgOperand(1));
              Value* arg2 = isConstant(F, I, call->getArgOperand(2));

              if (arg1 && arg2) {
                ConstantInt *const1 = cast<ConstantInt>(arg1);
                ConstantInt *const2 = cast<ConstantInt>(arg2);

                IntegerType *intType = IntegerType::get(M->getContext(), 64);
                Value *sum = ConstantInt::get(intType, const1->getSExtValue() + const2->getSExtValue(), true);

                builder.CreateCall(M->getFunction("CAT_set"), {call->getArgOperand(0), sum});
                toDelete.push_back(&I);
                modified = true;
              }
            } else if (M->getFunction("CAT_sub") == callee) {
              Value* arg1 = isConstant(F, I, call->getArgOperand(1));
              Value* arg2 = isConstant(F, I, call->getArgOperand(2));

              if (arg1 && arg2) {
                ConstantInt *const1 = cast<ConstantInt>(arg1);
                ConstantInt *const2 = cast<ConstantInt>(arg2);

                IntegerType *intType = IntegerType::get(M->getContext(), 64);
                Value *diff = ConstantInt::get(intType, const1->getSExtValue() - const2->getSExtValue(), true);

                builder.CreateCall(M->getFunction("CAT_set"), {call->getArgOperand(0), diff});
                toDelete.push_back(&I);
                modified = true;
              }
            }
          }
        }
      }

      for (auto inst : toDelete) {
        inst->eraseFromParent();
      }

      // Algebraic simplification
      return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
    }
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
