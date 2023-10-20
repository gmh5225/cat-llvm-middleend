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
#include <deque>
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

    void getCatInstructions(Function &F, std::set<Instruction *> &CATInstructions) {
      for (auto &I : instructions(F)) {
        if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            CATInstructions.insert(&I);
          }
        }
      }
    }

    void printReachingDefs(Function &F,
                           std::map<Instruction *, std::set<Instruction *>> inSets, 
                           std::map<Instruction *, std::set<Instruction *>> outSets) {
      errs() << "FUNCTION \"" << F.getName() << "\"\n";
      for (auto &I : instructions(F)) {
        errs() << "INSTRUCTION:" << I << "\nIN\n{\n";
        for (auto in : inSets[&I]) {
          errs() << *in << "\n";
        }
        errs() << "}\nOUT\n{\n";
        for (auto out : outSets[&I]) {
          errs() << *out << "\n";
        }
        errs() << "}\n";
      }
    }

    void createReachingDefs(Function &F, 
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
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
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
          
        }

        gen[&I] = genSet;
        kill[&I] = killSet;
        num++;
      }

      for (auto inst : toKill) {
        CallInst *call = cast<CallInst>(inst);
        if (isa<Argument>(call->getArgOperand(0))) {
          continue;
        }
        Instruction *arg = cast<Instruction>(call->getArgOperand(0));

        kill[inst].set(instToNum[arg]);
        kill[inst] |= kill[arg];
        for (auto bit : kill[inst].set_bits()) {
          kill[numToInst[bit]].set(instToNum[inst]);
        }
      }

      BitVector workList = BitVector(size);
      workList.set();

      while (!workList.none()) {
        int first = workList.find_first();
        workList.reset(first);
        Instruction *inst = numToInst[first];
        BitVector oldOut = out[inst];
        Instruction *prev = inst->getPrevNode();
        
        if (!prev) {
          for (auto pred : predecessors(inst->getParent())) {
            in[inst] |= out[pred->getTerminator()];
          }
        } else {
          in[inst] |= out[prev];
        }

        out[inst] |= in[inst];
        out[inst].reset(kill[inst]);
        out[inst] |= gen[inst];

        if (oldOut != out[inst]) {
          Instruction *next = inst->getNextNode();
          if (!next) {
            for (auto succ : successors(inst->getParent())) {
              workList.set(instToNum[&(succ->front())]);
            }
          } else {
            workList.set(instToNum[next]);
          }
        }
      }

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

    bool phiContainsCycle(Value *v, std::set<Value *> &seen) {
      if (seen.contains(v)) {
        return true;
      }
      if (!isa<PHINode>(v)) {
        return false;
      }

      bool loop = false;
      seen.insert(v);
      PHINode *phi = cast<PHINode>(v);
      for (unsigned i = 0; i < phi->getNumIncomingValues(); i++) {
        loop |= phiContainsCycle(phi->getIncomingValue(i), seen);
      }
      seen.erase(v);
      return loop;
    }

    Value *isConstant(std::set<Instruction *> inSet, Value *v) {
      if (isa<Argument>(v)) {
        return nullptr;
      }

      for (auto user : v->users()) {
        if (CallInst *call = dyn_cast<CallInst>(user)) {
          Function *callee = call->getCalledFunction();
          if (!CATMap.contains(callee)) {
            return nullptr;
          }
        }
      }

      Value *valPtr = nullptr;
      int64_t c;
      bool initialized = false;
      std::set<Value *> seen;

      if (PHINode *p = dyn_cast<PHINode>(v)) {
        for (unsigned j = 0; j < p->getNumIncomingValues(); j++) {
          Value *phiVal = p->getIncomingValue(j);
          if (isa<UndefValue>(phiVal)) {
            continue;
          }
          if (phiContainsCycle(v, seen)) {
            return nullptr;
          }
          if (Value *constantVal = isConstant(inSet, phiVal)) {
            if (ConstantInt *constant = dyn_cast<ConstantInt>(constantVal)) {
              if (!initialized) {
                valPtr = constantVal;
                c = constant->getSExtValue();
                initialized = true;
              } else if (c != constant->getSExtValue()) {
                return nullptr;
              }
            }
          }
        }
      }

      for (auto inst : inSet) {
        if (CallInst *call = dyn_cast<CallInst>(inst)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_new:
                if (v == inst) {
                  if (ConstantInt *constant = dyn_cast<ConstantInt>(call->getArgOperand(0))) {
                    if (!initialized) {
                      valPtr = call->getArgOperand(0);
                      c = constant->getSExtValue();
                      initialized = true;
                    } else if (c != constant->getSExtValue()) {
                      return nullptr;
                    }
                  }
                }
                break;
              case CAT_add:
              case CAT_sub:
                if (v == call->getArgOperand(0)) {
                  return nullptr;
                }
                break;
              case CAT_set:
                if (v == call->getArgOperand(0)) {
                  if (ConstantInt *constant = dyn_cast<ConstantInt>(call->getArgOperand(1))) {
                    if (!initialized) {
                      valPtr = call->getArgOperand(1);
                      c = constant->getSExtValue();
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
      }
      
      return valPtr;
    }

    bool runConstantPropagation(std::map<Instruction *, std::set<Instruction *>> inSets,
                                std::map<Instruction *,std::set<Instruction *>> outSets,
                                std::set<Instruction *> CATInstructions) {
      bool modified = false;
      std::map<Instruction *, Value *> toReplace;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_get") == callee) {
            if (Value *c = isConstant(inSets[I], call->getArgOperand(0))) {
              toReplace[I] = c;
              modified = true;
            }
          }
        }
      }

      for (auto [I, constValue] : toReplace) {
        BasicBlock::iterator ii(I);
        ReplaceInstWithValue(I->getParent()->getInstList(), ii, constValue);
      }

      return modified;
    }

    bool runConstantFolding(std::map<Instruction *, std::set<Instruction *>> inSets,
                            std::map<Instruction *,std::set<Instruction *>> outSets,
                            std::set<Instruction *> CATInstructions) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);
          
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            Value* arg1 = isConstant(inSets[I], call->getArgOperand(1));
            Value* arg2 = isConstant(inSets[I], call->getArgOperand(2));

            if (arg1 && arg2) {
              ConstantInt *const1 = cast<ConstantInt>(arg1);
              ConstantInt *const2 = cast<ConstantInt>(arg2);

              IntegerType *intType = IntegerType::get(currentModule->getContext(), 64);
              Value *sum = ConstantInt::get(intType, const1->getSExtValue() + const2->getSExtValue(), true);

              builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), sum});

              toDelete.push_back(I);
              modified = true;
            }
          } else if (currentModule->getFunction("CAT_sub") == callee) {
            Value* arg1 = isConstant(inSets[I], call->getArgOperand(1));
            Value* arg2 = isConstant(inSets[I], call->getArgOperand(2));

            if (arg1 && arg2) {
              ConstantInt *const1 = cast<ConstantInt>(arg1);
              ConstantInt *const2 = cast<ConstantInt>(arg2);

              IntegerType *intType = IntegerType::get(currentModule->getContext(), 64);
              Value *diff = ConstantInt::get(intType, const1->getSExtValue() - const2->getSExtValue(), true);

              builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), diff});

              toDelete.push_back(I);
              modified = true;
            }
          }
        }
      }

      for (auto I : toDelete) {
        I->eraseFromParent();
      }

      return modified;
    }

    bool runAlgebraicSimplification(std::map<Instruction *, std::set<Instruction *>> inSets,
                                    std::map<Instruction *,std::set<Instruction *>> outSets,
                                    std::set<Instruction *> CATInstructions) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);

          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            if (Value *arg = isConstant(inSets[I], call->getArgOperand(1))) {
              ConstantInt *c = cast<ConstantInt>(arg);
              
              if (c->getSExtValue() == 0) {
                Value *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(2)});
                builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});

                toDelete.push_back(I);
                modified = true;
              }
            } else if (Value *arg = isConstant(inSets[I], call->getArgOperand(2))) {
              ConstantInt *c = cast<ConstantInt>(arg);

              if (c->getSExtValue() == 0) {
                Value *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(1)});
                builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});

                toDelete.push_back(I);
                modified = true;
              }
            }
          } else if (currentModule->getFunction("CAT_sub") == callee) {
            if (Value *arg = isConstant(inSets[I], call->getArgOperand(2))) {
              ConstantInt *c = cast<ConstantInt>(arg);

              if (c->getSExtValue() == 0) {
                Value *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(1)});
                builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});
                
                toDelete.push_back(I);
                modified = true;
              }
            } else if (call->getArgOperand(1) == call->getArgOperand(2)) {
              Value *zeroConst = ConstantInt::get(IntegerType::get(currentModule->getContext(), 64), 0, true);
              builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), zeroConst});

              toDelete.push_back(I);
              modified = true;
            }
          }
        }
      }

      for (auto I : toDelete) {
        I->eraseFromParent();
      }

      return modified;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      bool modified = false;
      std::map<Instruction *, std::set<Instruction *>> inSets;
      std::map<Instruction *, std::set<Instruction *>> outSets;
      std::set<Instruction *> CATInstructions;
      createReachingDefs(F, inSets, outSets);
      getCatInstructions(F, CATInstructions);

      // Constant propagation
      modified |= runConstantPropagation(inSets, outSets, CATInstructions);

      // Constant folding
      modified |= runConstantFolding(inSets, outSets, CATInstructions);

      // Algebraic Simplification
      modified |= runAlgebraicSimplification(inSets, outSets, CATInstructions);

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
