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
#include <map>
#include <set>
#include <vector>
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

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
      std::vector<Instruction *> numToInst;
      std::map<Instruction *, unsigned> instToNum;
      std::map<Instruction *, BitVector> gen;
      std::map<Instruction *, BitVector> kill;
      std::vector<Instruction *> toKill;
      std::map<Instruction *, BitVector> in;
      std::map<Instruction *, BitVector> out;

      for (auto &F : M) {
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
            if (M.getFunction("CAT_new") == callee) {
              genSet.set(num);
            } else if (M.getFunction("CAT_add") == callee || M.getFunction("CAT_sub") == callee || M.getFunction("CAT_set") == callee) {
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
        toKill.clear();

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
        gen.clear();
        kill.clear();

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
        numToInst.clear();
        instToNum.clear();
        in.clear();
        out.clear();
      }
      return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      bool modified = false;

      // Constant propagation
      for (auto &B : F) {
        std::map<Instruction *, Value *> toReplace;

        for (auto &I : B) {
          if (CallInst *call = dyn_cast<CallInst>(&I)) {
            Function *callee = call->getCalledFunction();
            Module *M = F.getParent();
            
            if (M->getFunction("CAT_get") == callee) {
              std::set<Instruction *> inSet = inSets[&F][&I];
              int64_t constant;
              Value *v;
              bool constantInitalized = false;
              bool runPropagation = false;
              Instruction *callArg = cast<Instruction>(call->getArgOperand(0));

              for (auto inst : inSet) {
                Function *instCallee = cast<CallInst>(inst)->getCalledFunction();

                if (M->getFunction("CAT_new") == instCallee && inst == callArg) {
                  v = inst->getOperand(0);
                  
                  if (ConstantInt *c = dyn_cast<ConstantInt>(v)) {
                    if (!constantInitalized) {
                      constant = c->getSExtValue();
                      constantInitalized = true;
                      runPropagation = true;
                    }
                    runPropagation = runPropagation && constant == c->getSExtValue();
                  }
                } else if (M->getFunction("CAT_set") == instCallee && inst->getOperand(0) == callArg) {
                  v = inst->getOperand(1);
                  
                  if (ConstantInt *c = dyn_cast<ConstantInt>(v)) {
                    if (!constantInitalized) {
                      constant = c->getSExtValue();
                      constantInitalized = true;
                      runPropagation = true;
                    }
                    runPropagation = runPropagation && constant == c->getSExtValue();
                  }                  
                }
              }

              if (runPropagation) {
                toReplace[&I] = v;
                modified = true;
              }
            }
          }
        }

        for (auto &[I, constValue] : toReplace) {
          BasicBlock::iterator ii(I);
          ReplaceInstWithValue(B.getInstList(), ii, constValue);
        }
      }

      // Constant folding
      for (auto &B : F) {
        for (auto &I : B) {
          if (CallInst *call = dyn_cast<CallInst>(&I)) {
            IRBuilder<> builder(call);
          }
        }
      }
      return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      // errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
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
