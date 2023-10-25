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

    // This function prints the reaching definitions for a function F in the style
    // of H1
    void printReachingDefs(Function &F,
                           std::map<Instruction *, std::set<Instruction *>> inSets, 
                           std::map<Instruction *, std::set<Instruction *>> outSets) {
      errs() << "Function \"" << F.getName() << "\"\n";
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

    // This function finds all CAT instructions in a function F and stores them into
    // the set CATInstructions
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

    void createDefTable(std::set<Instruction *> CATInstructions, 
                        std::map<Instruction *, std::set<Instruction *>> &defTable) {
      for (auto inst : CATInstructions) {
        CallInst *call = cast<CallInst>(inst);
        if (currentModule->getFunction("CAT_new") == call->getCalledFunction()) {
          defTable[inst] = std::set<Instruction *>();
          defTable[inst].insert(inst);

          for (auto user : inst->users()) {
            if (CallInst *userCall = dyn_cast<CallInst>(user)) {
              Function *userCallee = userCall->getCalledFunction();
              if (CATMap.contains(userCallee)) {
                switch (CATMap.at(userCallee)) {
                  case CAT_add:
                  case CAT_sub:
                  case CAT_set:
                    if (userCall->getArgOperand(0) == inst) {
                      defTable[inst].insert(userCall);
                    }
                    break;
                  default:
                    break;
                }
              } else {
                defTable[inst].insert(userCall);
              }
            } else if (StoreInst *userStore = dyn_cast<StoreInst>(user)) {
              defTable[inst].insert(userStore);
            }
          }
        }
      }
      return;
    }

    // This function creates reaching definitons for all instructions in function F
    // and stores them into the maps inSets and outSets. LLVM BitVectors are
    // used to generate the initial gen, kill, in, and out sets before being transformed
    // into sets
    void createReachingDefs(Function &F, 
                            std::map<Instruction *, std::set<Instruction *>> &inSets, 
                            std::map<Instruction *, std::set<Instruction *>> &outSets,
                            std::set<Instruction *> CATInstructions) {
      std::vector<Instruction *> numToInst;
      std::map<Instruction *, unsigned> instToNum;
      std::map<Instruction *, BitVector> gen;
      std::map<Instruction *, BitVector> kill;
      std::vector<std::vector<Instruction *>> toKill;
      std::map<Instruction *, BitVector> in;
      std::map<Instruction *, BitVector> out;
      std::vector<Instruction *> buffer;
      std::map<Instruction *, std::set<Instruction *>> defTable;
      std::set<Instruction *> escaped;

      createDefTable(CATInstructions, defTable);
      // for (auto [D, S] : defTable) {
      //   errs() << "=====" << *D << "\n";
      //   for (auto N : S) {
      //     errs() << *N << "\n";
      //   }
      // }

      // Initialize the unsigned size to be the total number of instructions in F
      // The unsigned num represents the number (temporarily) assigned to an
      // instruction for reference
      unsigned num = 0;
      unsigned size = 0;
      for (auto &B : F) {
        size += B.size();
      }

      // Generate the gen sets
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
                // genSet.set(num);
                if (Instruction *arg = dyn_cast<Instruction>(call->getArgOperand(0))) {
                  if (!escaped.contains(arg)) {
                    genSet.set(num);
                    std::vector<Instruction *> pair = {&I, arg};
                    toKill.push_back(pair);
                  }
                }
                break;
              default:
                break;
            }
          } else {
            for (auto [def, insts] : defTable) {
              if (insts.contains(&I)) {
                escaped.insert(def);
                std::vector<Instruction *> pair = {&I, def};
                toKill.push_back(pair);
              }
            }
          }
        } else if (StoreInst *store = dyn_cast<StoreInst>(&I)) {
          if (CallInst *val = dyn_cast<CallInst>(store->getValueOperand())) {
            std::vector<Instruction *> pair = {&I, val};
            toKill.push_back(pair);
          }
        } else if (isa<LoadInst>(&I)) {
          for (auto buff : buffer) {
            std::vector<Instruction *> pair = {&I, buff};
            toKill.push_back(pair);
          }
          buffer.clear();
        }

        gen[&I] = genSet;
        kill[&I] = killSet;
        num++;
      }

      // Generate the kill sets
      for (auto inst : toKill) {
        kill[inst[0]].set(instToNum[inst[1]]);
        kill[inst[0]] |= kill[inst[1]];
        for (auto bit : kill[inst[0]].set_bits()) {
          kill[numToInst[bit]].set(instToNum[inst[0]]);
        }
      }

      // Compute the in and out sets with a work list
      BitVector workList = BitVector(size, true);

      while (workList.any()) {
        int first = workList.find_first();
        workList.reset(first);

        Instruction *inst = numToInst[first];
        Instruction *prev = inst->getPrevNode();
        
        if (!prev) {
          for (auto pred : predecessors(inst->getParent())) {
            in[inst] |= out[pred->getTerminator()];
          }
        } else {
          in[inst] |= out[prev];
        }

        BitVector newOut = BitVector(size);
        newOut |= in[inst];
        newOut.reset(kill[inst]);
        newOut |= gen[inst];

        if (newOut != out[inst]) {
          Instruction *next = inst->getNextNode();
          if (!next) {
            for (auto succ : successors(inst->getParent())) {
              workList.set(instToNum[&(succ->front())]);
            }
          } else {
            workList.set(instToNum[next]);
          }
        }

        out[inst] = newOut;
      }

      // Convert BitVectors to sets and insert them into inSets and outSets
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

    // This function runs DFS to check if there is a cycle when 
    // traversing the incoming values in a PHI node
    bool containsCycle(Value *v) {
      std::vector<Value *> stack;
      std::set<Value *> visited;
      stack.push_back(v);

      while (!stack.empty()) {
        Value *val = stack.back();
        stack.pop_back();
        
        if (visited.contains(val)) {
          return true;
        }
        visited.insert(val);

        if (PHINode *phi = dyn_cast<PHINode>(val)) {
          for (unsigned i = 0; i < phi->getNumIncomingValues(); i++) {
            stack.push_back(phi->getIncomingValue(i));
          }
        } else if (SelectInst *select = dyn_cast<SelectInst>(val)) {
          stack.push_back(select->getTrueValue());
          stack.push_back(select->getFalseValue());
        }
      }

      return false;
    }

    // This function checks if a value valToCheck is a constant
    // It returns a pointer to the ConstantInt if it is a constant
    // Otherwise, it returns a nullptr
    ConstantInt *isConstant(std::set<Instruction *> inSet, 
                            Value *valToCheck, 
                            Instruction *I) {
      // If the value is an argument, it is not safe to assume it is a constant
      if (isa<Argument>(valToCheck)) {
        return nullptr;
      }

      /* // Look through the def-use chain of valToCheck
      for (auto user : valToCheck->users()) {
        if (Instruction *inst = dyn_cast<Instruction>(user)) {
          if (CallInst *call = dyn_cast<CallInst>(inst)) {
            Function *callee = call->getCalledFunction();
            // If user is not a CAT function, then valToCheck might escape
            if (!CATMap.contains(callee)) {
              return nullptr;
            }
          }
        }
      } */

      ConstantInt *constPtr = nullptr;
      int64_t constant;
      bool initialized = false;
      ConstantInt *phiConst = nullptr;

      // If valToCheck is a PHI node, check if all incoming values 
      // are constants and if they are the same constant
      // If not, then valToCheck is not a constant
      if (PHINode *phi = dyn_cast<PHINode>(valToCheck)) {
        if (containsCycle(valToCheck)) {
          return nullptr;
        }

        for (unsigned i = 0; i < phi->getNumIncomingValues(); i++) {
          Value *phiVal = phi->getIncomingValue(i);
          
          if (isa<UndefValue>(phiVal)) {
            continue;
          }

          if (ConstantInt *constInt = isConstant(inSet, phiVal, I)) {
            if (!initialized) {
              phiConst = constInt;
              constant = constInt->getSExtValue();
              initialized = true;
            } else if (constant != constInt->getSExtValue()) {
              return nullptr;
            }
          } else {
            phiConst = nullptr;
            initialized = false;
            break;
          }
        }
      }
      
      // Go back and check if PHI has been set to anything
      initialized = false;

      // Check if all users of valToCheck that are also in instruction I's inSet
      // are constants
      for (auto inst : inSet) {
        if (CallInst *call = dyn_cast<CallInst>(inst)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_new:
                if (valToCheck == inst) {
                  if (ConstantInt *constInt = dyn_cast<ConstantInt>(call->getArgOperand(0))) {
                    if (!initialized) {
                      constPtr = constInt;
                      constant = constInt->getSExtValue();
                      initialized = true;
                    } else if (constant != constInt->getSExtValue()) {
                      return nullptr;
                    }
                  }
                }
                break;
              case CAT_add:
              case CAT_sub:
                if (valToCheck == call->getArgOperand(0)) {
                  return nullptr;
                }
                break;
              case CAT_set:
                if (valToCheck == call->getArgOperand(0)) {
                  if (ConstantInt *constInt = dyn_cast<ConstantInt>(call->getArgOperand(1))) {
                    if (!initialized) {
                      constPtr = constInt;
                      constant = constInt->getSExtValue();
                      initialized = true;
                    } else if (constant != constInt->getSExtValue()) {
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
      
      // Operations performed on the PHI take precedence over PHI values
      return constPtr ? constPtr : phiConst;
    }

    // This function runs constant propagation on a set of CAT instruction
    bool runConstantPropagation(std::map<Instruction *, std::set<Instruction *>> inSets,
                                std::map<Instruction *,std::set<Instruction *>> outSets,
                                std::set<Instruction *> &CATInstructions) {
      bool modified = false;
      std::map<Instruction *, ConstantInt *> toReplace;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_get") == callee) {
            if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(0), I)) {
              toReplace[I] = c;
              modified = true;
            }
          }
        }
      }

      for (auto [I, constValue] : toReplace) {
        BasicBlock::iterator ii(I);
        ReplaceInstWithValue(I->getParent()->getInstList(), ii, constValue);
        CATInstructions.erase(I);
      }

      return modified;
    }

    // This function runs constant folding on a set of CAT instructions
    bool runConstantFolding(std::map<Instruction *, std::set<Instruction *>> inSets,
                            std::map<Instruction *,std::set<Instruction *>> outSets,
                            std::set<Instruction *> &CATInstructions) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);
          
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            ConstantInt *const1 = isConstant(inSets[I], call->getArgOperand(1), I);
            ConstantInt *const2 = isConstant(inSets[I], call->getArgOperand(2), I);

            if (const1 && const2) {
              IntegerType *intType = IntegerType::get(currentModule->getContext(), 64);
              Value *sum = ConstantInt::get(intType, const1->getSExtValue() + const2->getSExtValue(), true);

              Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), sum});
              CATInstructions.insert(newInst);

              toDelete.push_back(I);
              modified = true;
            }
          } else if (currentModule->getFunction("CAT_sub") == callee) {
            ConstantInt *const1 = isConstant(inSets[I], call->getArgOperand(1), I);
            ConstantInt *const2 = isConstant(inSets[I], call->getArgOperand(2), I);

            if (const1 && const2) {
              IntegerType *intType = IntegerType::get(currentModule->getContext(), 64);
              Value *diff = ConstantInt::get(intType, const1->getSExtValue() - const2->getSExtValue(), true);

              Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), diff});
              CATInstructions.insert(newInst);

              toDelete.push_back(I);
              modified = true;
            }
          }
        }
      }

      for (auto I : toDelete) {
        I->eraseFromParent();
        CATInstructions.erase(I);
      }

      return modified;
    }

    // This function runs algebraic simplification on a set of CAT instructions
    bool runAlgebraicSimplification(std::map<Instruction *, std::set<Instruction *>> inSets,
                                    std::map<Instruction *,std::set<Instruction *>> outSets,
                                    std::set<Instruction *> &CATInstructions) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);

          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(1), I)) {
              // If the 2nd argument is a constant = 0, then simplify to 3rd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(2)});
                Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);

                toDelete.push_back(I);
                modified = true;
              }
            } else if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(2), I)) {
              // If the 3rd argument is a constant = 0, then simplify to 2nd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(1)});
                Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);

                toDelete.push_back(I);
                modified = true;
              }
            }
          } else if (currentModule->getFunction("CAT_sub") == callee) {
            if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(2), I)) {
              // If the 3rd argument is a constant = 0, then simplify to 2nd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(1)});
                Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);
                
                toDelete.push_back(I);
                modified = true;
              }
            } /*else if (call->getArgOperand(1) == call->getArgOperand(2)) {
              // If 2nd and 3rd arguments are the same variable, then simplify result to 0
              Value *zeroConst = ConstantInt::get(IntegerType::get(currentModule->getContext(), 64), 0, true);
              Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), zeroConst});
              CATInstructions.insert(newInst);

              toDelete.push_back(I);
              modified = true;
            }*/
          }
        }
      }

      for (auto I : toDelete) {
        I->eraseFromParent();
        CATInstructions.erase(I);
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
      getCatInstructions(F, CATInstructions);
      createReachingDefs(F, inSets, outSets, CATInstructions);

      printReachingDefs(F, inSets, outSets);

      // Constant propagation
      modified |= runConstantPropagation(inSets, outSets, CATInstructions);

      // Constant folding
      if (modified) {
        inSets.clear();
        outSets.clear();
        createReachingDefs(F, inSets, outSets, CATInstructions);
      }
      modified |= runConstantFolding(inSets, outSets, CATInstructions);

      // Algebraic Simplification
      if (modified) {
        inSets.clear();
        outSets.clear();
        createReachingDefs(F, inSets, outSets, CATInstructions);
      }
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
