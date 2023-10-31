#include "llvm/Pass.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
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

    // This function prints the definitions of a variable
    void printDefTable(Function &F, std::map<Instruction *, std::set<Instruction *>> defTable) {
      for (auto [def, insts] : defTable) {
        for (auto inst : insts) {
          errs() << F.getName() << *def << *inst << "\n";
        }
      }
    }

    // This function prints the reaching definitions of a function F
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

    void getPointerUsers(Value *pointer,
                         std::vector<Instruction *> &calls,
                         std::set<Value *> &seen) {
      for (auto user : pointer->users()) {
        if (!seen.contains(user)) {
          seen.insert(user);

          if (CallInst *call = dyn_cast<CallInst>(user)) {
            Function *callee = call->getCalledFunction();
            if (CATMap.contains(callee)) {
              switch (CATMap.at(callee)) {
                case CAT_add:
                case CAT_sub:
                case CAT_set:
                  if (call->getArgOperand(0) == pointer) {
                    calls.push_back(call);
                  }
                  break;
                default:
                  break;
              }
            } else {
              calls.push_back(call);
            }
          } else if (StoreInst *store = dyn_cast<StoreInst>(user)) {
            getPointerUsers(store->getPointerOperand(), calls, seen);
          } else if (isa<PHINode>(user) || isa<SelectInst>(user) || isa<LoadInst>(user)) {
            getPointerUsers(user, calls, seen);
          }
        }
        
      }
    }

    void createDefTable(std::set<Instruction *> CATInstructions, 
                        std::map<Instruction *, std::set<Instruction *>> &defTable) {
      std::vector<Instruction *> escaped;
      std::vector<Instruction *> calls;

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
                escaped.push_back(inst);
                calls.push_back(userCall);
              }
            } else if (StoreInst *store = dyn_cast<StoreInst>(user)) {
              escaped.push_back(inst);
              std::set<Value *> seen = {user};
              getPointerUsers(store->getPointerOperand(), calls, seen);
            }
          }
        }
      }

      for (auto var : escaped) {
        for (auto call : calls) {
          defTable[var].insert(call);
        }
      }
    }

    unsigned assignNumbers(Function &F, 
                           std::vector<Instruction *> &numToInst, 
                           std::map<Instruction *, unsigned> &instToNum) {
      unsigned num = 0;
      for (auto &I : instructions(F)) {
        numToInst.push_back(&I);
        instToNum[&I] = num;
        num++;
      }
      return num;
    }

    // This function creates reaching definitons for all instructions in function F
    // and stores them into the maps inSets and outSets. LLVM BitVectors are
    // used to generate the initial gen, kill, in, and out sets before being transformed
    // into sets
    void createReachingDefs(Function &F, 
                            std::map<Instruction *, std::set<Instruction *>> &inSets, 
                            std::map<Instruction *, std::set<Instruction *>> &outSets,
                            std::map<Instruction *, std::set<Instruction *>> defTable,
                            AliasAnalysis &aliasAnalysis) {
      std::vector<Instruction *> numToInst;
      std::map<Instruction *, unsigned> instToNum;
      unsigned size = assignNumbers(F, numToInst, instToNum);

      std::map<Instruction *, BitVector> gen;
      std::map<Instruction *, BitVector> kill;
      std::map<Instruction *, BitVector> in;
      std::map<Instruction *, BitVector> out;

      std::vector<std::vector<Instruction *>> toKill;
      std::set<Instruction *> escaped;

      // Generate the gen sets
      for (auto &I : instructions(F)) {
        gen[&I] = BitVector(size);
        kill[&I] = BitVector(size);      

        if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_new:
                gen[&I].set(instToNum.at(&I));
                for (auto def : defTable.at(&I)) {
                  kill[&I].set(instToNum.at(def));
                }
                kill[&I].reset(instToNum.at(&I));
                break;
              case CAT_add:
              case CAT_sub:
              case CAT_set:
                if (Instruction *arg = dyn_cast<Instruction>(call->getArgOperand(0))) {
                  if (!escaped.contains(arg)) {
                    gen[&I].set(instToNum.at(&I));
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
              if (insts.contains(&I) && !escaped.contains(def)) {
                escaped.insert(def);
                gen[&I].set(instToNum.at(&I));
                std::vector<Instruction *> pair = {&I, def};
                toKill.push_back(pair);
              }
            }
          }
        } else if (StoreInst *store = dyn_cast<StoreInst>(&I)) {
          if (Instruction *val = dyn_cast<Instruction>(store->getValueOperand())) {
            std::vector<Instruction *> pair = {&I, val};
            toKill.push_back(pair);
          }
        }

        in[&I] = BitVector(size);
        out[&I] = BitVector(size);
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
      std::vector<Value *> stack = {v};
      std::set<Value *> visited;

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
                            std::map<Instruction *, std::set<Instruction *>> defTable) {
      // If the value is an argument, it is not safe to assume it is a constant
      if (isa<Argument>(valToCheck)) {
        return nullptr;
      }

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

          if (ConstantInt *constInt = isConstant(inSet, phiVal, defTable)) {
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
          } else {
            if (Instruction *valInst = dyn_cast<Instruction>(valToCheck)) {
              if (defTable.contains(valInst) && defTable.at(valInst).contains(inst)) {
                return nullptr;
              }
            }
          }
        }
      }
      
      // Operations performed on the PHI take precedence over incoming values
      return constPtr ? constPtr : phiConst;
    }

    // This function runs constant propagation on a set of CAT instruction
    bool runConstantPropagation(std::map<Instruction *, std::set<Instruction *>> inSets,
                                std::map<Instruction *,std::set<Instruction *>> outSets,
                                std::set<Instruction *> &CATInstructions,
                                std::map<Instruction *, std::set<Instruction *>> defTable) {
      bool modified = false;
      std::map<Instruction *, ConstantInt *> toReplace;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_get") == callee) {
            if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(0), defTable)) {
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
                            std::set<Instruction *> &CATInstructions,
                            std::map<Instruction *, std::set<Instruction *>> defTable) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);
          
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            ConstantInt *const1 = isConstant(inSets[I], call->getArgOperand(1), defTable);
            ConstantInt *const2 = isConstant(inSets[I], call->getArgOperand(2), defTable);

            if (const1 && const2) {
              IntegerType *intType = IntegerType::get(currentModule->getContext(), 64);
              Value *sum = ConstantInt::get(intType, const1->getSExtValue() + const2->getSExtValue(), true);

              Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), sum});
              CATInstructions.insert(newInst);

              toDelete.push_back(I);
              modified = true;
            }
          } else if (currentModule->getFunction("CAT_sub") == callee) {
            ConstantInt *const1 = isConstant(inSets[I], call->getArgOperand(1), defTable);
            ConstantInt *const2 = isConstant(inSets[I], call->getArgOperand(2), defTable);

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
                                    std::set<Instruction *> &CATInstructions,
                                    std::map<Instruction *, std::set<Instruction *>> defTable) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);

          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(1), defTable)) {
              // If the 2nd argument is a constant = 0, then simplify to 3rd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(2)});
                Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);

                toDelete.push_back(I);
                modified = true;
              }
            } else if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(2), defTable)) {
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
            if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(2), defTable)) {
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

    void regenerateDataStructs(Function &F,
                               std::map<Instruction *, std::set<Instruction *>> &inSets,
                               std::map<Instruction *, std::set<Instruction *>> &outSets,
                               std::set<Instruction *> CATInstructions,
                               std::map<Instruction *, std::set<Instruction *>> &defTable,
                               AliasAnalysis &aliasAnalysis) {
      inSets.clear();
      outSets.clear();
      defTable.clear();
      createDefTable(CATInstructions, defTable);
      createReachingDefs(F, inSets, outSets, defTable, aliasAnalysis);
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      bool modified = false;
      std::map<Instruction *, std::set<Instruction *>> inSets;
      std::map<Instruction *, std::set<Instruction *>> outSets;
      std::set<Instruction *> CATInstructions;
      std::map<Instruction *, std::set<Instruction *>> defTable;
      AliasAnalysis &aliasAnalysis = getAnalysis<AAResultsWrapperPass>().getAAResults();
      getCatInstructions(F, CATInstructions);
      regenerateDataStructs(F, inSets, outSets, CATInstructions, defTable, aliasAnalysis);

      // printDefTable(F, defTable);
      printReachingDefs(F, inSets, outSets);

      // Constant propagation
      modified |= runConstantPropagation(inSets, outSets, CATInstructions, defTable);

      // Constant folding
      if (modified) {
        regenerateDataStructs(F, inSets, outSets, CATInstructions, defTable, aliasAnalysis);
      }
      modified |= runConstantFolding(inSets, outSets, CATInstructions, defTable);

      // Algebraic Simplification
      if (modified) {
        regenerateDataStructs(F, inSets, outSets, CATInstructions, defTable, aliasAnalysis);
      }
      modified |= runAlgebraicSimplification(inSets, outSets, CATInstructions, defTable);

      return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<AAResultsWrapperPass>();
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
