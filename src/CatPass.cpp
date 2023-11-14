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
#include "llvm/Transforms/Utils/Cloning.h"
#include <map>
#include <set>
#include <vector>

using namespace llvm;

namespace {
  enum CAT_API {CAT_new, CAT_add, CAT_sub, CAT_get, CAT_set, CAT_destroy};

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

    // This function finds all CAT instructions in a function F and stores them into
    // the set CATInstructions
    void getCATInstructions(Function &F, std::set<Instruction *> &CATInstructions) {
      for (auto &I : instructions(F)) {
        if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            CATInstructions.insert(&I);
          }
        }
      }
    }
    
    // This function creates a definition table of CAT variables
    void createDefTable(Function &F,
                        std::map<Value *, std::set<Instruction *>> &defTable) {
      for (auto &I : instructions(F)) {
        if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_new:
                defTable[&I].insert(&I);
                break;
              case CAT_add:
              case CAT_sub:
              case CAT_set:
                defTable[call->getArgOperand(0)].insert(&I);
                break;
              default:
                break;
            }
          }
        }
      }
    }

    // This function assigns numbers to each instruction in function F
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

    // This function looks for every function call that any variable might escape to
    void findEscapingCalls(Value *pointer,
                           std::set<Instruction *> &calls,
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
                    calls.insert(call);
                  }
                  break;
                default:
                  break;
              }
            } else {
              calls.insert(call);
            }
          } else if (StoreInst *store = dyn_cast<StoreInst>(user)) {
            findEscapingCalls(store->getPointerOperand(), calls, seen);
          } else if (isa<PHINode>(user) || isa<SelectInst>(user) || isa<LoadInst>(user)) {
            findEscapingCalls(user, calls, seen);
          }
        }
      }
    }

    // This function finds every variable that escapes
    void getEscapedInsts(std::map<Value *, std::set<Instruction *>> defTable,
                         std::set<Value *> &escaped,
                         std::set<Instruction *> &calls) {
      for (auto def : defTable) {
        for (auto user : def.first->users()) {
          std::set<Value *> seen = {user};

          if (CallInst *call = dyn_cast<CallInst>(user)) {
            if (!CATMap.contains(call->getCalledFunction())) {
              escaped.insert(def.first);
              calls.insert(call);
              findEscapingCalls(call, calls, seen);
            }
          } else if (StoreInst *store = dyn_cast<StoreInst>(user)) {
            if (store->getValueOperand() == def.first) {
              escaped.insert(def.first);
              findEscapingCalls(store->getPointerOperand(), calls, seen);
            }
          }
        }
      }
    }

    // Helper function for killing instructions
    void killHelper(Instruction *killer,
                    Value *killed,
                    std::map<Instruction *, std::set<Instruction *>> &kill,
                    std::map<Value *, std::set<Instruction *>> defTable) {
      kill[killer].insert(defTable.at(killed).begin(), defTable.at(killed).end());
      kill[killer].erase(killer);
    }

    // Helper function for computing gen and kill sets
    void computeGenKill(Function &F,
                        AliasAnalysis &aliasAnalysis,
                        std::map<Instruction *, std::set<Instruction *>> &gen,
                        std::map<Instruction *, std::set<Instruction *>> &kill,
                        std::map<Value *, std::set<Instruction *>> defTable) {
      std::set<Value *> escaped;
      std::set<Instruction *> calls;
      getEscapedInsts(defTable, escaped, calls);

      for (auto &I : instructions(F)) {
        if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_new:
                gen[&I].insert(&I);
                killHelper(&I, &I, kill, defTable);
                break;
              case CAT_add:
              case CAT_sub:
              case CAT_set:
                if (Value *arg = dyn_cast<Value>(call->getArgOperand(0))) {
                  if (defTable.contains(arg)) {                 
                    gen[&I].insert(&I);
                    killHelper(&I, arg, kill, defTable);

                    // Select: kill true and false values
                    if (SelectInst *sel = dyn_cast<SelectInst>(arg)) {
                      if (Instruction *trueVal = dyn_cast<Instruction>(sel->getTrueValue())) {
                        if (defTable.contains(trueVal)) {
                          killHelper(&I, trueVal, kill, defTable);
                        }
                      }
                      if (Instruction *falseVal = dyn_cast<Instruction>(sel->getFalseValue())) {
                        if (defTable.contains(falseVal)) {
                          killHelper(&I, falseVal, kill, defTable);
                        }
                      }
                    }
                  }
                }
                break;
              default:
                break;
            }
          } else {
            if (calls.contains(&I)) {
              if (CallInst *escapeCall = dyn_cast<CallInst>(&I)) {
                switch (aliasAnalysis.getModRefBehavior(escapeCall->getCalledFunction())) {
                  case FMRB_DoesNotAccessMemory:
                    break;
                  default:
                    for (auto escapeVar : escaped) {
                      gen[&I].insert(&I);
                      killHelper(&I, escapeVar, kill, defTable);
                    }
                    break;
                }
              }
            }
          }
        } else if (isa<PHINode>(&I) || isa<SelectInst>(&I)) {
          // If PHI nodes or selects have been redefined, then kill those redefinitions
          for (auto def : defTable) {
            if (def.first == &I) {
              killHelper(&I, def.first, kill, defTable);
              break;
            }
          }
        }
      }
    }

    // Helper function for computing in and out sets
    void computeInOut(Function &F,
                      std::map<Instruction *, std::set<Instruction *>> &inSets,
                      std::map<Instruction *, std::set<Instruction *>> &outSets,
                      std::map<Instruction *, std::set<Instruction *>> gen,
                      std::map<Instruction *, std::set<Instruction *>> kill) {
      std::vector<Instruction *> numToInst;
      std::map<Instruction *, unsigned> instToNum;
      std::vector<BitVector> genBit, killBit, in, out;

      // Assign number to each instruction in F
      unsigned size = assignNumbers(F, numToInst, instToNum);

      // Convert the gen and kill sets to BitVectors
      genBit = std::vector<BitVector>(size);
      killBit = std::vector<BitVector>(size);
      in = std::vector<BitVector>(size);
      out = std::vector<BitVector>(size);
      
      for (unsigned i = 0; i < size; i++) {
        genBit[i] = BitVector(size);
        killBit[i] = BitVector(size);

        for (auto genInst : gen[numToInst[i]]) {
          genBit[i].set(instToNum.at(genInst));
        }
        
        for (auto killInst : kill[numToInst[i]]) {
          killBit[i].set(instToNum.at(killInst));
        }
      }

      // Compute the in and out sets with a work list
      BitVector workList = BitVector(size, true);

      while (workList.any()) {
        int first = workList.find_first();
        workList.reset(first);

        BitVector oldOut = out[first];
        Instruction *inst = numToInst[first];

        Instruction *prev = inst->getPrevNode();
        if (!prev) {
          for (auto pred : predecessors(inst->getParent())) {
            in[first] |= out[instToNum.at(pred->getTerminator())];
          }
        } else {
          in[first] |= out[instToNum.at(prev)];
        }

        out[first] |= in[first];
        out[first].reset(killBit[first]);
        out[first] |= genBit[first];

        if (oldOut != out[first]) {
          Instruction *next = inst->getNextNode();
          if (!next) {
            for (auto succ : successors(inst->getParent())) {
              workList.set(instToNum.at(&(succ->front())));
            }
          } else {
            workList.set(instToNum.at(next));
          }
        }
      }

      // Convert BitVectors to sets and insert them into inSets and outSets
      for (unsigned i = 0; i < size; i++) {
        for (auto bit : in[i].set_bits()) {
          inSets[numToInst[i]].insert(numToInst[bit]);
        }
        for (auto bit : out[i].set_bits()) {
          outSets[numToInst[i]].insert(numToInst[bit]);
        }
      }
      return;
    }

    // This function creates reaching definitions for all instructions in function F
    // and stores them into the maps inSets and outSets. LLVM BitVectors are
    // used to generate the initial gen, kill, in, and out sets before being transformed
    // into sets
    void createReachingDefs(Function &F,
                            AliasAnalysis &aliasAnalysis,
                            std::map<Instruction *, std::set<Instruction *>> &inSets, 
                            std::map<Instruction *, std::set<Instruction *>> &outSets,
                            std::map<Value *, std::set<Instruction *>> defTable) {
      // Compute gen and kill sets
      std::map<Instruction *, std::set<Instruction *>> gen, kill;
      computeGenKill(F, aliasAnalysis, gen, kill, defTable);

      // Compute in and out sets
      computeInOut(F, inSets, outSets, gen, kill);      
    }

    // This function computes memory instructions that may point to each other 
    // using LLVM alias analysis
    void computeMayPointTo(Function &F,
                           AliasAnalysis &aliasAnalysis,
                           std::map<Instruction *, std::set<Instruction *>> &mayPointTo) {
      std::vector<StoreInst *> stores;
      std::vector<Instruction *> loads;

      for (auto &I : instructions(F)) {
        if (StoreInst *store = dyn_cast<StoreInst>(&I)) {
          stores.push_back(store);
        } else if (isa<LoadInst>(&I)) {
          loads.push_back(&I);
        }
      }

      for (auto storeInst : stores) {
        for (auto loadInst : loads) {
          switch (aliasAnalysis.alias(MemoryLocation::get(storeInst), MemoryLocation::get(loadInst))) {
            case AliasResult::MayAlias:
            case AliasResult::PartialAlias:
            case AliasResult::MustAlias:
              mayPointTo[storeInst].insert(loadInst);
              mayPointTo[loadInst].insert(storeInst);
              break;
            default:
              break;
          }
        }
      }
    }

    // This function creates the aliasIn and aliasOut sets for alias analysis
    void createAliasSets(Function &F,
                         AliasAnalysis &aliasAnalysis,
                         std::map<Instruction *, std::set<std::vector<Instruction *>>> &aliasIn,
                         std::map<Instruction *, std::set<std::vector<Instruction *>>> &aliasOut) {
      std::map<Instruction *, std::set<Instruction *>> mayPointTo, pointerToValues;
      std::map<Instruction *, std::set<std::vector<Instruction *>>> aliasGen, aliasKill;

      computeMayPointTo(F, aliasAnalysis, mayPointTo);

      // Compute the alias gen sets
      for (auto &I : instructions(F)) {
        // If I is a store, then for each load it may alias, insert a
        // {load, CAT call} into the gen set
        if (StoreInst *store = dyn_cast<StoreInst>(&I)) {
          if (!isa<SelectInst>(store->getPointerOperand()) && mayPointTo.contains(store)) {
            if (CallInst *valOp = dyn_cast<CallInst>(store->getValueOperand())) {
              for (auto pointer : mayPointTo.at(store)) {
                aliasGen[&I].insert({pointer, valOp});
                pointerToValues[pointer].insert(valOp);
              }
            }
          }
        // If I is a CAT instruction that modifies a load, then go through
        // every other load that it may point to and insert {other load, I}
        // into the set
        } else if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_add:
              case CAT_sub:
              case CAT_set:
                if (LoadInst *arg = dyn_cast<LoadInst>(call->getArgOperand(0))) {
                  if (mayPointTo.contains(arg)) {
                    for (auto store : mayPointTo.at(arg)) {
                      for (auto pointer : mayPointTo.at(store)) {
                        aliasGen[&I].insert({pointer, &I});
                        pointerToValues[pointer].insert(&I);
                      }
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

      // Compute the alias kill sets
      // Kill every pair with the form {pointer, value != stored value}
      for (auto &I : instructions(F)) {
        if (StoreInst *store = dyn_cast<StoreInst>(&I)) {
          if (mayPointTo.contains(store)) {
            if (CallInst *valOp = dyn_cast<CallInst>(store->getValueOperand())) {
              for (auto pointer : mayPointTo.at(store)) {
                for (auto val : pointerToValues.at(pointer)) {
                  if (val != valOp) {
                    aliasKill[&I].insert({pointer, val});
                  }
                }
              }
            }
          }
        } else if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_add:
              case CAT_sub:
              case CAT_set:
                if (LoadInst *arg = dyn_cast<LoadInst>(call->getArgOperand(0))) {
                  if (mayPointTo.contains(arg)) {
                    for (auto store : mayPointTo.at(arg)) {
                      for (auto pointer : mayPointTo.at(store)) {
                        for (auto val : pointerToValues.at(pointer)) {
                          if (val != &I) {
                            aliasKill[&I].insert({pointer, val});
                          }
                        }
                      }
                    }
                  }
                }
                break;
              default:
                break;
            }
          }
        } else if (SelectInst *select = dyn_cast<SelectInst>(&I)) {
          for (auto pointer : pointerToValues) {
            if (LoadInst *loadPtr = dyn_cast<LoadInst>(pointer.first)) {
              if (loadPtr->getPointerOperand() == select->getTrueValue() ||
                  loadPtr->getPointerOperand() == select->getFalseValue()) {
                for (auto val : pointer.second) {
                  aliasKill[&I].insert({pointer.first, val});
                }
              }
            }
          }
        }
      }

      // Generate in/out sets
      bool done;
      do {
        done = true;

        for (auto &I : instructions(F)) {
          Instruction *prev = I.getPrevNode();
          if (!prev) {
            for (auto pred : predecessors(I.getParent())) {
              aliasIn[&I].insert(aliasOut[pred->getTerminator()].begin(), aliasOut[pred->getTerminator()].end());
            }
          } else {
            aliasIn[&I].insert(aliasOut[prev].begin(), aliasOut[prev].end());
          }

          std::set<std::vector<Instruction *>> newOut;
          newOut.insert(aliasGen[&I].begin(), aliasGen[&I].end());
          for (auto vec : aliasIn[&I]) {
            if (!aliasKill[&I].contains(vec)) {
              newOut.insert(vec);
            }
          }

          done = done & (newOut == aliasOut[&I]);
          aliasOut[&I] = newOut;
        }
      } while (!done);
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

    // This function runs through the users of a variable to see if it
    // escapes to another non-CAT function
    bool isEscaped(Value *valToCheck) {
      for (auto user : valToCheck->users()) {
        if (CallInst *call = dyn_cast<CallInst>(user)) {
          if (!CATMap.contains(call->getCalledFunction())) {
            return true;
          }
        } else if (StoreInst *store = dyn_cast<StoreInst>(user)) {
          if (store->getValueOperand() == valToCheck) {
            return true;
          }
        }
      }
      return false;
    }

    // This function checks if a value valToCheck is a constant
    // and returns a pointer to the ConstantInt if it is a constant
    // Otherwise, it returns a nullptr
    ConstantInt *isConstant(Value *valToCheck,
                            std::set<Instruction *> inSet,
                            std::set<std::vector<Instruction *>> mayPointTo) {
      // If the value is an argument, it is not safe to assume it is a constant
      if (isa<Argument>(valToCheck)) {
        return nullptr;
      }

      ConstantInt *constPtr = nullptr;
      ConstantInt *phiConst = nullptr;
      int64_t constant;
      bool initialized = false;

      // If valToCheck is a load, then run alias analysis
      if (LoadInst *load = dyn_cast<LoadInst>(valToCheck)) {
        for (auto aliasPair : mayPointTo) {
          if (load == aliasPair[0]) {
            if (ConstantInt *constInt = isConstant(aliasPair[1], inSet, mayPointTo)) {
              if (!initialized) {
                constPtr = constInt;
                constant = constInt->getSExtValue();
                initialized = true;
              } else if (constant != constInt->getSExtValue()) {
                return nullptr;
              }
            } else {
              return nullptr;
            }
          }
        }

        return constPtr;
      }

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

          if (ConstantInt *constInt = isConstant(phiVal, inSet, mayPointTo)) {
            if (!initialized) {
              phiConst = constInt;
              constant = constInt->getSExtValue();
              initialized = true;
            } else if (constant != constInt->getSExtValue()) {
              phiConst = nullptr;
              break;
            }
          } else {
            phiConst = nullptr;
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
          } else if (isEscaped(valToCheck)) {
            return nullptr;
          }
        }
      }
      
      // Operations performed on the PHI take precedence over incoming values
      return constPtr ? constPtr : phiConst;
    }

    // This function runs constant propagation on a set of CAT instruction
    bool runConstantPropagation(std::map<Instruction *, std::set<Instruction *>> inSets,
                                std::set<Instruction *> &CATInstructions,
                                std::map<Instruction *, std::set<std::vector<Instruction *>>> aliasIn) {
      bool modified = false;
      std::map<Instruction *, ConstantInt *> toReplace;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_get") == callee) {
            if (ConstantInt *c = isConstant(call->getArgOperand(0), inSets[I], aliasIn[I])) {
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
                            std::set<Instruction *> &CATInstructions,
                            std::map<Instruction *, std::set<std::vector<Instruction *>>> aliasIn) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);
          
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            ConstantInt *const1 = isConstant(call->getArgOperand(1), inSets[I], aliasIn[I]);
            ConstantInt *const2 = isConstant(call->getArgOperand(2), inSets[I], aliasIn[I]);

            if (const1 && const2) {
              IntegerType *intType = IntegerType::get(currentModule->getContext(), 64);
              Value *sum = ConstantInt::get(intType, const1->getSExtValue() + const2->getSExtValue(), true);

              Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), sum});
              CATInstructions.insert(newInst);

              toDelete.push_back(I);
              modified = true;
            }
          } else if (currentModule->getFunction("CAT_sub") == callee) {
            ConstantInt *const1 = isConstant(call->getArgOperand(1), inSets[I], aliasIn[I]);
            ConstantInt *const2 = isConstant(call->getArgOperand(2), inSets[I], aliasIn[I]);

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
                                    std::set<Instruction *> &CATInstructions,
                                    std::map<Instruction *, std::set<std::vector<Instruction *>>> aliasIn) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);

          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            if (ConstantInt *c = isConstant(call->getArgOperand(1), inSets[I], aliasIn[I])) {
              // If the 2nd argument is a constant = 0, then simplify to 3rd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(2)});
                Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);

                toDelete.push_back(I);
                modified = true;
              }
            } else if (ConstantInt *c = isConstant(call->getArgOperand(2), inSets[I], aliasIn[I])) {
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
            if (ConstantInt *c = isConstant(call->getArgOperand(2), inSets[I], aliasIn[I])) {
              // If the 3rd argument is a constant = 0, then simplify to 2nd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(1)});
                Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);
                
                toDelete.push_back(I);
                modified = true;
              }
            } else if (call->getArgOperand(1) == call->getArgOperand(2)) {
              // If 2nd and 3rd arguments are the same variable, then simplify result to 0
              Value *zeroConst = ConstantInt::get(IntegerType::get(currentModule->getContext(), 64), 0, true);
              Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), zeroConst});
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

    // This function regenerates the data structures needed for
    // constant optimizations every time the function is modified
    void regenerateDataStructs(Function &F,
                               AliasAnalysis &aliasAnalysis,
                               std::map<Value *, std::set<Instruction *>> &defTable,
                               std::map<Instruction *, std::set<Instruction *>> &inSets,
                               std::map<Instruction *, std::set<Instruction *>> &outSets,
                               std::map<Instruction *, std::set<std::vector<Instruction *>>> &aliasIn,
                               std::map<Instruction *, std::set<std::vector<Instruction *>>> &aliasOut) {
      defTable.clear();
      inSets.clear();
      outSets.clear();
      aliasIn.clear();
      aliasOut.clear();
      createDefTable(F, defTable);
      createReachingDefs(F, aliasAnalysis, inSets, outSets, defTable);
      createAliasSets(F, aliasAnalysis, aliasIn, aliasOut);
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      bool modified = false;
      std::set<Instruction *> CATInstructions, nonCATCalls;
      std::map<Instruction *, std::set<Instruction *>> inSets, outSets;
      std::map<Value *, std::set<Instruction *>> defTable;
      std::map<Instruction *, std::set<std::vector<Instruction *>>> aliasIn, aliasOut;

      AliasAnalysis &aliasAnalysis = getAnalysis<AAResultsWrapperPass>().getAAResults();
      getCATInstructions(F, CATInstructions);
      regenerateDataStructs(F, aliasAnalysis, defTable, inSets, outSets, aliasIn, aliasOut);

      printDefTable(F, defTable);
      printReachingDefs(F, inSets, outSets);
      // printAliasSets(F, aliasIn, aliasOut);

      // Constant propagation
      modified |= runConstantPropagation(inSets, CATInstructions, aliasIn);

      // Constant folding
      if (modified) {
        regenerateDataStructs(F, aliasAnalysis, defTable, inSets, outSets, aliasIn, aliasOut);
      }
      modified |= runConstantFolding(inSets, CATInstructions, aliasIn);

      // Algebraic Simplification
      if (modified) {
        regenerateDataStructs(F, aliasAnalysis, defTable, inSets, outSets, aliasIn, aliasOut);
      }
      modified |= runAlgebraicSimplification(inSets, CATInstructions, aliasIn);

      return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<AAResultsWrapperPass>();
    }

    // This function prints the definitions of a variable for debugging purposes
    void printDefTable(Function &F, 
                       std::map<Value *, std::set<Instruction *>> defTable) {
      for (auto [def, insts] : defTable) {
        for (auto inst : insts) {
          errs() << F.getName() << *def << *inst << "\n";
        }
      }
    }

    // This function prints the reaching definitions of a function F for debugging purposes
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

    void printAliasSets(Function &F,
                        std::map<Instruction *, std::set<std::vector<Instruction *>>> aliasIn, 
                        std::map<Instruction *, std::set<std::vector<Instruction *>>> aliasOut) {
      errs() << "Function \"" << F.getName() << "\"\n";
      for (auto &I : instructions(F)) {
        errs() << "INSTRUCTION:" << I << "\nIN\n{\n";
        for (auto in : aliasIn[&I]) {
          errs() << *(in[0]) << *(in[1]) << "\n";
        }
        errs() << "}\nOUT\n{\n";
        for (auto out : aliasOut[&I]) {
          errs() << *(out[0]) << *(out[1]) << "\n";
        }
        errs() << "}\n";
      }
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
