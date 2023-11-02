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
    
    // This function creates a definition table of CAT variables
    void createDefTable(Function &F,
                        std::map<Instruction *, std::set<Instruction *>> &defTable) {
      for (auto &I : instructions(F)) {
        if (CallInst *call = dyn_cast<CallInst>(&I)) {
          if (currentModule->getFunction("CAT_new") == call->getCalledFunction()) {
            defTable[&I].insert(&I);
          }
        }

        for (auto user : I.users()) {
          if (CallInst *userCall = dyn_cast<CallInst>(user)) {
            Function *userCallee = userCall->getCalledFunction();
            if (CATMap.contains(userCallee)) {
              switch (CATMap.at(userCallee)) {
                case CAT_add:
                case CAT_sub:
                case CAT_set:
                  if (userCall->getArgOperand(0) == &I) {
                    defTable[&I].insert(userCall);
                  }
                  break;
                default:
                  break;
              }
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
    void getEscapedInsts(std::map<Instruction *, std::set<Instruction *>> defTable,
                         std::set<Instruction *> &escaped,
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

    // This function creates the mayPointTo and mustPointTo sets for alias analysis
    void createAliasSets(Function &F,
                         AliasAnalysis &aliasAnalysis,
                         std::map<Instruction *, std::set<Instruction *>> &mayPointTo,
                         std::map<Instruction *, std::set<Instruction *>> &mustPointTo) {
      std::vector<StoreInst *> stores;
      std::vector<Instruction *> loads;

      for (auto &I : instructions(F)) {
        if (StoreInst *store = dyn_cast<StoreInst>(&I)) {
          stores.push_back(store);
        } else if (isa<LoadInst>(&I)) {
          loads.push_back(&I);
        }
      }

      for (auto store : stores) {
        for (auto load : loads) {
          if (Instruction *stored = dyn_cast<Instruction>(store->getValueOperand())) {
            switch (aliasAnalysis.alias(MemoryLocation::get(store), MemoryLocation::get(load))) {
              case AliasResult::MayAlias:
              case AliasResult::PartialAlias:
                mayPointTo[stored].insert(load);
                mayPointTo[load].insert(stored);
                break;
              case AliasResult::MustAlias:
                mustPointTo[stored].insert(load);
                mustPointTo[load].insert(stored);
                break;
              default:
                break;
            }
          }
        }
      }

      for (auto [may, pointTo] : mayPointTo) {
        errs() << "=============MAY=============" << *may << "\n";
        for (auto point : pointTo) {
          errs() << *point << "\n";
        }
        errs() << "\n";
      }
      for (auto [must, pointTo] : mustPointTo) {
        errs() << "==============MUST============" << *must << "\n";
        for (auto point : pointTo) {
          errs() << *point << "\n";
        }
        errs() << "\n";
      }
    }

    // Helper function for killing instructions
    void killHelper(Instruction *killer,
                    Instruction *killed,
                    std::map<Instruction *, std::set<Instruction *>> &kill,
                    std::map<Instruction *, std::set<Instruction *>> mustPointTo,
                    std::map<Instruction *, std::set<Instruction *>> defTable) {
      kill[killer].insert(defTable.at(killed).begin(), defTable.at(killed).end());

      if (mustPointTo.contains(killed)) {
        std::set<Instruction *> mustLoad = mustPointTo.at(killed);
        for (auto loadInst : mustPointTo.at(killed)) {
          for (auto stored : mustPointTo.at(loadInst)) {
            if (stored != killed) {
              kill[killer].insert(stored);
            }
          }
        }
      }
    }

    // Helper function for computing gen and kill sets
    void computeGenKill(Function &F,
                        AliasAnalysis &aliasAnalysis,
                        std::map<Instruction *, std::set<Instruction *>> &gen,
                        std::map<Instruction *, std::set<Instruction *>> &kill,
                        std::map<Instruction *, std::set<Instruction *>> defTable) {
      std::set<Instruction *> escaped, calls;
      std::map<Instruction *, std::set<Instruction *>> mayPointTo, mustPointTo;
      getEscapedInsts(defTable, escaped, calls);
      createAliasSets(F, aliasAnalysis, mayPointTo, mustPointTo);

      for (auto &I : instructions(F)) {
        if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_new:
                gen[&I].insert(&I);
                killHelper(&I, &I, kill, mustPointTo, defTable);
                kill[&I].erase(&I);
                break;
              case CAT_add:
              case CAT_sub:
              case CAT_set:
                if (Instruction *arg = dyn_cast<Instruction>(call->getArgOperand(0))) {
                  if (defTable.contains(arg)) {                 
                    gen[&I].insert(&I);
                    killHelper(&I, arg, kill, mustPointTo, defTable);
                    kill[&I].erase(&I);

                    // Select: kill true and false values
                    if (SelectInst *sel = dyn_cast<SelectInst>(arg)) {
                      if (Instruction *trueVal = dyn_cast<Instruction>(sel->getTrueValue())) {
                        if (defTable.contains(trueVal)) {
                          killHelper(&I, trueVal, kill, mustPointTo, defTable);
                        }
                      }
                      if (Instruction *falseVal = dyn_cast<Instruction>(sel->getFalseValue())) {
                        if (defTable.contains(falseVal)) {
                          killHelper(&I, falseVal, kill, mustPointTo, defTable);
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
            // If I is not a CAT instruction, see if it is a call that variables escape to
            // If call is not a NoModRef, then kill the escaped variable
            if (calls.contains(&I)) {
              for (auto var : escaped) {
                if (CallInst *varCall = dyn_cast<CallInst>(var)) {
                  switch (aliasAnalysis.getModRefInfo(&I, varCall)) {
                    case ModRefInfo::ModRef:
                    case ModRefInfo::Mod:
                    case ModRefInfo::Ref:
                    case ModRefInfo::MustRef:
                    case ModRefInfo::MustMod:
                    case ModRefInfo::MustModRef:
                      gen[&I].insert(&I);
                      killHelper(&I, var, kill, mustPointTo, defTable);
                      break;
                    default:
                      break;
                  }
                }
              }
            }
          }
        } else if (isa<PHINode>(&I) || isa<SelectInst>(&I)) {
          // If PHI nodes or selects have been redefined, then kill those redefinitions
          for (auto def : defTable) {
            if (def.first == &I) {
              killHelper(&I, def.first, kill, mustPointTo, defTable);
              break;
            }
          }
        } else if (isa<LoadInst>(&I)) {
          // If I is a load, then add both must point to and may point to of
          // the corresponding stored value
          if (mayPointTo.contains(&I)) {
            gen[&I].insert(mayPointTo.at(&I).begin(), mayPointTo.at(&I).end());
          }
          if (mustPointTo.contains(&I)) {
            gen[&I].insert(mustPointTo.at(&I).begin(), mustPointTo.at(&I).end());
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
                            std::map<Instruction *, std::set<Instruction *>> defTable) {
      // Compute gen and kill sets
      std::map<Instruction *, std::set<Instruction *>> gen, kill;
      computeGenKill(F, aliasAnalysis, gen, kill, defTable);

      // Compute in and out sets
      computeInOut(F, inSets, outSets, gen, kill);      
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
    ConstantInt *isConstant(std::set<Instruction *> inSet, 
                            Value *valToCheck) {
      // If the value is an argument, it is not safe to assume it is a constant
      if (isa<Argument>(valToCheck)) {
        return nullptr;
      }

      ConstantInt *constPtr = nullptr;
      int64_t constant;
      bool initialized = false;
      ConstantInt *phiConst = nullptr;
      bool escaped = isEscaped(valToCheck);

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

          if (ConstantInt *constInt = isConstant(inSet, phiVal)) {
            if (!initialized) {
              phiConst = constInt;
              constant = constInt->getSExtValue();
              initialized = true;
            } else if (constant != constInt->getSExtValue()) {
              phiConst = nullptr;
              initialized = false;
              break;
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
          } else if (escaped) {
            return nullptr;
          }
        }
      }
      
      // Operations performed on the PHI take precedence over incoming values
      return constPtr ? constPtr : phiConst;
    }

    // This function runs constant propagation on a set of CAT instruction
    bool runConstantPropagation(std::map<Instruction *, std::set<Instruction *>> inSets,
                                std::set<Instruction *> &CATInstructions) {
      bool modified = false;
      std::map<Instruction *, ConstantInt *> toReplace;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_get") == callee) {
            if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(0))) {
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
                            std::set<Instruction *> &CATInstructions) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);
          
          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            ConstantInt *const1 = isConstant(inSets[I], call->getArgOperand(1));
            ConstantInt *const2 = isConstant(inSets[I], call->getArgOperand(2));

            if (const1 && const2) {
              IntegerType *intType = IntegerType::get(currentModule->getContext(), 64);
              Value *sum = ConstantInt::get(intType, const1->getSExtValue() + const2->getSExtValue(), true);

              Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), sum});
              CATInstructions.insert(newInst);

              toDelete.push_back(I);
              modified = true;
            }
          } else if (currentModule->getFunction("CAT_sub") == callee) {
            ConstantInt *const1 = isConstant(inSets[I], call->getArgOperand(1));
            ConstantInt *const2 = isConstant(inSets[I], call->getArgOperand(2));

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
                                    std::set<Instruction *> &CATInstructions) {
      bool modified = false;
      std::vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (CallInst *call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);

          Function *callee = call->getCalledFunction();
          if (currentModule->getFunction("CAT_add") == callee) {
            if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(1))) {
              // If the 2nd argument is a constant = 0, then simplify to 3rd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(currentModule->getFunction("CAT_get"), {call->getArgOperand(2)});
                Instruction *newInst = builder.CreateCall(currentModule->getFunction("CAT_set"), {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);

                toDelete.push_back(I);
                modified = true;
              }
            } else if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(2))) {
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
            if (ConstantInt *c = isConstant(inSets[I], call->getArgOperand(2))) {
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
                               std::map<Instruction *, std::set<Instruction *>> &inSets,
                               std::map<Instruction *, std::set<Instruction *>> &outSets,
                               std::map<Instruction *, std::set<Instruction *>> &defTable) {
      inSets.clear();
      outSets.clear();
      defTable.clear();
      createDefTable(F, defTable);
      createReachingDefs(F, aliasAnalysis, inSets, outSets, defTable);
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      bool modified = false;
      std::set<Instruction *> CATInstructions;
      std::map<Instruction *, std::set<Instruction *>> inSets, outSets, defTable;

      AliasAnalysis &aliasAnalysis = getAnalysis<AAResultsWrapperPass>().getAAResults();
      getCatInstructions(F, CATInstructions);
      regenerateDataStructs(F, aliasAnalysis, inSets, outSets, defTable);

      printDefTable(F, defTable);
      printReachingDefs(F, inSets, outSets);

      // Constant propagation
      modified |= runConstantPropagation(inSets, CATInstructions);

      // Constant folding
      if (modified) {
        regenerateDataStructs(F, aliasAnalysis, inSets, outSets, defTable);
      }
      modified |= runConstantFolding(inSets, CATInstructions);

      // Algebraic Simplification
      if (modified) {
        regenerateDataStructs(F, aliasAnalysis, inSets, outSets, defTable);
      }
      modified |= runAlgebraicSimplification(inSets, CATInstructions);

      return modified;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<AAResultsWrapperPass>();
    }

    // This function prints the definitions of a variable for debugging purposes
    void printDefTable(Function &F, 
                       std::map<Instruction *, std::set<Instruction *>> defTable) {
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
