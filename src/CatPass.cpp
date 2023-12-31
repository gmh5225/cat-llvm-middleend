#include "llvm/Pass.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
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
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/LoopPeel.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include <map>
#include <set>
#include <vector>

using namespace llvm;
using namespace std;

namespace {
  enum CAT_API {CAT_new, CAT_add, CAT_sub, CAT_get, CAT_set, CAT_destroy};

  struct AliasValue {
    Instruction *pointer;
    Instruction *variable;
  };

  bool operator==(const AliasValue &lhs, const AliasValue &rhs) {
    return lhs.pointer == rhs.pointer && lhs.variable == rhs.variable;
  }

  bool operator<(const AliasValue &lhs, const AliasValue &rhs) {
    return lhs.pointer == rhs.pointer 
      ? lhs.variable < rhs.variable 
      : lhs.pointer < rhs.pointer;
  }

  struct CAT : public ModulePass {
    static char ID; 
    
    CAT() : ModulePass(ID) {}

    /**
     * This function is invoked once at the initialization phase 
     * of the compiler.
     * 
     * The LLVM IR of functions isn't ready at this point.
     */
    bool doInitialization(Module &M) override {
      CATMap[M.getFunction("CAT_new")] = CAT_new;
      CATMap[M.getFunction("CAT_add")] = CAT_add;
      CATMap[M.getFunction("CAT_sub")] = CAT_sub;
      CATMap[M.getFunction("CAT_get")] = CAT_get;
      CATMap[M.getFunction("CAT_set")] = CAT_set;
      CATMap[M.getFunction("CAT_destroy")] = CAT_destroy;
      return false;
    }

    /**
     * This function is invoked once per module compiled.
     */
    bool runOnModule(Module &M) override {
      bool modified = false;

      CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
      modified |= inlineFunctions(M, CG);

      modified |= transformLoops(M);
      
      modified |= optimizeFunctions(M);
      
      return modified;
    }

    /**
     * We don't modify the program, so we preserve all analyses.
     * 
     * The LLVM IR of functions isn't ready at this point.
     */
    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<AAResultsWrapperPass>();
      AU.addRequired<CallGraphWrapperPass>();
      AU.addRequired<AssumptionCacheTracker>();
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<LoopInfoWrapperPass>();
      AU.addRequired<ScalarEvolutionWrapperPass>();
      AU.addRequired<TargetTransformInfoWrapperPass>();
      return;
    }

    private:
    map<Function *, CAT_API> CATMap;

    /**
     * Wrapper function for performing inter-procedural code analysis.
     */
    bool inlineFunctions(Module &M, CallGraph &CG) {
      bool modified = false;
      
      // Inline functions
      for (auto &F : M) {
        if (F.empty()) {
          continue;
        }
        modified |= inlineFunction(M, F, CG);
      }

      return modified;
    }

    /**
     * This function inlines callees in function F.
     */
    bool inlineFunction(Module &M, Function &F, CallGraph &CG) {
      bool modified = false;
      bool inlined = false;

      for (auto &I : instructions(F)) {
        if (auto call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (callee == NULL || isRecursive(callee, CG)) {
            continue;
          }

          InlineFunctionInfo IFI;
          inlined |= InlineFunction(*call, IFI).isSuccess();
          if (inlined) {
            modified = true;
            break;
          }
        }
      }

      if (inlined) {
        modified |= inlineFunction(M, F, CG);
      }

      return modified;
    }

    /**
     * This function checks if a function calls itself using the call graph.
     */
    bool isRecursive(Function *F, CallGraph &CG) {
      if (F->empty()) {
        return false;
      }

      CallGraphNode *n = CG[F];

      for (auto callee : *n) {
        auto calleeNode = callee.second;
        auto calleeF = calleeNode->getFunction();
        if (F == calleeF) {
          return true;
        }
      }

      return false;
    }

    bool transformLoops(Module &M) {
      for (auto &F : M) {
        if (F.empty() || F.getInstructionCount() > 800) {
          continue;
        }

        errs() << F.getInstructionCount() << "\n";
        errs() << F.size() << "\n";

        auto &LI = getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
        auto &DT = getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
        auto &SE = getAnalysis<ScalarEvolutionWrapperPass>(F).getSE();
        auto &AC = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);
        const auto &TTI = getAnalysis<TargetTransformInfoWrapperPass>().getTTI(F);

        OptimizationRemarkEmitter ORE(&F);
        for (auto i : LI) {
          auto loop = &*i;
          if (analyzeLoop(LI, loop, DT, SE, AC, ORE, TTI)) {
            return true;
          }
        }
      }

      return false;
    }

    bool analyzeLoop(LoopInfo &LI, Loop *loop, DominatorTree &DT,
                     ScalarEvolution &SE, AssumptionCache &AC,
                     OptimizationRemarkEmitter &ORE,
                     const TargetTransformInfo &TTI) {
      if (loop->isLoopSimplifyForm() && loop->isLCSSAForm(DT)) {
        auto peelingCount = 1;
        auto peeled = peelLoop(loop, peelingCount, &LI, &SE, DT, &AC, true);
        if (peeled){
          errs() << "   Peeled\n";
          return true;
        }

        // UnrollLoopOptions ULO;
        // ULO.Count = 4;
        // ULO.Force = false;
        // ULO.Runtime = true;
        // ULO.AllowExpensiveTripCount = true;
        // ULO.UnrollRemainder = false;
        // ULO.ForgetAllSCEV = true;

        // auto unrolled = UnrollLoop(loop, ULO, &LI, &SE, &DT, &AC, &TTI, &ORE,
        //                            true);

        // switch (unrolled) {
        //   case LoopUnrollResult::FullyUnrolled:
        //   case LoopUnrollResult::PartiallyUnrolled:
        //     return true;
        //   case LoopUnrollResult::Unmodified:
        //     break;
        // }
      }

      auto subloops = loop->getSubLoops();
      for (auto j : subloops) {
        auto subloop = &*j;
        if (analyzeLoop(LI, subloop, DT, SE, AC, ORE, TTI)) {
          return true;
        }
      }
      
      return false;
    }

    /**
     * Wrapper function for performing constant optimizations.
     */
    bool optimizeFunctions(Module &M) {
      bool modified = false;
      for (auto &F : M) {
        if (F.empty()) {
          continue;
        }
        modified |= optimizeFunction(M, F);
      }
      return modified;
    }

    /**
     * This function is invoked once per function compiled.
     * 
     * The LLVM IR of the input functions is ready and it can be analyzed 
     * and/or transformed.
     */
    bool optimizeFunction(Module &M, Function &F) {
      bool modified = false;

      set<Instruction *> CATInstructions;
      set<Instruction *> nonCATInsts;
      getCallInstructions(F, CATInstructions, nonCATInsts);

      AliasAnalysis &AA = getAnalysis<AAResultsWrapperPass>(F).getAAResults();
      map<Instruction *, set<Instruction *>> inSets;
      map<Instruction *, set<Instruction *>> outSets;
      map<Instruction *, set<Instruction *>> defTable;
      map<Instruction *, set<Instruction *>> mayPointTo;
      map<Instruction *, set<AliasValue>> aliasIn;
      map<Instruction *, set<AliasValue>> aliasOut;

      // Clear and regenerate data structures
      auto populateStructs = [&]() {
        defTable.clear();
        mayPointTo.clear();
        inSets.clear();
        outSets.clear();
        aliasIn.clear();
        aliasOut.clear();
        createDefTable(F, defTable);
        createMayPointTo(F, AA, mayPointTo);
        createReachingDefs(F, AA, inSets, outSets, defTable, mayPointTo, 
                           nonCATInsts);
        createAliasSets(F, AA, aliasIn, aliasOut, mayPointTo, nonCATInsts);
      };


      getCallInstructions(F, CATInstructions, nonCATInsts);
      
      getCallInstructions(F, CATInstructions, nonCATInsts);
      populateStructs();

      // if (F.getName() == "main") {
      //   printDefTable(F, defTable);
      //   printReachingDefs(F, inSets, outSets);
      //   printMayPointTo(F, mayPointTo);
      //   printAliasSets(F, aliasIn, aliasOut);
      // }
      
      // Constant propagation
      modified |= runConstantPropagation(M, CATInstructions, inSets, aliasIn);

      // Constant folding
      if (modified) {
        populateStructs();
      }
      modified |= runConstantFolding(M, CATInstructions, inSets, aliasIn);

      // Algebraic Simplification
      if (modified) {
        populateStructs();
      }
      modified |= runAlgebraicSimplification(M, CATInstructions, inSets, 
                                             aliasIn);

      return modified;
    }

    /**
     * This function stores all CAT instructions in the set parameter.
     */
    void getCallInstructions(Function &F, 
                             set<Instruction *> &CATInstructions,
                             set<Instruction *> &nonCATInsts) {
      for (auto &I : instructions(F)) {
        if (auto call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            CATInstructions.insert(&I);
          } else if (!callee->empty()) {
            nonCATInsts.insert(&I);
          }
        }
      }
    }
    
    /**
     * This function creates a definition table of CAT variables.
     */
    void createDefTable(
        Function &F,
        map<Instruction *, set<Instruction *>> &defTable) {
      for (auto &I : instructions(F)) {
        if (auto call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_new:
                defTable[&I].insert(&I);
                break;
              case CAT_add:
              case CAT_sub:
              case CAT_set:
                if (auto arg = dyn_cast<Instruction>(
                    call->getArgOperand(0))) {
                  if (!isa<LoadInst>(arg)) {
                    defTable[arg].insert(&I);
                  }
                }
                break;
              default:
                break;
            }
          }
        }
      }
    }

    /**
     * This function computes memory instructions that may point to 
     * each other using LLVM alias analysis.
     */
    void createMayPointTo(
        Function &F, 
        AliasAnalysis &AA,
        map<Instruction *, set<Instruction *>> &mayPointTo) {
      vector<StoreInst *> stores;
      vector<Instruction *> loads;

      for (auto &I : instructions(F)) {
        if (auto store = dyn_cast<StoreInst>(&I)) {
          stores.push_back(store);
        } else if (isa<LoadInst>(&I)) {
          loads.push_back(&I);
        }
      }

      for (auto storeInst : stores) {
        for (auto loadInst : loads) {
          switch (AA.alias(MemoryLocation::get(storeInst), 
                           MemoryLocation::get(loadInst))) {
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

    /**
     * This function creates reaching definitions for all instructions 
     * in function F and stores them into the maps inSets and outSets. 
     * 
     * LLVM BitVectors are used to generate the initial gen, kill, 
     * in, and out sets before being transformed into sets.
     */
    void createReachingDefs(Function &F, AliasAnalysis &AA,
                            map<Instruction *, set<Instruction *>> &inSets, 
                            map<Instruction *, set<Instruction *>> &outSets,
                            map<Instruction *, set<Instruction *>> defTable,
                            map<Instruction *, set<Instruction *>> mayPointTo,
                            set<Instruction *> nonCATInsts) {
      // Compute gen and kill sets
      map<Instruction *, set<Instruction *>> gen;
      map<Instruction *, set<Instruction *>> kill;
      computeGenKill(F, AA, gen, kill, defTable, mayPointTo, nonCATInsts);

      // Compute in and out sets
      computeInOut(F, inSets, outSets, gen, kill);      
    }

    /**
     * Helper function for computing gen and kill sets.
     */
    void computeGenKill(Function &F, AliasAnalysis &AA,
                        map<Instruction *, set<Instruction *>> &gen,
                        map<Instruction *, set<Instruction *>> &kill,
                        map<Instruction *, set<Instruction *>> defTable,
                        map<Instruction *, set<Instruction *>> mayPointTo,
                        set<Instruction *> nonCATInsts) {
      set<Instruction *> escaped;
      getEscapedInsts(defTable, escaped);

      for (auto &I : instructions(F)) {
        if (auto call = dyn_cast<CallInst>(&I)) {
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
                if (auto arg = dyn_cast<Instruction>(
                    call->getArgOperand(0))) {
                  if (defTable.contains(arg)) {
                    gen[&I].insert(&I);
                    killHelper(&I, arg, kill, defTable);
                  // Kill every value that loads may point to
                  } else if (mayPointTo.contains(arg)) {
                    for (auto point : mayPointTo.at(arg)) {
                      if (auto store = dyn_cast<StoreInst>(point)) {
                        if (auto val = dyn_cast<Instruction>(
                            store->getValueOperand())) {
                          if (defTable.contains(val)) {
                            gen[&I].insert(&I);
                            kill[&I].insert(defTable.at(val).begin(), 
                                            defTable.at(val).end());
                            kill[&I].erase(&I);
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
          } else if (nonCATInsts.contains(&I)) {
            if (auto escapeCall = dyn_cast<CallInst>(&I)) {
              switch (AA.getModRefBehavior(escapeCall->getCalledFunction())) {
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
        } else if (isa<PHINode>(&I) || isa<SelectInst>(&I)) {
          // If PHI nodes or selects have been redefined, then 
          // kill those redefinitions
          for (auto def : defTable) {
            if (def.first == &I) {
              killHelper(&I, def.first, kill, defTable);
              break;
            }
          }
        }
      }
    }

    /**
     * This function finds every variable that escapes.
     */
    void getEscapedInsts(map<Instruction *, set<Instruction *>> defTable,
                         set<Instruction *> &escaped) {
      for (auto def : defTable) {
        for (auto user : def.first->users()) {
          if (auto call = dyn_cast<CallInst>(user)) {
            if (!CATMap.contains(call->getCalledFunction())) {
              escaped.insert(def.first);
            }
          } else if (auto store = dyn_cast<StoreInst>(user)) {
            if (store->getValueOperand() == def.first) {
              escaped.insert(def.first);
            }
          }
        }
      }
    }

    /**
     * Helper function for killing instructions.
     */
    void killHelper(Instruction *killer, Instruction *killed,
                    map<Instruction *, set<Instruction *>> &kill,
                    map<Instruction *, set<Instruction *>> defTable) {
      kill[killer].insert(defTable.at(killed).begin(),
                          defTable.at(killed).end());
      kill[killer].erase(killer);
    }

    /**
     * Helper function for computing in and out sets.
     */
    void computeInOut(Function &F,
                      map<Instruction *, set<Instruction *>> &inSets,
                      map<Instruction *, set<Instruction *>> &outSets,
                      map<Instruction *, set<Instruction *>> gen,
                      map<Instruction *, set<Instruction *>> kill) {
      // Assign number to each instruction in F
      vector<Instruction *> numToInst;
      map<Instruction *, unsigned> instToNum;
      unsigned size = assignNumbers(F, numToInst, instToNum);

      // Convert the gen and kill sets to BitVectors
      vector<BitVector> genBit(size);
      vector<BitVector> killBit(size);
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
      vector<BitVector> in(size);
      vector<BitVector> out(size);
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

      // Convert BitVectors to sets and insert them into inSets and outSets.
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

    /**
     * This function assigns numbers to each instruction in function F.
     * 
     * Returns the number of instructions in function F.
     */
    unsigned assignNumbers(Function &F, 
                           vector<Instruction *> &numToInst, 
                           map<Instruction *, unsigned> &instToNum) {
      unsigned num = 0;
      for (auto &I : instructions(F)) {
        numToInst.push_back(&I);
        instToNum[&I] = num;
        num++;
      }
      return num;
    }

    /**
     * This function creates in and out sets for alias analysis.
     */
    void createAliasSets(Function &F, AliasAnalysis &AA,
                         map<Instruction *, set<AliasValue>> &aliasIn,
                         map<Instruction *, set<AliasValue>> &aliasOut,
                         map<Instruction *, set<Instruction *>> mayPointTo,
                         set<Instruction *> nonCATInsts) {
      // Compute gen and kill sets
      map<Instruction *, set<Instruction *>> pointerToValues;
      map<Instruction *, set<AliasValue>> aliasGen;
      map<Instruction *, set<AliasValue>> aliasKill;
      computeAliasGen(F, AA, aliasGen, pointerToValues, mayPointTo, 
                      nonCATInsts);
      computeAliasKill(F, aliasKill, pointerToValues, mayPointTo, 
                       nonCATInsts);

      // Generate in/out sets
      bool done = false;

      while (!done) {
        done = true;

        for (auto &I : instructions(F)) {
          Instruction *prev = I.getPrevNode();
          if (!prev) {
            for (auto pred : predecessors(I.getParent())) {
              aliasIn[&I].insert(aliasOut[pred->getTerminator()].begin(), 
                                 aliasOut[pred->getTerminator()].end());
            }
          } else {
            aliasIn[&I].insert(aliasOut[prev].begin(), aliasOut[prev].end());
          }

          set<AliasValue> newOut;
          newOut.insert(aliasGen[&I].begin(), aliasGen[&I].end());
          for (auto val : aliasIn[&I]) {
            if (!aliasKill[&I].contains(val)) {
              newOut.insert(val);
            }
          }

          done &= newOut == aliasOut[&I];
          aliasOut[&I] = newOut;
        }
      }
    }

    /**
     * Helper function for computing the alias gen sets.
     */
    void computeAliasGen(
        Function &F,
        AliasAnalysis &AA,
        map<Instruction *, set<AliasValue>> &aliasGen,
        map<Instruction *, set<Instruction *>> &pointerToValues,
        map<Instruction *, set<Instruction *>> mayPointTo,
        set<Instruction *> nonCATInsts) {
      // Compute the alias gen sets
      for (auto &I : instructions(F)) {
        // If I is a store, then for each load it may alias, insert a
        // {load, CAT call} into the gen set
        if (auto store = dyn_cast<StoreInst>(&I)) {
          if (!isa<SelectInst>(store->getPointerOperand()) 
              && mayPointTo.contains(store)) {
            if (auto valOp = dyn_cast<CallInst>(store->getValueOperand())) {
              for (auto pointer : mayPointTo.at(store)) {
                aliasGen[&I].insert({pointer, valOp});
                pointerToValues[pointer].insert(valOp);
              }
            }
          }
        // If I is a CAT instruction that modifies a load, then go through
        // every other load that it may point to and insert {other load, I}
        // into the set
        } else if (auto call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_add:
              case CAT_sub:
              case CAT_set:
                if (auto arg = dyn_cast<LoadInst>(call->getArgOperand(0))) {
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
          } else if (nonCATInsts.contains(&I)) {
            if (auto functionCall = dyn_cast<CallInst>(&I)) {
              switch (AA.getModRefBehavior(
                  functionCall->getCalledFunction())) {
                case FMRB_DoesNotAccessMemory:
                  break;
                default:
                  for (auto load : mayPointTo) {
                    if (isa<LoadInst>(load.first)) {
                      aliasGen[&I].insert({load.first, &I});
                    }
                  }
                  break;
              }
            }
          }
        }
      }
    }

    /**
     * Helper function for computing the alias kill sets.
     */
    void computeAliasKill(
        Function &F,
        map<Instruction *, set<AliasValue>> &aliasKill,
        map<Instruction *, set<Instruction *>> pointerToValues,
        map<Instruction *, set<Instruction *>> mayPointTo,
        set<Instruction *> nonCATInsts) {
      // Compute the alias kill sets
      // Kill every pair with the form {pointer, value != stored value}
      for (auto &I : instructions(F)) {
        if (auto store = dyn_cast<StoreInst>(&I)) {
          if (mayPointTo.contains(store)) {
            if (auto valOp = dyn_cast<CallInst>(store->getValueOperand())) {
              for (auto pointer : mayPointTo.at(store)) {
                for (auto val : pointerToValues.at(pointer)) {
                  if (val != valOp) {
                    aliasKill[&I].insert({pointer, val});
                  }
                }
              }
            }
          }
        } else if (auto call = dyn_cast<CallInst>(&I)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_add:
              case CAT_sub:
              case CAT_set:
                if (auto arg = dyn_cast<LoadInst>(call->getArgOperand(0))) {
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
          } else if (nonCATInsts.contains(&I)) {
            for (auto [pointer, values] : pointerToValues) {
              for (auto val : values) {
                if (val != &I) {
                  aliasKill[&I].insert({pointer, val});
                }
              }
            }
          }
        } else if (auto select = dyn_cast<SelectInst>(&I)) {
          for (auto pointer : pointerToValues) {
            if (auto loadPtr = dyn_cast<LoadInst>(pointer.first)) {
              if (loadPtr->getPointerOperand() == select->getTrueValue() 
                  || loadPtr->getPointerOperand() == select->getFalseValue()) {
                for (auto val : pointer.second) {
                  aliasKill[&I].insert({pointer.first, val});
                }
              }
            }
          }
        }
      }
    }

    /**
     * This function checks if a value valToCheck is a constant and 
     * returns a ConstantInt pointer if it is a constant. 
     * 
     * Otherwise, it returns a null pointer.
     */
    ConstantInt *isConstant(Value *valToCheck, set<Instruction *> inSet,
                            set<AliasValue> mptIn) {
      // If the value is an argument, it is not safe 
      // to assume it is a constant
      if (isa<Argument>(valToCheck)) {
        return nullptr;
      }

      // If valToCheck is a load, then run alias analysis
      if (auto load = dyn_cast<LoadInst>(valToCheck)) {
        return isLoadConstant(load, inSet, mptIn);
      }

      // If valToCheck is a PHI node, check if all incoming values 
      // are constants and if they are the same constant
      // If not, then valToCheck is not a constant
      ConstantInt *phiConst = nullptr;
      int64_t constant;
      bool initialized = false;
      if (auto phi = dyn_cast<PHINode>(valToCheck)) {
        if (containsCycle(valToCheck)) {
          return nullptr;
        }

        for (unsigned i = 0; i < phi->getNumIncomingValues(); i++) {
          Value *phiVal = phi->getIncomingValue(i);
          
          if (isa<UndefValue>(phiVal)) {
            continue;
          }

          if (!setConstants(isConstant(phiVal, inSet, mptIn), phiConst, 
                            constant, initialized)) {
            break;
          }
        }
      }

      // Go back and check if PHI has been set to anything
      initialized = false;

      // Check if selects are constants
      ConstantInt *constPtr = nullptr;
      if (auto select = dyn_cast<SelectInst>(valToCheck)) {
        if (containsCycle(valToCheck)) {
          return nullptr;
        }

        if (ConstantInt* constInt = isConstant(select->getTrueValue(), inSet,
                                               mptIn)) {
          constPtr = constInt;
          constant = constInt->getSExtValue();
          initialized = true;

          if (ConstantInt* constInt = isConstant(select->getFalseValue(),
                                                 inSet, mptIn)) {
            if (constant != constInt->getSExtValue()) {
              return nullptr;
            }
          } else {
            return nullptr;
          }
        } else {
          return nullptr;
        }
      }

      // Check if all users of valToCheck that are also 
      // in instruction I's inSet are constants
      for (auto inst : inSet) {
        if (auto call = dyn_cast<CallInst>(inst)) {
          Function *callee = call->getCalledFunction();
          if (CATMap.contains(callee)) {
            switch (CATMap.at(callee)) {
              case CAT_new:
                if (valToCheck == inst) {
                  if (!setConstants(call->getArgOperand(0), constPtr, 
                                    constant, initialized)) {
                    return nullptr;
                  }
                }
                break;
              case CAT_add:
              case CAT_sub:
                if (valToCheck == call->getArgOperand(0)) {
                  return nullptr;
                } else if (auto select = dyn_cast<SelectInst>(
                    call->getArgOperand(0))) {
                  if (valToCheck == select->getTrueValue() 
                      || valToCheck == select->getFalseValue()) {
                    return nullptr;
                  }
                } else if (isa<LoadInst>(call->getArgOperand(0))) {
                  return nullptr;
                }
                break;
              case CAT_set:
                if (valToCheck == call->getArgOperand(0)) {
                  if (!setConstants(call->getArgOperand(1), constPtr, 
                                    constant, initialized)) {
                    return nullptr;
                  }
                } else if (auto select = dyn_cast<SelectInst>(
                    call->getArgOperand(0))) {
                  if (valToCheck == select->getTrueValue() 
                      || valToCheck == select->getFalseValue()) {
                    if (!setConstants(call->getArgOperand(1), constPtr, 
                                      constant, initialized)) {
                      return nullptr;
                    }
                  }
                } else if (isa<LoadInst>(call->getArgOperand(0))) {
                  if (!setConstants(call->getArgOperand(1), constPtr, 
                                    constant, initialized)) {
                    return nullptr;
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

    /**
     * Checks if a load instruction is a constant.
     */
    ConstantInt *isLoadConstant(LoadInst *load, set<Instruction *> inSet,
                                set<AliasValue> mptIn) {
      ConstantInt *constPtr = nullptr;
      int64_t constant;
      bool initialized;

      for (auto val : mptIn) {
        if (load == val.pointer) {
          if (auto aliasCall = dyn_cast<CallInst>(val.variable)) {
            Function *aliasCallee = aliasCall->getCalledFunction();
            if (CATMap.contains(aliasCallee)) {
              switch (CATMap.at(aliasCallee)) {
                case CAT_new:
                  if (!setConstants(aliasCall->getArgOperand(0), constPtr, 
                                    constant, initialized)) {
                    return nullptr;
                  }
                  break;
                case CAT_add:
                case CAT_sub:
                  return nullptr;
                case CAT_set:
                  if (!setConstants(aliasCall->getArgOperand(1), constPtr, 
                                    constant, initialized)) {
                    return nullptr;
                  }
                  break;
                default:
                  break;
              }
            } else {
              return nullptr;
            }
          }
        }
      }

      return constPtr;
    }

    /**
     * If a value is a constant then either initialize the constant variables 
     * or check if the value is the same as previously found constants. 
     * Return true afterwards.
     * 
     * If it is not a constant or it is different than previously 
     * found constants, then return false.
     */
    bool setConstants(Value *val, ConstantInt *&constPtr, 
                      int64_t &constant, bool &initialized) {
      if (!val) {
        constPtr = nullptr;
        return false;
      }

      if (auto constInt = dyn_cast<ConstantInt>(val)) {
        if (!initialized || constant == constInt->getSExtValue()) {
          constPtr = constInt;
          constant = constInt->getSExtValue();
          initialized = true;
          return true;
        }
      }

      constPtr = nullptr;
      return false;
    }

    /**
     * This function runs a depth-first search to check if there is a cycle 
     * when traversing phi nodes or select instructions.
     */
    bool containsCycle(Value *v) {
      vector<Value *> stack = {v};
      set<Value *> visited;

      while (!stack.empty()) {
        Value *val = stack.back();
        stack.pop_back();
        
        if (visited.contains(val)) {
          return true;
        }
        visited.insert(val);

        if (auto phi = dyn_cast<PHINode>(val)) {
          for (unsigned i = 0; i < phi->getNumIncomingValues(); i++) {
            stack.push_back(phi->getIncomingValue(i));
          }
        } else if (auto select = dyn_cast<SelectInst>(val)) {
          stack.push_back(select->getTrueValue());
          stack.push_back(select->getFalseValue());
        }
      }

      return false;
    }

    /**
     * This function iterates through the users of a variable to see if 
     * it escapes to another non-CAT function.
     */
    bool isEscaped(Value *valToCheck) {
      for (auto user : valToCheck->users()) {
        if (auto call = dyn_cast<CallInst>(user)) {
          if (!CATMap.contains(call->getCalledFunction())) {
            return true;
          }
        } else if (auto store = dyn_cast<StoreInst>(user)) {
          if (store->getValueOperand() == valToCheck) {
            return true;
          }
        }
      }
      return false;
    }

    /**
     * This function runs constant propagation on a set of CAT instruction.
     */
    bool runConstantPropagation(Module &M,
                                set<Instruction *> &CATInstructions,
                                map<Instruction *, set<Instruction *>> inSets,
                                map<Instruction *, set<AliasValue>> aliasIn) {
      bool modified = false;
      map<Instruction *, ConstantInt *> toReplace;

      for (auto I : CATInstructions) {
        if (auto call = dyn_cast<CallInst>(I)) {
          Function *callee = call->getCalledFunction();
          if (M.getFunction("CAT_get") == callee) {
            if (ConstantInt *c = isConstant(call->getArgOperand(0), inSets[I],
                                            aliasIn[I])) {
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

    /**
     * This function runs constant folding on a set of CAT instructions.
     */
    bool runConstantFolding(Module &M,
                            set<Instruction *> &CATInstructions,
                            map<Instruction *, set<Instruction *>> inSets,
                            map<Instruction *, set<AliasValue>> aliasIn) {
      bool modified = false;
      vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (auto call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);
          
          Function *callee = call->getCalledFunction();
          if (M.getFunction("CAT_add") == callee) {
            ConstantInt *const1 = isConstant(call->getArgOperand(1), 
                                             inSets[I], aliasIn[I]);
            ConstantInt *const2 = isConstant(call->getArgOperand(2), 
                                             inSets[I], aliasIn[I]);

            if (const1 && const2) {
              IntegerType *intType = IntegerType::get(M.getContext(), 64);
              Value *sum = ConstantInt::get(
                  intType, const1->getSExtValue() + const2->getSExtValue(), 
                  true);
              FunctionType *funcType = FunctionType::get(
                  Type::getVoidTy(M.getContext()),
                  {call->getArgOperand(0)->getType(), intType},
                  false);

              Instruction *newInst = builder.CreateCall(
                  M.getOrInsertFunction("CAT_set", funcType),
                  {call->getArgOperand(0), sum});
              CATInstructions.insert(newInst);

              toDelete.push_back(I);
              modified = true;

              /* if (M.getFunction("CAT_set")) {
                Instruction *newInst = builder.CreateCall(
                    M.getFunction("CAT_set"), {call->getArgOperand(0), sum});
                CATInstructions.insert(newInst);

                toDelete.push_back(I);
                modified = true;
              } */
            }
          } else if (M.getFunction("CAT_sub") == callee) {
            ConstantInt *const1 = isConstant(call->getArgOperand(1), 
                                             inSets[I], aliasIn[I]);
            ConstantInt *const2 = isConstant(call->getArgOperand(2), 
                                             inSets[I], aliasIn[I]);

            if (const1 && const2) {
              IntegerType *intType = IntegerType::get(M.getContext(), 64);
              Value *diff = ConstantInt::get(
                  intType, const1->getSExtValue() - const2->getSExtValue(), 
                  true);

              Instruction *newInst = builder.CreateCall(
                  M.getFunction("CAT_set"), {call->getArgOperand(0), diff});
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

    /**
     * This function runs algebraic simplification on a set of CAT instructions.
     */
    bool runAlgebraicSimplification(
        Module &M,
        set<Instruction *> &CATInstructions,
        map<Instruction *, set<Instruction *>> inSets,
        map<Instruction *, set<AliasValue>> aliasIn) {
      bool modified = false;
      vector<Instruction *> toDelete;

      for (auto I : CATInstructions) {
        if (auto call = dyn_cast<CallInst>(I)) {
          IRBuilder<> builder(call);

          Function *callee = call->getCalledFunction();
          if (M.getFunction("CAT_add") == callee) {
            if (ConstantInt *c = isConstant(call->getArgOperand(1), inSets[I],
                                            aliasIn[I])) {
              // If the 2nd argument is a constant = 0, then 
              // simplify to 3rd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(
                    M.getFunction("CAT_get"), {call->getArgOperand(2)});
                Instruction *newInst = builder.CreateCall(
                    M.getFunction("CAT_set"), 
                    {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);

                toDelete.push_back(I);
                modified = true;
              }
            } else if (ConstantInt *c = isConstant(call->getArgOperand(2), 
                                                   inSets[I], aliasIn[I])) {
              // If the 3rd argument is a constant = 0, then 
              // simplify to 2nd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(
                    M.getFunction("CAT_get"), {call->getArgOperand(1)});
                Instruction *newInst = builder.CreateCall(
                    M.getFunction("CAT_set"), 
                    {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);

                toDelete.push_back(I);
                modified = true;
              }
            }
          } else if (M.getFunction("CAT_sub") == callee) {
            if (ConstantInt *c = isConstant(call->getArgOperand(2), inSets[I],
                                            aliasIn[I])) {
              // If the 3rd argument is a constant = 0, then simplify to 2nd argument
              if (c->getSExtValue() == 0) {
                Instruction *catGet = builder.CreateCall(
                    M.getFunction("CAT_get"), {call->getArgOperand(1)});
                Instruction *newInst = builder.CreateCall(
                    M.getFunction("CAT_set"), 
                    {call->getArgOperand(0), catGet});
                CATInstructions.insert(catGet);
                CATInstructions.insert(newInst);
                
                toDelete.push_back(I);
                modified = true;
              }
            } else if (call->getArgOperand(1) == call->getArgOperand(2)) {
              // If 2nd and 3rd arguments are the same variable, then 
              // simplify result to 0
              Value *zeroConst = ConstantInt::get(
                  IntegerType::get(M.getContext(), 64), 0, true);
              Instruction *newInst = builder.CreateCall(
                  M.getFunction("CAT_set"), 
                  {call->getArgOperand(0), zeroConst});
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

    /**
     * This function prints the definitions of a variable for debugging.
     */
    void printDefTable(Function &F, 
                       map<Instruction *, set<Instruction *>> defTable) {
      for (auto [def, insts] : defTable) {
        for (auto inst : insts) {
          errs() << F.getName() << *def << *inst << "\n";
        }
      }
    }

    /**
     * This function prints the reaching definitions of a function F for debugging.
     */
    void printReachingDefs(Function &F,
                           map<Instruction *, set<Instruction *>> inSets, 
                           map<Instruction *, set<Instruction *>> outSets) {
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

    /**
     * This function prints the alias analysis of a function F for debugging.
     */
    void printAliasSets(Function &F,
                        map<Instruction *, set<AliasValue>> aliasIn, 
                        map<Instruction *, set<AliasValue>> aliasOut) {
      errs() << "Function \"" << F.getName() << "\"\n";
      for (auto &I : instructions(F)) {
        errs() << "INSTRUCTION:" << I << "\nIN\n{\n";
        for (auto in : aliasIn[&I]) {
          errs() << *(in.pointer) << *(in.variable) << "\n";
        }
        errs() << "}\nOUT\n{\n";
        for (auto out : aliasOut[&I]) {
          errs() << *(out.pointer) << *(out.variable) << "\n";
        }
        errs() << "}\n";
      }
    }

    /**
     * This function prints the may point to sets of a function F for debugging.
     */
    void printMayPointTo(Function &F, 
                         map<Instruction *, set<Instruction *>> mayPointTo) {
      Value *val1;
      Value *val2;
      for (auto [inst, pointsTo] : mayPointTo) {
        if (auto store1 = dyn_cast<StoreInst>(inst)) {
          val1 = store1->getValueOperand();
        } else {
          val1 = inst;
        }
        
        for (auto point : pointsTo) {
          if (auto store2 = dyn_cast<StoreInst>(point)) {
            val2 = store2->getValueOperand();
          } else {
            val2 = point;
          }
          errs() << F.getName() << *val1 << *val2 << "\n";
        }
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
