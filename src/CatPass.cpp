#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <map>
#include <set>

using namespace llvm;

namespace {
  struct CAT : public FunctionPass {
    static char ID; 

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      // errs() << "Hello LLVM World at \"doInitialization\"\n" ;
      return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {
      errs() << "Function \"" << F.getName() << "\"\n";

      std::map<Instruction *, std::set<Instruction *>> gen;
      std::map<Instruction *, std::set<Instruction *>> kill;

      for (auto &inst : instructions(F)) {
        gen[&inst] = std::set<Instruction*>();
        kill[&inst] = std::set<Instruction*>();

        if (CallInst *callInst = dyn_cast<CallInst>(&inst)) {
          Function *callee = callInst->getCalledFunction();
          if (callee->getName() == "CAT_new") {
            gen[&inst].insert(&inst);
          }
        }
      }

      for (auto &inst : instructions(F)) {
        if (CallInst *callInst = dyn_cast<CallInst>(&inst)) {
          Function *callee = callInst->getCalledFunction();
          if (callee->getName() == "CAT_add" || callee->getName() == "CAT_sub" || callee->getName() == "CAT_set") {
            gen[&inst].insert(&inst);

            Instruction *arg = cast<Instruction>(callInst->getArgOperand(0));
            kill[&inst].insert(arg);
            kill[&inst].insert(kill[arg].begin(), kill[arg].end());

            for (auto &killInst : kill[&inst]) {
              kill[killInst].insert(&inst);
            }
          }
        }
      }

      std::map<Instruction *, std::set<Instruction *>> in;
      std::map<Instruction *, std::set<Instruction *>> out;

      for (auto &inst : instructions(F)) {
        in[&inst] = std::set<Instruction *>();
        out[&inst] = std::set<Instruction *>();
      }

      bool done;
      do {
        done = true;

        for (auto &bb : F) {
          for (auto &inst : bb) {
            Instruction *prev = inst.getPrevNode();
            if (!prev) {
              for (auto pred : predecessors(&bb)) {
                in[&inst].insert(out[pred->getTerminator()].begin(), out[pred->getTerminator()].end());
              }
            } else {
              in[&inst].insert(out[prev].begin(), out[prev].end());
            }

            std::set<Instruction *> tempOut = {};

            for (auto &inInst : in[&inst]) {
              if (!kill[&inst].contains(inInst)) {
                tempOut.insert(inInst);
              }
            }
            tempOut.insert(gen[&inst].begin(), gen[&inst].end());

            done = done && (out[&inst] == tempOut);
            out[&inst] = tempOut;
          }
        }
      } while (!done);

      for (auto &inst : instructions(F)) {
        errs() << "INSTRUCTION:" << inst << "\nIN\n{\n";
        for (auto &inInst : in[&inst]) {
          errs() << *inInst << "\n";
        }
        errs() << "}\nOUT\n{\n";
        for (auto &outInst : out[&inst]) {
          errs() << *outInst << "\n";
        }
        errs() << "}\n";
      }
      return false;
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
