//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "hello"
#include "llvm/ADT/Statistic.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/Constants.h"
#include "llvm/ValueSymbolTable.h"
#include "llvm/ADT/ValueMap.h"
#include "llvm/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/LLVMContext.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Type.h"

#include <map>
#include <vector>
using namespace llvm;

// Create a map of maps that contain information about statically
// allocated arrays and their values. Example usage:
// GlobalArrayInfo[array name][array allocation] gives a vector
// containing the array values
void BuildArrayInfo(
    std::map<StringRef, std::map<Value *, std::vector<int> > > *GlobalArrayInfo,
    iplist<GlobalVariable> *gvl) {

  // Iterate through all Global variables
  for (iplist<GlobalVariable>::iterator it = gvl->begin(); it != gvl->end();
       it++) {
    // If the variable is initialized (user created)
    if (it->hasInitializer()) {
      // If the variable is an array
      if (it->getInitializer()->getType()->isArrayTy()) {
        // If the array is not a special array created for internal
        // LLVM use
        if (isa<ConstantAggregateZero>(it->getInitializer()) == false) {
          // If the array contains integers
          if (it->getInitializer()->getOperand(0)->getType()->isIntegerTy()) {

            // Get the number of elements the array contains
            int arrayElements = dyn_cast<ArrayType>(
                it->getInitializer()->getType())->getNumElements();
            // Get the array's name
            StringRef arrayName = it->getName();
            // Check to see if an entry already exits in GlobalArrayInfo
            std::map<StringRef, std::map<Value *, std::vector<int> > >::iterator
            findArray = GlobalArrayInfo->find(arrayName);
            // If no entry has been created
            if (findArray == GlobalArrayInfo->end()) {
              // Get the pointer to array
              Value *arrayPtr;
              arrayPtr = it->getInitializer()->getOperand(0);
              // Create an entry for the array where the key
              // is the array name and the value is an
              // empty map
              GlobalArrayInfo->insert(std::make_pair(
                  arrayName, std::map<Value *, std::vector<int> >()));
              (*GlobalArrayInfo)[arrayName]
                  .insert(make_pair(arrayPtr, std::vector<int>()));
              (*GlobalArrayInfo)[arrayName][arrayPtr].push_back(0);
            }

            Value *val;

            // Walk through all the elements in the array, storing
            // each statically assigned value of the array in a
            // vector
            for (int i = 0; i < arrayElements; i++) {
              val = it->getInitializer()->getOperand(i);
              std::map<Value *, std::vector<int> >::iterator findval =
                  (*GlobalArrayInfo)[arrayName].find(val);
              if (findval != (*GlobalArrayInfo)[arrayName].end()) {
                (*GlobalArrayInfo)[arrayName][val].push_back(i);
              } else {
                (*GlobalArrayInfo)[arrayName]
                    .insert(std::make_pair(val, std::vector<int>()));
                (*GlobalArrayInfo)[arrayName][val].push_back(i);
              }
            }
          }
        }
      }
    }
  }
}

// Create the BB block structure that will later be used by switch statements
void BuildGEPBlocks(
    Module *M,
    std::map<StringRef, std::map<Value *, std::vector<int> > > *GlobalArrayInfo,
    std::vector<GetElementPtrInst *> *relGeps) {

  // First split of a GEP has not occurred
  bool splitBasicBlock = false;

  // For each function
  iplist<Function> &fl = M->getFunctionList();
  for (iplist<Function>::iterator it = fl.begin(); it != fl.end(); it++) {
    // For each BB
    iplist<BasicBlock> &bb = it->getBasicBlockList();
    for (iplist<BasicBlock>::iterator bb_it = bb.begin(); bb_it != bb.end();
         bb_it++) {
      // For each Instruction
      iplist<Instruction> &inst = bb_it->getInstList();
      for (iplist<Instruction>::iterator inst_it = inst.begin();
           inst_it != inst.end(); inst_it++) {
        // If the intruction is a gep (essentially calculates the
        // pointer that corresponds to a specific array access)
        if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(inst_it)) {
          // If accessing a user created variable or array
          if (gep->getPointerOperand()->hasName()) {
            std::map<StringRef, std::map<Value *, std::vector<int> > >::iterator
            findArrayName =
                GlobalArrayInfo->find(gep->getPointerOperand()->getName());

            // If the GEP is targeting a statically allocated array
            if (findArrayName != GlobalArrayInfo->end()) {
              // Split BB's at location of gep (used later
              // when creating switch cases)
              if (!splitBasicBlock) {
                // Store the gep we will later replace
                relGeps->push_back(gep);
                SplitBlock(bb_it, gep, this);
                inst_it = inst.end();
                inst_it--;
                splitBasicBlock = true;
              } else {

                BasicBlock *postGepBlock = SplitBlock(bb_it, ++inst_it, this);
                BasicBlock *DefaultBlock =
                    BasicBlock::Create(gep->getContext(), "defblock",
                                       bb_it->getParent(), postGepBlock);
                BranchInst *jumpToLoadBlock =
                    BranchInst::Create(postGepBlock, DefaultBlock);
                inst_it = inst.end();
                inst_it--;
                splitBasicBlock = false;
              }
            }
          }
        }
      }
    }
  }
}

// For every GEP accessing applicable arrays, find all the loads that
// target them
void GetGEPLoadPair(Module *M, std::vector<GetElementPtrInst *> *relGeps) {

  iplist<Function> &fl = M->getFunctionList();

  // For each GEP that targets a statically allocated array
  for (std::vector<GetElementPtrInst *>::iterator gepIt = relGeps->begin();
       gepIt != relGeps->end(); gepIt++) {
    // For each function in the program
    for (iplist<Function>::iterator func_it = fl.begin(); func_it != fl.end();
         func_it++) {
      // For each BB in the program
      iplist<BasicBlock> &bb = func_it->getBasicBlockList();
      for (iplist<BasicBlock>::iterator bb_it = bb.begin(); bb_it != bb.end();
           bb_it++) {
        // For each instruction
        iplist<Instruction> &inst = bb_it->getInstList();
        for (iplist<Instruction>::iterator inst_it = inst.begin();
             inst_it != inst.end(); inst_it++) {
          if (inst_it) {
            // If current instruction is a load
            if (LoadInst *r = dyn_cast<LoadInst>(inst_it)) {
              // If load targets a gep that targets
              // a statically allocated array
              if (r->getOperand(0) == *gepIt) {
                // Store the gep and load pair
                GepsAndLoads.first.push_back(*gepIt);
                GepsAndLoads.second.push_back(r);
              }
            }
          }
        }
      }
    }
  }
}

// Build the switch statements the implement the accelerated array
// optimization for Symbolic Execution. For example, consider the
// array: int array[5] = {0,2,4,6,8}
// with a symbolic index read (index is computed during runtime):
// val = array[symb_idx]
//
// This creates issues during symbolic execution due to the complicated
// nature of modeling arrays in an SMT Logic. Since statically allocated
// arrays have known values this encoding is overly complex. Therefore,
// we replace the above symbolic index read with a set of instructions:
// switch (symb_idx)
// {
// 	case 0:
// 		val = 0;
// 		break;
// 	case 1:
// 		val = 2;
// 		break;
// 	case 2:
// 		val = 4;
// 		break;
// 	case 3:
// 		val = 6;
// 		break;
// 	case 4:
// 		val = 8;
// 		break;
// }
void
BuildSwitchStmts(std::pair<std::vector<GetElementPtrInst *>,
                           std::vector<LoadInst *> > *GepsAndLoads,
                 std::map<StringRef, std::map<Value *, std::vector<int> > > *
                     GlobalArrayInfo) {

  LoadInst *newli;
  AllocaInst *holder;
  StringRef sr;

  // For each GEP and Load pair
  for (int i = 0; i < GepsAndLoads.first.size(); i++) {

    // Get the array name, and see if we have
    // its info (double check that the array
    // is applicable to our optimization
    sr = GepsAndLoads.first[i]->getPointerOperand()->getName();
    std::map<StringRef, std::map<Value *, std::vector<int> > >::iterator
    findArrayName = GlobalArrayInfo.find(sr);
    if (findArrayName != GlobalArrayInfo.end()) {
      BasicBlock *ParentBB = GepsAndLoads.first[i]->getParent();
      Function *ParentFunction = ParentBB->getParent();
      iplist<BasicBlock> &parentBBlist = ParentFunction->getBasicBlockList();
      BasicBlock *defBlock;

      // Find where the default block that we created earlier is
      // for the specific GEP Load pair
      bool foundDef = false;
      for (iplist<BasicBlock>::iterator pit = parentBBlist.begin();
           pit != parentBBlist.end(); pit++) {
        if (!foundDef) {
          if (&(*pit) == &(*ParentBB)) {
            foundDef = true;
          }
        } else {
          defBlock = pit;
          break;
        }
      }

      // Get the values of the array for this specific
      // allocate
      std::map<Value *, std::vector<int> >::iterator vals =
          findArrayName->second.begin();
      // Create a new allocate of the array
      holder = new AllocaInst(GlobalArrayInfo[sr].begin()->first[0].getType(),
                              "holder", GepsAndLoads.first[i]);
      // Remove GEP from program
      GepsAndLoads.first[i]->getParent()->back().eraseFromParent();

      // Create the switch instruction that performs the replaces the
      // GEP (array memory location calculation)
      SwitchInst *si =
          SwitchInst::Create(GepsAndLoads.first[i]->getOperand(2), defBlock,
                             (unsigned)1, GepsAndLoads.first[i]->getParent());

      // For each array allocate
      for (; vals != findArrayName->second.end(); vals++) {
        if (vals->first->getType()->isIntegerTy()) {

          // For each value in the array
          for (std::vector<int>::iterator idxit = vals->second.begin();
               idxit != vals->second.end(); idxit++) {

            // Create the BB's for the switch statement
            // that store the value of the array read to
            // the proper variable based on the index
            // used to access it
            BasicBlock *newBB = BasicBlock::Create(
                defBlock->getContext(), "", defBlock->getParent(), defBlock);
            BranchInst *bi = BranchInst::Create(defBlock, newBB);

            StoreInst *strinst = new StoreInst(vals->first, holder, bi);

            Value *consInt = ConstantInt::get(
                GepsAndLoads.first[i]->getOperand(2)->getType(), *idxit);
            si->addCase(dyn_cast<ConstantInt>(consInt), newBB);
          }
        }
      }
      // Load the variable that stored the array read's result
      newli = new LoadInst(holder, "optLoad");
      newli->setAlignment(GepsAndLoads.second[i]->getAlignment());
      ReplaceInstWithInst(GepsAndLoads.second[i], newli);
    }
  }
}

STATISTIC(HelloCounter, "Counts number of functions greeted");
namespace {
// Hello - The first implementation, without getAnalysisUsage.
struct Hello : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  Hello() : ModulePass(ID) {}

  bool runOnModule(Module &M) override {

    // List of global variables in the program
    // (where statically allocated arrays are
    // stored)
    iplist<GlobalVariable> &gvl = M.getGlobalList();
    // Find GEPs that are relevant to our optimization
    std::vector<GetElementPtrInst *> relGeps;
    // Relevant GEPs and the loads in the program that
    // target them
    std::pair<std::vector<GetElementPtrInst *>, std::vector<LoadInst *> >
    GepsAndLoads;
    GepsAndLoads.first = std::vector<GetElementPtrInst *>();
    GepsAndLoads.second = std::vector<LoadInst *>();
    // Info about relevant arrays: name, allocations, and their
    // initialvalues
    std::map<StringRef, std::map<Value *, std::vector<int> > > GlobalArrayInfo;

    BuildArrayInfo(&GlobalArrayInfo, &gvl);
    BuildGEPBlocks(Module & M, &GlobalArrayInfo, &relGeps);
    GetGEPLoadPair(Module & M, std::vector<GetElementPtrInst *> & relGeps);

    return false;
  }
};
}

char Hello::ID = 0;
static RegisterPass<Hello> X("hello", "Hello World Pass");
