//===- LoopDeletion.cpp - Dead Loop Deletion Pass ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the Dead Loop Deletion Pass. This pass is responsible
// for eliminating loops with non-infinite computable trip counts that have no
// side effects or volatile instructions, and do not contribute to the
// computation of the function's return value.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Scalar/LoopDeletion.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"


#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/ScalarEvolution.h"

using namespace llvm;

namespace {
class BoundsCheckLoopPass : public LoopPass {
public:
  static char ID; // Pass ID, replacement for typeid
  BoundsCheckLoopPass() : LoopPass(ID) {
    initializeBoundsCheckLoopPassPass(*PassRegistry::getPassRegistry());
  }


    Value* getLoopVariable(Loop * L){
      auto* BB = L->getHeader();
      auto it = BB->begin();
      ++it;
      ++it;
      auto& inst = *it;
      auto* load = dyn_cast<LoadInst>(&inst);
      auto* local1 = load->getOperand(0);
      return local1;
    }

    BranchInst *getPHBranch(BasicBlock *pBlock){
      Instruction* last_inst = nullptr;
      for(auto& inst : *pBlock){
        last_inst = &inst;
      }
      return dyn_cast<BranchInst>(last_inst);
    }
    bool runOnLoop(Loop *L, LPPassManager &LPM) override {
      auto* PH = L->getLoopPreheader();
      if(!PH->getParent()->getName().equals("wasmer_function__5")){
        return false;
      }
      auto* B = L->getHeader(); // TODO: get BB with Bounds Check
      auto& vst = B->getModule()->getValueSymbolTable();
      ValueToValueMapTy VMap;
      auto* BBDash = CloneBasicBlock(B, VMap, "_bounds_check", B->getParent());
      VMap[B] = BBDash;
      for(auto& Inst : *BBDash){
        RemapInstruction(&Inst, VMap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
      }

      auto* indexVar = getLoopVariable(L);
      int maxValue = 200000000; // TODO: get Loop Max value
      bool found = false;
      for(auto& inst : *BBDash){
        if(found){
          // inst.dump();
        }
        for(int i = 0; i < inst.getNumOperands(); ++i){
          auto* operand = inst.getOperand(i);
          if(operand == indexVar){
            auto maxV = ConstantInt::get(inst.getType(), maxValue, false);
            inst.replaceAllUsesWith(maxV);
            found = true;
            inst.dump();
          }
        }
      }
      auto* branch = getPHBranch(PH);
      branch->setSuccessor(0, BBDash);
      auto* branchBBDash = getPHBranch(BBDash);
      branchBBDash->setSuccessor(0, B);

      for(auto&Instruction : *B) {
        if (Instruction.getMetadata(10) != nullptr) {
          if (auto *StringMetaData = dyn_cast<MDString>(
                  Instruction.getMetadata(10)->getOperand(0).get())) {
            if (StringMetaData->getString().equals("wasmer_bounds_check")) {
              // Found memory access with bounds check

              /* assume ptr_in_bounds_expect == true */
              auto *Prev = Instruction.getPrevNode();
              while (!dyn_cast<ICmpInst>(Prev)) {
                Prev = Prev->getPrevNode();
              }
              // Cmp Instruction for bounds check
              auto *ICMPInst = dyn_cast<ICmpInst>(Prev);
              assumeCMPIsTrue(ICMPInst);
            }
          }
        }
      }
      BBDash->moveAfter(PH);

      return true;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.addRequired<ScalarEvolutionWrapperPass>();
      AU.addRequired<AssumptionCacheTracker>();
      AU.addPreserved<AssumptionCacheTracker>();
      getLoopAnalysisUsage(AU);
    }

  private:
    void assumeCMPIsTrue(ICmpInst* ICMPInst){
      Function *AssumeIntrinsic = Intrinsic::getDeclaration(
          ICMPInst->getModule(), Intrinsic::assume);
      CallInst *CI = CallInst::Create(AssumeIntrinsic, {ICMPInst});
      CI->insertAfter(ICMPInst);
      AssumptionCache AC = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(*ICMPInst->getFunction());
      AC.registerAssumption(CI);
    }

  };
}

char BoundsCheckLoopPass::ID = 0;
INITIALIZE_PASS_BEGIN(BoundsCheckLoopPass, "bounds-check-loop",
                      "Delete dead loops", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopPass)
INITIALIZE_PASS_DEPENDENCY(AssumptionCacheTracker)
INITIALIZE_PASS_END(BoundsCheckLoopPass, "bounds-check-loop",
                    "Delete dead loops", false, false)

Pass *llvm::createBoundsCheckLoop() { return new BoundsCheckLoopPass(); }