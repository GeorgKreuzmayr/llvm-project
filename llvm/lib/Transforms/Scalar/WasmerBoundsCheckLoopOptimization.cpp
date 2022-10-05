//===- WasmerBoundsCheckLoopOptimization.cpp - Bounds Check Optimization --===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the Wasmer Bounds Check Loop Optimization.
// The optimization extracts one loop iteration to the pre loop header
// and replaces the bounds check of the current index with its maximum value
// if this check succeeds, the further loop iterations are done without a
// bounds check
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/WasmerPass.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/WasmerPass.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"


#include <iostream>
#include <optional>
#include <unordered_set>

using namespace llvm;

namespace {
class WasmerBoundsCheckLoopOptimization : public LoopPass {
public:
  static char ID; // Pass ID, replacement for typeid
  WasmerBoundsCheckLoopOptimization() : LoopPass(ID) {
    initializeWasmerBoundsCheckLoopOptimizationPass(
        *PassRegistry::getPassRegistry());
  }
  void cloneInstructionsToBCBlock(ValueToValueMapTy& VMap, std::vector<Instruction*>& BCInstructions, Instruction* InductionVariable, Value* Max, BasicBlock* BCBlock){
    for(auto InstIt = BCInstructions.rbegin(); InstIt != BCInstructions.rend(); ++InstIt){
      auto* Inst = *InstIt;
      auto* ClonedInst = Inst->clone();
      VMap[Inst] = ClonedInst;
      for(size_t OpIdx = 0; OpIdx < ClonedInst->getNumOperands(); ++OpIdx){
        if(ClonedInst->getOperand(OpIdx) == InductionVariable){
          ClonedInst->setOperand(OpIdx, Max);
        }else{
          auto ClonedOp = VMap[ClonedInst->getOperand(OpIdx)];
          if(ClonedOp.pointsToAliveValue()){
            ClonedInst->setOperand(OpIdx, dyn_cast<Value>(&*ClonedOp));
          }
        }
      }
      BCBlock->getInstList().push_back(ClonedInst);
    }
  }

  /*
   * This function clones all Instructions that are used to perform a bounds
   * check for one memory access and adds them to the pre loop header.
   */
  std::vector<Instruction*> extractBcInstructions(BranchInst*BoundsCheckBranch, Loop* L, Instruction* InductionVariable){
        if(!BoundsCheckBranch->getPrevNode()){
      return {};
    }
	if (auto *BCCompare = dyn_cast<ICmpInst>(BoundsCheckBranch->getPrevNode())) {
      std::vector<Instruction *> InstructionsUsedForBC;
      InstructionsUsedForBC.push_back(BCCompare);

      // Collect all non loop invariant instructions to calculate bounds
      // check
      size_t MaxIdx = 1;
      for (size_t CopyStartIdx = 0; CopyStartIdx != MaxIdx;
           ++CopyStartIdx) {
        auto *Next = InstructionsUsedForBC.at(CopyStartIdx);
        for (size_t OpIdx = 0; OpIdx < Next->getNumOperands(); ++OpIdx) {
          auto *Operand = Next->getOperand(OpIdx);
          if (L->isLoopInvariant(Operand)) {
          } else if (auto *OpInst = dyn_cast<Instruction>(Operand)) {
            for (auto *OpUser : OpInst->users()) {
              if (isa<GEPOperator>(OpUser)) {
                // TODO: Improve this annotation
                dyn_cast<Instruction>(Operand)->addAnnotationMetadata(
                    MemoryAccessIndex);
                dyn_cast<Instruction>(OpUser)->addAnnotationMetadata(
                    GEPMemoryAccess);
              }
            }
            if(isa<PHINode>(OpInst)){
              if(OpInst != InductionVariable){
                return {};
              }
            } else {
              InstructionsUsedForBC.push_back(OpInst);
              ++MaxIdx;
            }
          } else {
            std::cerr << "This is unexpected, found a: ";
            assert(false);
          }
        }
      }
      return InstructionsUsedForBC;
    }
    return {};
  }

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    std::cerr << L->getBlocks().front()->getParent()->getName().data() << std::endl;
    ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    auto LB = L->getBounds(SE);
    auto* InductionVariable = L->getInductionVariable(SE);
    if(!InductionVariable){
      return false;
    }
    InductionVariable->addAnnotationMetadata(InductionVariableAnno);
    Value *Max = nullptr;
    if (LB) {
        std::cerr << "Max: ";
        if (LB.getValue().getDirection() ==
            Loop::LoopBounds::Direction::Increasing) {
          Max = &LB.getValue().getFinalIVValue();
          std::cerr << "Min: ";
        } else {
          Max = &LB.getValue().getInitialIVValue();
          std::cerr << "Min: ";
        }
        std::cerr << "IV: ";
      }

    if(!Max){
      return false;
    }

    ValueToValueMapTy VMap;
    BasicBlock*LastPreLoopBlock = L->getLoopPreheader();
    BasicBlock* FirstLoopBlock = L->getBlocks().front();
    if(!LastPreLoopBlock){
      std::cerr << "Failed to find Loop Pre Header" << std::endl;
    }
    std::unordered_set<BasicBlock*> LoopBlocks;

    for (auto* BB : L->getBlocks()){
      LoopBlocks.insert(BB);
    }

    for (auto *BB : L->getBlocks()) {
      auto*OGTerminator = BB->getTerminator();
      assert(OGTerminator);
      if (isAnnotated(OGTerminator, WasmerBoundsCheck)) {
        // Try to extract Bounds Check
        auto*BoundsCheckBranch = dyn_cast<BranchInst>(OGTerminator);
        assert(BoundsCheckBranch);
        auto BCInstr = extractBcInstructions(BoundsCheckBranch, L, InductionVariable);
        if(!BCInstr.empty()){
          std::cerr << "Identified BC Instructions successfully" << std::endl;
          auto* BCBlock = SplitEdge(LastPreLoopBlock, FirstLoopBlock);
          if(!BCBlock){
            continue;
          }
          assert(BCBlock->getInstList().size() == 1);
          LastPreLoopBlock = BCBlock;
          cloneInstructionsToBCBlock(VMap, BCInstr, InductionVariable, Max, BCBlock);
          assert(isa<ICmpInst>(&BCBlock->getInstList().back()));
          auto* TrueBranch = BoundsCheckBranch->getSuccessor(0);
          auto* FalseBranch = BoundsCheckBranch->getSuccessor(1);
          BasicBlock* InLoopContinue = nullptr;
          if(FalseBranch->getName().startswith("not_in_bounds_block")){
            InLoopContinue = TrueBranch;
            TrueBranch = FirstLoopBlock;
          }else{
            assert(TrueBranch->getName().startswith("not_in_bounds_block"));
            InLoopContinue = FalseBranch;
            FalseBranch = FirstLoopBlock;
          }
          auto* PreLoopBranch = BranchInst::Create(TrueBranch, FalseBranch, &BCBlock->getInstList().back(), BCBlock);
          PreLoopBranch->addAnnotationMetadata(WasmerBoundsCheck);
          assert(isa<BranchInst>(&BCBlock->getInstList().front()));
          // Remove Branch inserted by SplitEdge
          auto* RemBr = &BCBlock->getInstList().front();
          RemBr->removeFromParent();
          RemBr->deleteValue();

          // Remove Conditional Branch inside Loop:
          OGTerminator->removeFromParent();
          OGTerminator->deleteValue();
          BranchInst::Create(InLoopContinue, BB);

          auto* Par = L->getParentLoop();
          if(Par){
            Par->addBasicBlockToLoop(BCBlock, LI);
          }

          std::cerr << "SUCCESSFUL EXTRACTION IN: " << BB->getParent()->getName().data() << std::endl;
        }
      }
    }
    std::cerr << "END OF LOOOOOOPPP PASS " << std::endl;
    return true;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AssumptionCacheTracker>();
    AU.addRequired<LoopInfoWrapperPass>();
    getLoopAnalysisUsage(AU);
  }
};
} // namespace

char WasmerBoundsCheckLoopOptimization::ID = 0;
INITIALIZE_PASS_BEGIN(WasmerBoundsCheckLoopOptimization, "bounds-check-loop",
                      "Delete dead loops", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopPass)
INITIALIZE_PASS_END(WasmerBoundsCheckLoopOptimization, "bounds-check-loop",
                    "Delete dead loops", false, false)

Pass *llvm::createWasmerBoundsCheckLoopOptimization() {
  return new WasmerBoundsCheckLoopOptimization();
}
