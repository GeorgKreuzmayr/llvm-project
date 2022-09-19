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

#include <iostream>
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

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {

    // Only optimize most outer loop
    if (L->getLoopDepth() != 1) {
      return false;
    }
    ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto lb = L->getBounds(SE);
    auto InductionVariable = L->getInductionVariable(SE);
    if(!InductionVariable){
      return false;
    }
    InductionVariable->addAnnotationMetadata(InductionVariableAnno);
    Value *Max = nullptr;
    if (lb) {
      if (isa<ConstantInt>(&lb.getValue().getInitialIVValue()) &&
          isa<ConstantInt>(&lb.getValue().getFinalIVValue())) {
        std::cerr << "Max: ";
        if (lb.getValue().getDirection() ==
            Loop::LoopBounds::Direction::Increasing) {
          Max = &lb.getValue().getFinalIVValue();
          std::cerr << "Min: ";
        } else {
          Max = &lb.getValue().getInitialIVValue();
          std::cerr << "Min: ";
        }
        std::cerr << "IV: ";
      }

    } else {
      return false;
    }

    if(!Max){
      return false;
    }

    std::unordered_set<Instruction *> NonLoopInvariantLocalVariables;
    ValueToValueMapTy VMap;

    bool FoundMemAcc = false;

    // Analyze Loop
    for (auto *BB : L->getBlocks()) {
      auto &LastInst = BB->getInstList().back();
      if (isAnnotated(&LastInst, WasmerBoundsCheck)) {
        FoundMemAcc = true;
        if (auto *BCCompare = dyn_cast<ICmpInst>(LastInst.getPrevNode())) {
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
                    return false;
                  }
                  std::cerr << "Found induction use" << std::endl;

                } else {
                  OpInst->addAnnotationMetadata(NonLoopIV);
                  InstructionsUsedForBC.push_back(OpInst);
                  ++MaxIdx;
                }
              } else {
                std::cerr << "This is unexpected, found a: ";
                assert(false);
              }
            }
          }
        }
      }
    }
    if(!FoundMemAcc){
      return false;
    }

    auto UnrollRes = unrollOneLoopIteration(L, VMap);
    if(!UnrollRes.HeaderEnd || !UnrollRes.HeaderStart){
      return false;
    }

    std::cerr << std::endl << std::endl << std::endl << std::endl;
    // Manipulate Loop
    for (auto *BB = UnrollRes.HeaderStart; BB != UnrollRes.HeaderEnd;
         BB = BB->getNextNode()) {
      for (auto &Inst : BB->getInstList()) {
        if (isAnnotated(&Inst, MemoryAccessIndex)) {
          std::vector<Instruction *> BCInstructions;
          BCInstructions.push_back(&Inst);

          // Collect all non loop invariant instructions to calculate bounds
          // check
          size_t MaxIdx = 1;
          for (size_t CopyStartIdx = 0; CopyStartIdx != MaxIdx;
               ++CopyStartIdx) {
            auto *Next = BCInstructions.at(CopyStartIdx);
            for (size_t OpIdx = 0; OpIdx < Next->getNumOperands(); ++OpIdx) {
              auto *Operand = Next->getOperand(OpIdx);
              if (auto *OpInst = dyn_cast<Instruction>(Operand)) {
                if (OpInst == InductionVariable) {

                } else if (isAnnotated(OpInst, NonLoopIV)) {
                  BCInstructions.push_back(OpInst);
                  ++MaxIdx;
                }
              }
            }
          }

          std::cerr << "Iterate over BC inst" << std::endl;
          for (auto RevIt = BCInstructions.rbegin();
               RevIt != BCInstructions.rend(); ++RevIt) {
            auto *Instr = *RevIt;
            auto *ClonedInst = Instr->clone();
            ClonedInst->insertAfter(Instr);
            VMap[Instr] = ClonedInst;
            for (size_t OpIdx = 0; OpIdx < ClonedInst->getNumOperands();
                 ++OpIdx) {
              auto *Operand = ClonedInst->getOperand(OpIdx);
              if (isa<Instruction>(Operand)) {
                if (isAnnotated(dyn_cast<Instruction>(Operand),
                                InductionVariableAnno)) {
                  ClonedInst->setOperand(OpIdx, Max);
                } else {
                  auto VRes = VMap[Operand];
                  if (VRes.pointsToAliveValue()) {
                    if (auto *ClonedOperand = dyn_cast<Instruction>(&*VRes)) {
                      ClonedInst->setOperand(OpIdx, ClonedOperand);
                    }
                  }
                }
              }
            }
          }

          // Replace usage of index in BC
          assert(isAnnotated(BCInstructions.front(), MemoryAccessIndex));
          auto *MemAccIdx = BCInstructions.front();
          auto *ClonedMemAccIdx = dyn_cast<Instruction>(&(*VMap[MemAccIdx]));
          for (auto *User : BCInstructions.front()->users()) {
            if (!isa<GEPOperator>(User)) {
              if (auto *Instr = dyn_cast<Instruction>(User)) {
                for (size_t OpIdx = 0; OpIdx < Instr->getNumOperands();
                     ++OpIdx) {
                  if (dyn_cast<Instruction>(Instr->getOperand(OpIdx)) ==
                      MemAccIdx) {
                    Instr->setOperand(OpIdx, ClonedMemAccIdx);
                  }
                }
              }
            }
          }

          dyn_cast<BasicBlock>(&*VMap[BB])->getInstList().back().addAnnotationMetadata(RemoveBC);
          break;
        }
      }
    }



    // Assume index is in bounds
    for(auto* BB : L->getBlocks()){
      if(isAnnotated(&BB->getInstList().back(), RemoveBC)){
        if(auto* Branch = dyn_cast<BranchInst>(&BB->getInstList().back())){
          Branch->setCondition(ConstantInt::getFalse(Branch->getCondition()->getContext()));
        }
      }
    }
    std::cerr << "SUCCESSFULL BOUND EXTRACTION for:" << L->getBlocks().front()->getParent()->getName().data() << std::endl;
    return true;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AssumptionCacheTracker>();
    getLoopAnalysisUsage(AU);
  }

private:
  struct LoopBounds {
    Value *IndexPointer;
    Value *MaxIndexValue;
  };

  struct LoopUnrollReturn {
    BasicBlock *HeaderStart;
    BasicBlock *HeaderEnd;
  };

  // Find value that is stored to the index value in the preheader
  // This is the maximum value if the loop index is decremented
  ConstantInt *findStoreToIdxInPreHeader(Loop *L, AllocaInst *Index) {
    auto *BB = L->getLoopPreheader();
    for (auto &Instruction : *BB) {
      if (auto *Store = dyn_cast<StoreInst>(&Instruction)) {
        // Check if value stored to Index
        if (Store->getOperand(1) == Index) {
          if (auto *MaxIdx = dyn_cast<ConstantInt>(Store->getOperand(0))) {
            // Add value size to MaxIdx
            // TODO: Only do this, if the index is used for mem access
            return MaxIdx;
          }
        }
      }
    }
    return nullptr;
  }

  // Copy all BasicBlocks from Loop to PreHeader
  LoopUnrollReturn unrollOneLoopIteration(Loop *L, ValueToValueMapTy &VMap) {
    auto *LoopPreHeaderBlock = L->getLoopPreheader();
    VMap[LoopPreHeaderBlock] = LoopPreHeaderBlock;
    // Require initial loop to have preheader
    assert(LoopPreHeaderBlock);
    auto *LastPreLoopBlock = LoopPreHeaderBlock;
    // First loop block
    auto *FirstLoopBlock = L->getHeader();

    for(auto* BB : L->getBlocks()){
      if(!dyn_cast<BranchInst>(&BB->getInstList().back())){
        return {nullptr, nullptr};
      }
    }

    // TODO: Ask Moritz: std::vector reserve?
    std::vector<BasicBlock *> ClonedBlocks;
    // Extract one Loop iteration
    for (auto *BB : L->getBlocks()) {
      auto *LastInstruction = &BB->getInstList().back();
      auto *Branch = dyn_cast<BranchInst>(LastInstruction);
      assert(Branch);
      auto *BBDash =
          CloneBasicBlock(BB, VMap, "_bounds_check", BB->getParent());
      // TODO: Ask Moritz: Is this allowed? (mapped in both directions)
      VMap[BBDash] = BB;
      VMap[BB] = BBDash;
      for (auto &Inst : *BBDash) {
        RemapInstruction(&Inst, VMap,
                         RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
      }
      ClonedBlocks.push_back(BBDash);
    }

    // Insert cloned blocks after pre header
    auto *ClonedFirstLoopBlock = dyn_cast<BasicBlock>(&*VMap[FirstLoopBlock]);
    auto *PreHeaderBranch =
        dyn_cast<BranchInst>(&LoopPreHeaderBlock->getInstList().back());
    assert(PreHeaderBranch);
    for (size_t SuccIdx = 0; SuccIdx < PreHeaderBranch->getNumSuccessors();
         ++SuccIdx) {
      // Branch from Pre Header to cloned first loop block
      if (PreHeaderBranch->getSuccessor(SuccIdx) == FirstLoopBlock) {
        PreHeaderBranch->setSuccessor(SuccIdx, ClonedFirstLoopBlock);
      }
    }

    // Remap all branch of cloned blocks
    for (size_t Idx = 0; Idx < ClonedBlocks.size(); ++Idx) {
      auto *ClonedBlock = ClonedBlocks.at(Idx);
      // Insert all cloned loop blocks before actual loop
      ClonedBlock->moveAfter(LastPreLoopBlock);
      auto *LastInstruction = &ClonedBlock->getInstList().back();
      auto *Branch = dyn_cast<BranchInst>(LastInstruction);
      assert(Branch);
      for (size_t SuccIdx = 0; SuccIdx < Branch->getNumSuccessors();
           ++SuccIdx) {
        auto *OldSucc = Branch->getSuccessor(SuccIdx);
        auto NewSuccIt = VMap[OldSucc];
        if (NewSuccIt.pointsToAliveValue()) {
          Branch->setSuccessor(SuccIdx, dyn_cast<BasicBlock>(&*NewSuccIt));
        }else{
          if(auto* OldSuccPhi = dyn_cast<PHINode>(&OldSucc->getInstList().front())){
            // TODO: This is super HIGH RISK!!!!
            for(size_t IdxOSP = 0; IdxOSP < OldSuccPhi->getNumIncomingValues(); ++IdxOSP){
              auto* OgBlock = dyn_cast<BasicBlock>(&*VMap[ClonedBlock]);
              if(OldSuccPhi->getIncomingBlock(IdxOSP) == OgBlock){
                auto* OgValueForPhi = OldSuccPhi->getIncomingValue(IdxOSP);
                auto ProbCopyOgValueForPhi = VMap[OgValueForPhi];
                if(ProbCopyOgValueForPhi.pointsToAliveValue()){
                  OldSuccPhi->addIncoming(dyn_cast<Value>(&*ProbCopyOgValueForPhi), ClonedBlock);
                }else{
                  OldSuccPhi->addIncoming(OgValueForPhi, ClonedBlock);
                }
              }
            }
          }
        }
      }
      LastPreLoopBlock = ClonedBlock;
    }

    // Branch from last cloned block to first loop block
    auto *LastClonedBlockBranch =
        dyn_cast<BranchInst>(&LastPreLoopBlock->getInstList().back());
    for (size_t SuccIdx = 0;
         SuccIdx < LastClonedBlockBranch->getNumSuccessors(); ++SuccIdx) {
      if (LastClonedBlockBranch->getSuccessor(SuccIdx) ==
          ClonedFirstLoopBlock) {
        LastClonedBlockBranch->setSuccessor(SuccIdx, FirstLoopBlock);
      }
    }

    for(auto& Inst: FirstLoopBlock->getInstList()) {
      if (auto *PhiNode = dyn_cast<PHINode>(&Inst)) {
        for (size_t OpIdx = 0; OpIdx < PhiNode->getNumIncomingValues();
             ++OpIdx) {
          auto *OldIncomingBlock = PhiNode->getIncomingBlock(OpIdx);
          if (OldIncomingBlock == LoopPreHeaderBlock) {
            PhiNode->setIncomingBlock(OpIdx, LastPreLoopBlock);
          }
        }
      } else {
        break;
      }
    }


    for (auto *ClonedBlock : ClonedBlocks) {
      if (auto *FirstInstruction =
              dyn_cast<PHINode>(&ClonedBlock->getInstList().front())) {
        std::vector<size_t> ToDelIdx;
        for (size_t OpIdx = 0; OpIdx < FirstInstruction->getNumIncomingValues();
             ++OpIdx) {
          auto *OldIncomingBlock = FirstInstruction->getIncomingBlock(OpIdx);
          auto *NewIncomingBlock =
              dyn_cast<BasicBlock>(&*VMap[OldIncomingBlock]);
          bool replacedPre = false;
          for (auto *PreDec : predecessors(ClonedBlock)) {
            if (PreDec == NewIncomingBlock) {
              replacedPre = true;
              FirstInstruction->setIncomingBlock(OpIdx, NewIncomingBlock);
            }
          }
          if (!replacedPre) {
            ToDelIdx.emplace(ToDelIdx.begin(), OpIdx);
          }
        }
        for (auto DelIdx : ToDelIdx) {
          FirstInstruction->removeIncomingValue(DelIdx);
        }
        auto *OgBlock = dyn_cast<BasicBlock>(&*VMap[ClonedBlock]);
      }
    }
    return {LoopPreHeaderBlock, LastPreLoopBlock};
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