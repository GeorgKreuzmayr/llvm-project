//===- WasmerMemoryAccessAnalysis.cpp - Memory Access Analysis ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This analysis pass annotates the useful information concerning web assembly
// memory accesses, compiled by wasmer. Those are used in the
// WasmerBoundsCheckLoopOptimization.cpp
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/WasmerPass.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "llvm/Analysis/MemorySSA.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/WasmerPass.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <utility>

using namespace llvm;

namespace {
class WasmerMemoryAccessAnalysis : public FunctionPass {
public:
  static char ID;
  WasmerMemoryAccessAnalysis() : FunctionPass(ID) {
    initializeWasmerMemoryAccessAnalysisPass(*PassRegistry::getPassRegistry());
  }
  std::vector<Instruction *>
  extractBcInstructions(Instruction *MemoryAccessBranch, BasicBlock *BB,
                        std::unordered_map<BasicBlock *, Value *> &BCMap,
                        BasicBlock *EntryBlock) {
    if (BB == EntryBlock) {
      return {};
    }
    Instruction *MaxMem;
    if (auto *BCCompare =
            dyn_cast<ICmpInst>(MemoryAccessBranch->getPrevNode())) {
      assert(BCCompare->getNumOperands() == 2);
      auto *LeftVal = dyn_cast<Instruction>(BCCompare->getOperand(0));
      auto *RightVal = dyn_cast<Instruction>(BCCompare->getOperand(1));
      std::vector<Instruction *> InstructionsUsedForBC;

      // Start with computation inside the current basic block that is used for BC
      if (LeftVal->getParent() == BB && RightVal->getParent() == EntryBlock) {
        InstructionsUsedForBC.push_back(LeftVal);
        MaxMem = RightVal;
      } else if (LeftVal->getParent() == EntryBlock &&
                 RightVal->getParent() == BB) {
        InstructionsUsedForBC.push_back(RightVal);
        MaxMem = LeftVal;
      } else {
        return {};
      }

      // Collect all non loop invariant instructions to calculate bounds
      // check
      size_t MaxIdx = 1;
      for (size_t CopyStartIdx = 0; CopyStartIdx != MaxIdx; ++CopyStartIdx) {
        auto *Next = InstructionsUsedForBC.at(CopyStartIdx);
        for (size_t OpIdx = 0; OpIdx < Next->getNumOperands(); ++OpIdx) {
          auto *Operand = Next->getOperand(OpIdx);
          if (auto *OpInst = dyn_cast<Instruction>(Operand)) {
            if (OpInst->getParent() != BB) {
              // Skip Instructions from different BB
              if (OpInst->getParent() != EntryBlock) {
                std::cerr << "PARENT IS NOT ENTRY BLOCK" << std::endl;
                return {};
              }
              assert(OpInst->getParent() == EntryBlock);
            } else {
              for (auto *OpUser : OpInst->users()) {
                if (isa<GEPOperator>(OpUser)) {
                  // TODO: Improve this annotation
                  dyn_cast<Instruction>(Operand)->addAnnotationMetadata(
                      MemoryAccessIndex);
                  dyn_cast<Instruction>(OpUser)->addAnnotationMetadata(
                      GEPMemoryAccess);
                }
              }
              InstructionsUsedForBC.push_back(OpInst);
              ++MaxIdx;
            }
          } else if (isa<Argument>(Operand)) {
            std::cerr << "Argument: ";
            Operand->dump();
            assert(false);
          } else if (isa<Constant>(Operand)) {
            auto *Const = dyn_cast<Constant>(Operand);
            Const->getUniqueInteger().dump();
            std::cerr << "Constant: ";
            Operand->dump();
          } else {
            std::cerr << "This is unexpected, found a: ";
            Operand->dump();
            std::cerr << "Type: ";
            Operand->getType()->dump();
            assert(false);
          }
        }
      }
      auto *LastInstr = InstructionsUsedForBC.back();
      return InstructionsUsedForBC;
    }
    return {};
  }

  std::vector<Instruction *> findPotentialExtractBCs(Instruction *BCBranch) {
    std::vector<Instruction *> InstructionsUsedForBC;
    if (auto *BCCompare = dyn_cast<ICmpInst>(BCBranch->getPrevNode())) {
      assert(BCCompare->getNumOperands() == 2);
      auto *LeftVal = dyn_cast<Instruction>(BCCompare->getOperand(0));
      auto *RightVal = dyn_cast<Instruction>(BCCompare->getOperand(1));
      // Start with computation inside the current basic block that is used for BC
      if (isa<AddOperator>(LeftVal)) {
        InstructionsUsedForBC.push_back(LeftVal);
      } else if (isa<AddOperator>(RightVal)) {
        InstructionsUsedForBC.push_back(RightVal);
      } else {
        assert(false);
      }

      // Collect all non loop invariant instructions to calculate bounds
      // check
      size_t MaxIdx = 1;
      for (size_t CopyStartIdx = 0; CopyStartIdx != MaxIdx; ++CopyStartIdx) {
        auto *Next = InstructionsUsedForBC.at(CopyStartIdx);
        int NonGEPUsers = 0;
        for (auto *OpUser : Next->users()) {
          if (!isa<GEPOperator>(OpUser)) {
            ++NonGEPUsers;
          }
        }
        if (NonGEPUsers > 2) {
          return InstructionsUsedForBC;
        }
        for (size_t OpIdx = 0; OpIdx < Next->getNumOperands(); ++OpIdx) {
          auto *Operand = Next->getOperand(OpIdx);
          if (auto *OpInst = dyn_cast<Instruction>(Operand)) {
            if (isa<AddOperator>(OpInst) || isa<ZExtInst>(OpInst)) {
              InstructionsUsedForBC.push_back(OpInst);
              ++MaxIdx;
            } else {
              std::cerr << "found non add and zext instr" << std::endl;
              return {};
            }
          } else if (isa<Constant>(Operand)) {

          } else {
            assert(false);
          }
        }
      }
    }
    return {};
  }

  BasicBlock *createBCBlock(std::vector<Instruction *> Instrs, ICmpInst *Cmp,
                            ValueToValueMapTy &VMap) {
    BasicBlock *BCBlock = BasicBlock::Create(Cmp->getContext(), "",
                                             Cmp->getParent()->getParent());

    Instrs.pop_back();                   // Get rid of base value
    Instrs.emplace(Instrs.begin(), Cmp); // Add cmp to Instr
    for (auto It = Instrs.rbegin(); It != Instrs.rend(); ++It) {
      auto *Inst = *It;
      auto *ClonedInst = Inst->clone();
      VMap[Inst] = ClonedInst;
      for (size_t OpIdx = 0; OpIdx < ClonedInst->getNumOperands(); ++OpIdx) {
        auto ClonedOp = VMap[ClonedInst->getOperand(OpIdx)];
        if (ClonedOp.pointsToAliveValue()) {
          ClonedInst->setOperand(OpIdx, dyn_cast<Value>(&*ClonedOp));
        }
      }
      BCBlock->getInstList().push_back(ClonedInst);
    }
    return BCBlock;
  }

  int64_t interpretAddInstructions(std::vector<Instruction *> &Insts) {
    int64_t Sum = 0;
    for (int64_t Idx = Insts.size() - 2; Idx >= 0; --Idx) {
      auto *Next = Insts[Idx];
      if (auto *Add = dyn_cast<AddOperator>(Next)) {
        assert(Add->getOperand(0) == Insts[Idx + 1]);
        auto *Const = dyn_cast<ConstantInt>(Add->getOperand(1));
        Sum += Const->getSExtValue();
      }
    }
    return Sum;
  }

  bool runOnFunction(Function &F) override {

    auto *EntryBlock = &F.getEntryBlock();
    std::unordered_map<Instruction *, std::vector<ICmpInst *>> PotentialExtract;
    std::unordered_map<ICmpInst *, std::vector<Instruction *>> BCMap;
    std::cerr << F.getName().data() << std::endl;
    auto &Ctx = F.getContext();

    for (auto &BB : F.getBasicBlockList()) {
      for (auto &Inst : BB.getInstList()) {
        if (isAnnotated(&Inst, WasmerBoundsCheck)) {
          auto *BCCmp = dyn_cast<ICmpInst>(Inst.getPrevNode());
          auto BCInstr = findPotentialExtractBCs(&Inst);
          if (!BCInstr.empty()) {
            BCMap.emplace(BCCmp, BCInstr);
            auto *ExtractInstr = BCInstr.back();
            auto It = PotentialExtract.find(ExtractInstr);
            if (It != PotentialExtract.end()) {
              It->second.push_back(BCCmp);
            } else {
              std::vector<ICmpInst *> Vec;
              Vec.push_back(BCCmp);
              PotentialExtract.emplace(ExtractInstr, std::move(Vec));
            }
          }
        }
      }
    }

    std::unordered_map<Instruction *, std::pair<int64_t, ICmpInst *>> MaxAdd;
    for (auto PotExPair : PotentialExtract) {
      auto *ExtractInstr = PotExPair.first;
      if (PotExPair.second.size() < 3) {
        std::cerr << "Found less than 3 BCs for ";
        ExtractInstr->dump();
        continue;
      }
      std::cerr << "Potential Extraction value: ";
      ExtractInstr->dump();
      bool First = true;
      int64_t Max = 0;
      ICmpInst *MaxCmp = nullptr;
      for (auto *BCComp : PotExPair.second) {
        auto It = BCMap.find(BCComp);
        int64_t Res = interpretAddInstructions(It->second);
        if (First) {
          Max = Res;
          First = false;
          MaxCmp = BCComp;
        } else {
          if (Res > Max) {
            Max = Res;
            MaxCmp = BCComp;
          }
        }
      }
      MaxAdd.emplace(ExtractInstr, std::pair<int64_t, ICmpInst *>{Max, MaxCmp});
      std::cerr << "Max: " << Max << std::endl;
    }

    ValueToValueMapTy VMap;

    for (auto MaxPair : MaxAdd) {
      auto *ExtractInstr = MaxPair.first;
      auto ExtractBCCompPair = PotentialExtract.find(ExtractInstr);
      Instruction *SameCompTo = nullptr;
      BasicBlock *TrapBlock = nullptr;
      for (auto *BCComp : ExtractBCCompPair->second) {
        auto BCCalcPair = BCMap.find(BCComp);
        auto *CompToInst = BCComp->getOperand(0) == BCCalcPair->second.front()
                               ? dyn_cast<Instruction>(BCComp->getOperand(1))
                               : dyn_cast<Instruction>(BCComp->getOperand(0));
        if (SameCompTo == nullptr) {
          SameCompTo = CompToInst;
          auto *BCBranch = dyn_cast<BranchInst>(BCComp->getNextNode());
          TrapBlock = BCBranch->getSuccessor(0)->getName().startswith(
                          "not_in_bounds_block")
                          ? BCBranch->getSuccessor(0)
                          : BCBranch->getSuccessor(1);
        } else {
          if (SameCompTo != CompToInst) {
            std::cerr << "Expect everyone to compare to same instruction"
                      << std::endl;
            assert(false);
          }
        }
      }

      auto *MaxBCBlock =
          createBCBlock(BCMap.find(MaxPair.second.second)->second,
                        MaxPair.second.second, VMap);

      // Insert one Bounds Check with max value to entry block
      if (ExtractInstr->getParent() == EntryBlock &&
          SameCompTo->getParent() == EntryBlock) {
        if (SameCompTo->comesBefore(ExtractInstr)) {

        } else {
          auto *Splitted =
              EntryBlock->splitBasicBlock(SameCompTo->getNextNode());
          auto *Branch = &EntryBlock->getInstList().back();
          Branch->removeFromParent();
          Branch->deleteValue();
          BranchInst::Create(MaxBCBlock, EntryBlock);
          BranchInst::Create(Splitted, TrapBlock,
                             dyn_cast<Value>(&MaxBCBlock->getInstList().back()),
                             MaxBCBlock);
        }
      } else if (ExtractInstr->getParent() == EntryBlock) {

      } else if (SameCompTo->getParent() == EntryBlock) {

      } else {
        std::cerr << "Require either replace or Same Comp to be in entry block"
                  << std::endl;
        assert(false);
      }

      // Remove all bounds checks
      for (auto *BCComp : ExtractBCCompPair->second) {
        auto *BCBranch = dyn_cast<BranchInst>(BCComp->getNextNode());
        BasicBlock *LeftBlock = BCBranch->getSuccessor(0);
        BasicBlock *RightBlock = BCBranch->getSuccessor(1);
        if (LeftBlock->getName().startswith("not_in_bounds_block")) {
          BranchInst::Create(RightBlock, BCBranch);
        } else if (RightBlock->getName().startswith("not_in_bounds_block")) {
          BranchInst::Create(LeftBlock, BCBranch);
        } else {
          assert(false);
        }
        BCBranch->removeFromParent();
        BCBranch->deleteValue();
      }
    }

    for (auto &BB : F.getBasicBlockList()) {
      BB.dump();
    }

    return true;
  }
};
} // namespace

char WasmerMemoryAccessAnalysis::ID = 0;
INITIALIZE_PASS(WasmerMemoryAccessAnalysis, "bounds-check",
                "Interval Partition Construction", false, true)

Pass *llvm::createWasmerMemoryAccessAnalysis() {
  return new WasmerMemoryAccessAnalysis();
}