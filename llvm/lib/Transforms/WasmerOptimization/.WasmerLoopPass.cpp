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

#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/WasmerPass.h"
#include <iostream>
#include <unordered_map>
#include <unordered_set>

namespace llvm {
class WasmerLoopPass : public LoopPass {
public:
  static char ID; // Pass ID, replacement for typeid
  WasmerLoopPass() : LoopPass(ID) {}

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {

    // Only optimize most outer loop
    if (L->getLoopDepth() != 1) {
      return false;
    }

    auto LB = getLoopBounds(L);
    // Loop bounds have not been found successfully
    if (!LB.IndexPointer || !LB.MaxValue) {
      return false;
    }

    std::unordered_set<Instruction *> NonLoopInvariantLocalVariables;
    ValueToValueMapTy VMap;

    // Analyze Loop
    for (auto *BB : L->getBlocks()) {
      for (auto &Instruction : *BB) {

        // Find all non loop invariant local variables
        if (auto *Store = dyn_cast<StoreInst>(&Instruction)) {
          // Store Destination is local variable
          if (auto *Alloca = dyn_cast<AllocaInst>(Store->getOperand(1))) {
            auto AllocIt = NonLoopInvariantLocalVariables.find(Alloca);
            if (AllocIt == NonLoopInvariantLocalVariables.end()) {
              NonLoopInvariantLocalVariables.insert(Alloca);
            } else {
              if (*AllocIt == LB.IndexPointer) {
                std::cerr << "Write twice to Index Pointer" << std::endl;
                return false;
              }
            }
          }
        }
      }
    }

    // Unroll one Loop Iteration
    auto UnrollRes = unrollOneLoopIteration(L, VMap);

    // Replace bounds check in Preheader with Max Value and assume
    // index is in bound in actual loop
    auto *BBDash = UnrollRes.HeaderStart;
    do {
      auto *LastInstruction = &BBDash->getInstList().back();
      if (isAnnotated(LastInstruction, WasmerBoundsCheck)) {
        // Get original block for cloned block BBDash
        auto *BB = dyn_cast<BasicBlock>(VMap[BBDash].operator llvm::Value *());
        // Try to replace bounds check in cloned block with max value
        if (replaceBCIndexWithMax(BBDash, LB.IndexPointer, LB.MaxValue)) {
          // Assume index is in bounds for original block
          assumeIndexIsInBounds(BB);
        }
      }
      BBDash = BBDash->getNextNode();
    } while (BBDash != UnrollRes.HeaderEnd);
    return true;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<AssumptionCacheTracker>();
    AU.addPreserved<AssumptionCacheTracker>();
    getLoopAnalysisUsage(AU);
  }

private:
  struct LoopBounds {
    Value *IndexPointer;
    Value *MaxValue;
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
            // TODO: Get bit_width = 8 from somewhere
            auto IWidth = Index->getAllocatedType()->getIntegerBitWidth() / 8;
            MaxIdx = dyn_cast<ConstantInt>(ConstantInt::get(
                MaxIdx->getType(), MaxIdx->getValue() + IWidth));
            return MaxIdx;
          }
        }
      }
    }
    return nullptr;
  }

  // Iterate reverse over the last loop block to find loop condition
  LoopBounds getLoopBounds(Loop *L) {
    // TODO: Return highest possible value instead of upper bound
    auto *BB = L->getBlocks().back();
    auto It = BB->rbegin();
    // Find loop bounds
    if (auto *Branch = dyn_cast<BranchInst>(&*It)) {
      if (Branch->getNumOperands() == 3) {
        if (auto *ICmp1 = dyn_cast<ICmpInst>(&*++It)) {
          if (auto *Zext = dyn_cast<ZExtInst>(&*++It)) {
            if (auto *ICmp2 = dyn_cast<ICmpInst>(&*++It)) {
              if (auto *Store = dyn_cast<StoreInst>(&(*++It))) {
                if (auto *Add = dyn_cast<AddOperator>(&(*++It))) {
                  if (auto *Load = dyn_cast<LoadInst>(&(*++It))) {
                    // Check if branch depends on ICMP 1
                    if (Branch->getOperand(0) == ICmp1) {
                      // Check if zext extends ICMP 2
                      if (Zext->getOperand(0) == ICmp2) {
                        // Check if ICMP 1 operand 1 is 0
                        if (auto *Const =
                                dyn_cast<ConstantInt>(ICmp1->getOperand(1))) {
                          if (Const->getValue() == 0) {
                            // Check if stored to local variable
                            if (auto *Index = dyn_cast<AllocaInst>(
                                    Store->getOperand(1))) {
                              // Check if loaded from same variable
                              if (Load->getOperand(0) == Index) {
                                // Check if ICMP 2 compares with added value
                                if (ICmp2->getOperand(0) == Add) {
                                  // Check if second operand of ICMP is int
                                  // constant
                                  if (auto *MaxIdx = dyn_cast<ConstantInt>(
                                          ICmp2->getOperand(1))) {
                                    // Check if incrementing or decrementing
                                    // loop
                                    if (auto *AddValue = dyn_cast<ConstantInt>(
                                            Add->getOperand(1))) {
                                      if (AddValue->isNegative()) {
                                        MaxIdx =
                                            findStoreToIdxInPreHeader(L, Index);
                                        if (MaxIdx) {
                                          std::cerr << "Decrement loop found"
                                                    << std::endl;
                                          Index->dump();
                                          MaxIdx->dump();
                                          std::cerr << "Dump end" << std::endl;
                                          return {Index, MaxIdx};
                                        }
                                      } else {
                                        std::cerr << "Incrementing loop found"
                                                  << std::endl;
                                        Index->dump();
                                        MaxIdx->dump();
                                        std::cerr << "Dump end" << std::endl;
                                        return {Index, MaxIdx};
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    std::cerr << "failed to find loop bounds" << std::endl;
    std::cerr << "dumping last block: " << std::endl;
    L->getBlocks().back()->dump();
    std::cerr << "end of last block dump" << std::endl;
    return {nullptr, nullptr};
  }

  // Copy all BasicBlocks from Loop to PreHeader
  LoopUnrollReturn unrollOneLoopIteration(Loop *L, ValueToValueMapTy &VMap) {
    auto *FirstPreLoopBlock = L->getLoopPreheader();
    auto *LastPreLoopBlock = FirstPreLoopBlock;
    auto *HeaderBlock = L->getHeader();

    std::vector<BasicBlock *> OriginalBlocks;
    std::vector<BasicBlock *> ClonedBlocks;
    std::unordered_map<BasicBlock *, size_t> IndexMap;
    // Extract one Loop iteration to Preheader
    for (auto *BB : L->getBlocks()) {
      auto *LastInstruction = &BB->getInstList().back();
      auto *Branch = dyn_cast<BranchInst>(LastInstruction);
      assert(Branch);
      auto *BBDash =
          CloneBasicBlock(BB, VMap, "_bounds_check", BB->getParent());
      VMap[BBDash] = BB;
      VMap[BB] = BBDash;
      for (auto &Inst : *BBDash) {
        RemapInstruction(&Inst, VMap,
                         RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
      }
      IndexMap.emplace(BB, OriginalBlocks.size());
      OriginalBlocks.push_back(BB);
      ClonedBlocks.push_back(BBDash);
    }

    // Branch from FirstPreLoop Block to cloned Header
    auto *ClonedHeader =
        dyn_cast<BasicBlock>(VMap[HeaderBlock].operator llvm::Value *());
    auto *PreHeaderBranch =
        dyn_cast<BranchInst>(&FirstPreLoopBlock->getInstList().back());
    for (size_t SuccIdx = 0; SuccIdx < PreHeaderBranch->getNumSuccessors();
         ++SuccIdx) {
      if (PreHeaderBranch->getSuccessor(SuccIdx) == HeaderBlock) {
        PreHeaderBranch->setSuccessor(SuccIdx, ClonedHeader);
      }
    }

    // Remap all Cloned Blocks
    for (size_t Idx = 0; Idx < ClonedBlocks.size(); ++Idx) {
      auto *ClonedBlock = ClonedBlocks.at(Idx);
      ClonedBlock->moveAfter(LastPreLoopBlock);
      auto *LastInstruction = &ClonedBlock->getInstList().back();
      if (auto *Branch = dyn_cast<BranchInst>(LastInstruction)) {
        for (size_t SuccIdx = 0; SuccIdx < Branch->getNumSuccessors();
             ++SuccIdx) {
          auto *OldSucc = Branch->getSuccessor(SuccIdx);
          auto OldIt = IndexMap.find(OldSucc);
          if (OldIt != IndexMap.end()) {
            Branch->setSuccessor(SuccIdx, ClonedBlocks.at(OldIt->second));
          }
        }
      }
      LastPreLoopBlock = ClonedBlock;
    }

    // Branch from Last Pre Loop Block to old header
    PreHeaderBranch =
        dyn_cast<BranchInst>(&LastPreLoopBlock->getInstList().back());
    for (size_t SuccIdx = 0; SuccIdx < PreHeaderBranch->getNumSuccessors();
         ++SuccIdx) {
      if (PreHeaderBranch->getSuccessor(SuccIdx) == ClonedHeader) {
        PreHeaderBranch->setSuccessor(SuccIdx, HeaderBlock);
      }
    }
    return {FirstPreLoopBlock, LastPreLoopBlock};
  }

  bool replaceBCIndexWithMax(BasicBlock *BB, Value *IndexPointer,
                             Value *MaxValue) {
    bool ReplacedMax = false;
    for (auto &MemAddressInst : *BB) {
      if (isAnnotated(&MemAddressInst, MemoryAccessIndex)) {
        ICmpInst *BoundsCheckCompare = nullptr;
        // Check if bounds check on mem access index is performed
        if (auto *AddSize =
                dyn_cast<AddOperator>(MemAddressInst.getNextNode())) {
          if (AddSize->getOperand(0) == &MemAddressInst) {
            if (auto *LoadMaxMem = dyn_cast<LoadInst>(
                    MemAddressInst.getNextNode()->getNextNode())) {
              if (isAnnotated(LoadMaxMem, MaxMemoryLoadAnno)) {
                if (auto *ICmp =
                        dyn_cast<ICmpInst>(MemAddressInst.getNextNode()
                                               ->getNextNode()
                                               ->getNextNode())) {
                  if (ICmp->getNumOperands() == 2 &&
                      ICmp->getOperand(0) == AddSize &&
                      ICmp->getOperand(1) == LoadMaxMem) {
                    // Compare of index and max bounds found
                    BoundsCheckCompare = ICmp;
                  }
                }
              }
            }
          }
        }

        if (BoundsCheckCompare) {
          // Use MaxValue in bounds check
          std::vector<llvm::Instruction *> CopiedInstructions;
          std::vector<llvm::Instruction *> InstructionsToCopy;
          std::unordered_map<llvm::Instruction *, size_t>
              OriginalInstructionMap;
          InstructionsToCopy.push_back(&MemAddressInst);
          CopiedInstructions.push_back(MemAddressInst.clone());
          CopiedInstructions.back()->insertAfter(&MemAddressInst);
          OriginalInstructionMap.emplace(&MemAddressInst, 0);

          // Collect all Instructions that need to be copied
          for (size_t CopyStartIdx = 0;
               CopyStartIdx != InstructionsToCopy.size(); ++CopyStartIdx) {
            auto *Next = InstructionsToCopy.at(CopyStartIdx);
            for (auto *OpIt = Next->op_begin(); OpIt != Next->op_end();
                 ++OpIt) {
              if (auto *OpInst = dyn_cast<llvm::Instruction>(*OpIt)) {
                if (!dyn_cast<LoadInst>(OpInst)) {
                  auto *Cloned = OpInst->clone();
                  OriginalInstructionMap.emplace(OpInst,
                                                 InstructionsToCopy.size());
                  InstructionsToCopy.push_back(OpInst);
                  Cloned->insertAfter(OpInst);
                  CopiedInstructions.push_back(Cloned);
                }
              }
            }
          }

          // Update Operands in Copied Instructions
          for (auto ItOg = InstructionsToCopy.rbegin();
               ItOg != InstructionsToCopy.rend(); ++ItOg) {
            auto Index = OriginalInstructionMap.find(*ItOg)->second;
            auto *CpyInst = CopiedInstructions.at(Index);
            for (size_t OpIndex = 0; OpIndex < CpyInst->getNumOperands();
                 ++OpIndex) {
              auto *Operand = CpyInst->getOperand(OpIndex);
              if (auto *Load = dyn_cast<LoadInst>(Operand)) {
                assert(Load->getNumOperands() == 1);
                if (Load->getOperand(0) == IndexPointer &&
                    Load->getNumOperands() == 1) {
                  // Replace Index with Max Value
                  // isAnnotated(dyn_cast<Instruction>(IndexPointer),
                  // "NotLoopIV"
                  CpyInst->setOperand(OpIndex, MaxValue);
                  ReplacedMax = true;
                } else {
                  // TODO: This check doesnt work -> fix it
                  // TODO: Check if only loaded LoopIV
                  // assert(!isAnnotated(dyn_cast<Instruction>(Load->getOperand(0)),
                  // "NotLoopIV"));
                }
              } else if (auto *Inst = dyn_cast<llvm::Instruction>(Operand)) {
                CpyInst->setOperand(
                    OpIndex, CopiedInstructions.at(
                                 OriginalInstructionMap.find(Inst)->second));
              }
            }
          }

          // Use Max Index value for bounds check
          BoundsCheckCompare->setOperand(0, CopiedInstructions.front());
        }
      }
    }
    return ReplacedMax;
  }

  void assumeIndexIsInBounds(BasicBlock *BB) {
    auto *LastInst = &BB->getInstList().back();
    assert(isAnnotated(LastInst, "wasmer_bounds_check"));
    auto *Prev = LastInst->getPrevNode();
    while (!dyn_cast<ICmpInst>(Prev)) {
      Prev = Prev->getPrevNode();
    }
    // Cmp Instruction for bounds check
    auto *ICMPInst = dyn_cast<ICmpInst>(Prev);
    Function *AssumeIntrinsic =
        Intrinsic::getDeclaration(ICMPInst->getModule(), Intrinsic::assume);
    CallInst *CI = CallInst::Create(AssumeIntrinsic, {ICMPInst});
    CI->insertAfter(ICMPInst);
    AssumptionCache AC =
        getAnalysis<AssumptionCacheTracker>().getAssumptionCache(
            *ICMPInst->getFunction());
    AC.registerAssumption(CI);
  }
};
} // namespace llvm

char llvm::WasmerLoopPass::ID = 0;
static llvm::RegisterPass<llvm::WasmerLoopPass> X("wasmer-loop",
                                                  "Hello World Pass",
                                                  false /* Only looks at CFG */,
                                                  false /* Analysis Pass */);

static llvm::RegisterStandardPasses
    Y(llvm::PassManagerBuilder::EP_EarlyAsPossible,
      [](const llvm::PassManagerBuilder &Builder,
         llvm::legacy::PassManagerBase &PM) {
        PM.add(new llvm::WasmerLoopPass());
      });

llvm::Pass *llvm::createBoundsCheckLoop() { return new WasmerLoopPass(); }