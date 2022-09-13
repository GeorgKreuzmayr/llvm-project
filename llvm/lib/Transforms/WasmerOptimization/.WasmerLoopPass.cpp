#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/WasmerPass.h"

#include <iostream>
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
    ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
    auto lb = L->getBounds(SE);
    auto InductionVariable = L->getInductionVariable(SE);
    if (lb) {
      if (isa<ConstantInt>(&lb.getValue().getInitialIVValue()) &&
          isa<ConstantInt>(&lb.getValue().getFinalIVValue())) {
        std::cerr << "Max: ";
        if (lb.getValue().getDirection() ==
            Loop::LoopBounds::Direction::Increasing) {
          lb.getValue().getFinalIVValue().dump();
          std::cerr << "Min: ";
          lb.getValue().getInitialIVValue().dump();
        } else {
          lb.getValue().getInitialIVValue().dump();
          std::cerr << "Min: ";
          lb.getValue().getFinalIVValue().dump();
        }
        std::cerr << "IV: ";
        L->getInductionVariable(SE)->dump();
      }

    } else {
      return false;
    }

    std::unordered_set<Instruction *> NonLoopInvariantLocalVariables;
    ValueToValueMapTy VMap;

    // Analyze Loop
    for (auto *BB : L->getBlocks()) {
      auto &LastInst = BB->getInstList().back();
      if (isAnnotated(&LastInst, WasmerBoundsCheck)) {
        if (auto *BCCompare = dyn_cast<ICmpInst>(LastInst.getPrevNode())) {
          std::vector<Instruction *> BCInstructions;
          BCInstructions.push_back(BCCompare);

          // Collect all non loop invariant instructions to calculate bounds
          // check
          size_t MaxIdx = 1;
          for (size_t CopyStartIdx = 0; CopyStartIdx != MaxIdx;
               ++CopyStartIdx) {
            auto *Next = BCInstructions.at(CopyStartIdx);
            for (size_t OpIdx = 0; OpIdx < Next->getNumOperands(); ++OpIdx) {
              auto *Operand = Next->getOperand(OpIdx);
              if (L->isLoopInvariant(Operand)) {
                Operand->dump();
              } else if (auto *OpInst = dyn_cast<Instruction>(Operand)) {
                if(OpInst != InductionVariable){
                  BCInstructions.push_back(OpInst);
                  ++MaxIdx;
                }
              } else {
                std::cerr << "This is unexpected, found a: ";
                Operand->dump();
                assert(false);
              }
            }
          }
        }
      }
    }

    unrollOneLoopIteration(L, VMap);

    // Manipulate Loop
    for (auto *BB : L->getBlocks()) {
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
                if (!L->isLoopInvariant(Operand) && !isa<PHINode>(OpInst)){
                  BCInstructions.push_back(OpInst);
                  ++MaxIdx;
                }
              }
            }
          }
        }
      }
    }

    // auto &LastInst = BB->getInstList().back();
    return false;
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

    if (auto *PhiNode =
            dyn_cast<PHINode>(&FirstLoopBlock->getInstList().front())) {
      for (size_t OpIdx = 0; OpIdx < PhiNode->getNumIncomingValues(); ++OpIdx) {
        auto *OldIncomingBlock = PhiNode->getIncomingBlock(OpIdx);
        if (OldIncomingBlock == LoopPreHeaderBlock) {
          PhiNode->setIncomingBlock(OpIdx, LastPreLoopBlock);
        }
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
        FirstInstruction->dump();
        auto *OgBlock = dyn_cast<BasicBlock>(&*VMap[ClonedBlock]);
        OgBlock->getInstList().front().dump();
      }
    }
    return {LoopPreHeaderBlock, LastPreLoopBlock};
  }

  // Remove all instructions from Basic Block
  void removeInstructions(std::vector<Instruction *> &CopiedInst) {
    // TODO: Fix removing instructions
    for (auto InstIt = CopiedInst.rbegin(); InstIt != CopiedInst.rend();
         ++InstIt) {
      // auto* Inst = *InstIt;
      // Inst->eraseFromParent();
    }
  }

  // Replace value that is used for bounds check by maximal value of
  // IndexPointer, by copying instructions that are
  bool replaceBCIndexWithMax(
      BasicBlock *BB, Value *IndexPointer, Value *MaxValue,
      std::unordered_set<Instruction *> &NonLoopInvariantLocalVariables,
      ValueToValueMapTy &VMap) {
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

        // Copy bounds check instructions and replace index with its max value
        if (BoundsCheckCompare) {
          std::vector<llvm::Instruction *> CopiedInstructions;
          std::vector<llvm::Instruction *> InstructionsToCopy;
          InstructionsToCopy.push_back(&MemAddressInst);
          CopiedInstructions.push_back(MemAddressInst.clone());
          CopiedInstructions.back()->insertAfter(&MemAddressInst);
          VMap[InstructionsToCopy.back()] = CopiedInstructions.back();

          // Collect all Instructions that need to be copied
          // Iterate over all operators of an instruction and recursively add
          // them to InstructionsToCopy
          for (size_t CopyStartIdx = 0;
               CopyStartIdx != InstructionsToCopy.size(); ++CopyStartIdx) {
            auto *Next = InstructionsToCopy.at(CopyStartIdx);
            // TODO: Check if Instruction* can get invalidated
            for (auto *OpIt = Next->op_begin(); OpIt != Next->op_end();
                 ++OpIt) {
              // If operator is any instruction other than a load instruction,
              // add it to InstructionsToCopy
              if (auto *OpInst = dyn_cast<llvm::Instruction>(*OpIt)) {
                if (!dyn_cast<LoadInst>(OpInst)) {
                  auto *Cloned = OpInst->clone();
                  VMap[OpInst] = Cloned;
                  InstructionsToCopy.push_back(OpInst);
                  CopiedInstructions.push_back(Cloned);
                  Cloned->insertAfter(OpInst);
                }
              }
            }
          }

          // Update Operands in Copied Instructions
          for (int Index = InstructionsToCopy.size() - 1; Index >= 0; --Index) {
            auto *CpyInst = CopiedInstructions.at(Index);
            // Replace Load of index with max value and check if other loads are
            // loop invariant
            for (size_t OpIndex = 0; OpIndex < CpyInst->getNumOperands();
                 ++OpIndex) {
              auto *Operand = CpyInst->getOperand(OpIndex);
              // Replace index load with MaxValue and check if other load
              // operands are loop invariant
              if (auto *Load = dyn_cast<LoadInst>(Operand)) {
                auto *Alloca = dyn_cast<AllocaInst>(Load->getOperand(0));
                // All load operands must be local variables and load must only
                // have one operand
                assert(Load->getNumOperands() == 1);
                assert(Alloca);
                if (Alloca == IndexPointer) {
                  // Replace Index with Max Value
                  CpyInst->setOperand(OpIndex, MaxValue);
                  ReplacedMax = true;
                } else {
                  if (NonLoopInvariantLocalVariables.find(Alloca) !=
                      NonLoopInvariantLocalVariables.end()) {
                    std::cerr << "Load from non loop invariant value, other "
                                 "than index"
                              << std::endl;
                    removeInstructions(CopiedInstructions);
                    return false;
                  }
                }
              }
            }
            // Remap known operands to cloned instructions
            RemapInstruction(CpyInst, VMap,
                             RF_IgnoreMissingLocals | RF_NoModuleLevelChanges);
          }

          if (ReplacedMax) {
            // Use copied instruction for bounds check
            if (auto *AddWidth = dyn_cast<AddOperator>(
                    CopiedInstructions.front()->getNextNode())) {
              if (AddWidth->getOperand(0) == &MemAddressInst) {
                // Replace MemAddressInst with copied instruction using max
                // index value
                AddWidth->setOperand(0, CopiedInstructions.front());
                return true;
              }
            }
            removeInstructions(CopiedInstructions);
          } else {
            // If max could not be replaced, remove all copied instructions
            removeInstructions(CopiedInstructions);
          }
        }
      }
    }
    return false;
  }

  // Add assumption that index is always in bounds, so that further
  // optimization passes will remove the bounds check
  void assumeIndexIsInBounds(BasicBlock *BB) {
    auto *LastInst = &BB->getInstList().back();
    assert(isAnnotated(LastInst, WasmerBoundsCheck));
    if (auto *ICmp =
            dyn_cast<ICmpInst>(LastInst->getPrevNode()->getPrevNode())) {
      Function *AssumeIntrinsic =
          Intrinsic::getDeclaration(ICmp->getModule(), Intrinsic::assume);
      CallInst *CI = CallInst::Create(AssumeIntrinsic, {ICmp});
      CI->insertAfter(ICmp);
      AssumptionCache AC =
          getAnalysis<AssumptionCacheTracker>().getAssumptionCache(
              *ICmp->getFunction());
      AC.registerAssumption(CI);
    } else {
      // Compare must happen two instructions before branch
      assert(false);
    }
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