#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/MemorySSA.h"
#include <iostream>

using namespace llvm;

namespace {
struct WasmerFunctionPass : public FunctionPass {
  static constexpr const char* MEMORY_START_ANNO = "MemoryStartPointer";
  static constexpr const char* MAX_MEMORY_ANNO = "MaxMemoryPointer";
  static constexpr const char* MEMORY_START_LOAD_ANNO = "MemoryStartLoad";
  static constexpr const char* MAX_MEMORY_LOAD_ANNO = "MaxMemoryLoad";
  static constexpr const char* INITIAL_STORE_ANNO = "InitialStore";
  static constexpr const char* STORE_ANNO = "Store";



  static char ID;
  WasmerFunctionPass() : FunctionPass(ID) {}

  bool isAnnotated(Instruction* Inst, std::string_view Annotation){
    auto* MetaData = Inst->getMetadata(LLVMContext::MD_annotation);
    if(!MetaData){
      MetaData = Inst->getMetadata(10);
    }
    if (MetaData) {
      for (size_t Idx = 0; Idx < MetaData->getNumOperands(); ++Idx) {
        if (auto *StringMetaData =
                dyn_cast<MDString>(MetaData->getOperand(Idx).get())) {
          if (StringMetaData->getString().equals(Annotation.data())) {
            return true;
          }
        }
      }
    }
    return false;
  }

  bool runOnFunction(Function &F) override {
    auto&Ctx = F.getContext();

    // Find Start of Memory and Max Memory Pointer in entry block
    for(auto&Instruction : F.getEntryBlock()){
      if(auto* GEP = dyn_cast<GetElementPtrInst>(&Instruction)){
        if(GEP->getNumOperands() == 2){
          // First argument is start of metadata
          if(GEP->getOperand(0) == F.getArg(0)){
            // Second argument is offset of 180 or 188
            // TODO: Check why it differs
            if(GEP->getOperand(1) == ConstantInt::get(IntegerType::getInt32Ty(Ctx), 180)
                || GEP->getOperand(1) == ConstantInt::get(IntegerType::getInt32Ty(Ctx), 188)){

              // Bitcast to {i8*, i64}*
              if(auto* BitCast = dyn_cast<BitCastInst>(GEP->getNextNode())){

                // Retrieve Memory start
                if(auto* GEPMemStart = dyn_cast<GEPOperator>(BitCast->getNextNode())){
                  if(GEPMemStart->getType() == PointerType::get(PointerType::getInt8PtrTy(Ctx), 0)){
                    auto* MemoryStart = dyn_cast<llvm::Instruction>(GEPMemStart);
                    MemoryStart->addAnnotationMetadata(MEMORY_START_ANNO);
                  }
                }

                // Retrieve Max Memory
                if(auto* GEPMaxMem = dyn_cast<GEPOperator>(BitCast->getNextNode()->getNextNode())){
                  if(GEPMaxMem->getType() == PointerType::getInt64PtrTy(Ctx)){
                    auto* MaxMemory = dyn_cast<llvm::Instruction>(GEPMaxMem);
                    MaxMemory->addAnnotationMetadata(MAX_MEMORY_ANNO);
                  }
                }
              }
            }
          }
        }
      }
    }

    // Annotate Instructions
    for(auto&BasicBlock : F){
      for(auto&Instruction : BasicBlock){
        // Annotate load of max memory and memory start
        if(auto* Load = dyn_cast<LoadInst>(&Instruction)){
          if(auto* GEP = dyn_cast<llvm::Instruction>(Load->getOperand(0))){
            if(isAnnotated(GEP, MAX_MEMORY_ANNO)) {
              Load->addAnnotationMetadata(MAX_MEMORY_LOAD_ANNO);
            }else if (isAnnotated(GEP, MEMORY_START_ANNO)){
              Load->addAnnotationMetadata(MEMORY_START_LOAD_ANNO);
            }
          }
        }

        // Annotate store to local variables
        if(auto* Store = dyn_cast<StoreInst>(&Instruction)){
          if(auto* StoreDest = dyn_cast<llvm::Instruction>(Store->getOperand(1))){
            if(isAnnotated(StoreDest, MAX_MEMORY_ANNO)){
              // Never allow store to MAX_MEMORY value
              // TODO: Annotate that function should not be optimized
              assert(false);
            }else if(auto* Alloca = dyn_cast<AllocaInst>(StoreDest)){
              // Annotate the if a local variable is written only once or multiple
              // times in this function
              // TODO: Check if we actually need this
              if(!isAnnotated(Alloca, INITIAL_STORE_ANNO)){
                Alloca->addAnnotationMetadata(INITIAL_STORE_ANNO);
              }else if(!isAnnotated(Alloca, STORE_ANNO)){
                Alloca->addAnnotationMetadata(STORE_ANNO);
              }
            }
          }
        }
      }
    }

    return false;
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AssumptionCacheTracker>();
    AU.addPreserved<AssumptionCacheTracker>();
  }
};
}  // end of anonymous namespace

char WasmerFunctionPass::ID = 0;
static RegisterPass<WasmerFunctionPass> X("wasmer-function", "Hello World Pass",
                             false /* Only looks at CFG */,
                             true /* Analysis Pass */);


static RegisterStandardPasses Y(
    PassManagerBuilder::EP_EarlyAsPossible,
    [](const PassManagerBuilder &Builder,
       legacy::PassManagerBase &PM) { PM.add(new WasmerFunctionPass()); });
