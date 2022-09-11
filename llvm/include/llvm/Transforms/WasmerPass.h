#ifndef LLVM_WASMERPASS_H
#define LLVM_WASMERPASS_H
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include <string_view>

namespace llvm {
static constexpr const char* MemoryStartAnno = "MemoryStartPointer";
static constexpr const char* MaxMemoryAnno = "MaxMemoryPointer";
static constexpr const char* MemoryStartLoadAnno = "MemoryStartLoad";
static constexpr const char* MaxMemoryLoadAnno = "MaxMemoryLoad";
static constexpr const char* InitialStoreAnno = "InitialStore";
static constexpr const char* StoreAnno = "Store";
static constexpr const char* FunctionNotOptimizeAnno = "DoNotOptimizeFunction";

inline void annotateFunction(Function& F){
  MDBuilder MDB(F.getContext());
  MDNode *MD = MDTuple::get(F.getContext(), MDB.createString(FunctionNotOptimizeAnno));
  F.setMetadata(LLVMContext::MD_annotation, MD);
}

inline bool isAnnotated(Instruction* Inst, std::string_view Annotation){
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

} // namespace llvm
#endif // LLVM_WASMERPASS_H
