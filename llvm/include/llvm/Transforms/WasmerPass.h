#ifndef LLVM_WASMERPASS_H
#define LLVM_WASMERPASS_H
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/MDBuilder.h"
#include <string_view>

namespace llvm {
static constexpr const char *MemoryStartValue = "MemoryStartPointer";
static constexpr const char *MaxMemoryAnno = "MaxMemoryPointer";
static constexpr const char *LoadMemoryStart = "MemoryStartLoad";
static constexpr const char *MaxMemoryLoadAnno = "MaxMemoryLoad";
static constexpr const char *InitialStoreAnno = "InitialStore";
static constexpr const char *StoreAnno = "Store";
static constexpr const char *FunctionNotOptimizeAnno = "DoNotOptimizeFunction";
static constexpr const char *AccessHeapMemory = "HeapMemAcc";
static constexpr const char *MemoryAccessIndex = "MemoryAccessIndex";
static constexpr const char *GEPMemoryAccess = "MemoryAccess";
static constexpr const char *WasmerBoundsCheck = "wasmer_bounds_check";

inline void annotateFunction(Function &F) {
  MDBuilder MDB(F.getContext());
  MDNode *MD =
      MDTuple::get(F.getContext(), MDB.createString(FunctionNotOptimizeAnno));
  F.setMetadata(LLVMContext::MD_annotation, MD);
}

inline bool isAnnotated(Instruction *Inst, std::string_view Annotation) {
  static_assert(LLVMContext::MD_annotation == 30,
                "Annotation in wasmer are done on KindID 30");
  auto *MetaData = Inst->getMetadata(LLVMContext::MD_annotation);
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
