set(LLVM_LINK_COMPONENTS
  Support
  )

add_llvm_library(LLVMMCAnalysis
 MCAtom.cpp
 MCFunction.cpp
 MCModule.cpp
 MCObjectDisassembler.cpp
)
