add_llvm_library( WasmerFunctionPass MODULE
        .WasmerFunctionPass.cpp

        PLUGIN_TOOL
        opt
        )

add_llvm_library( WasmerLoopPass MODULE
        .WasmerLoopPass.cpp

        PLUGIN_TOOL
        opt
        )

add_llvm_library( BoundsCheckLoopPass MODULE
        ../Scalar/WasmerBoundsCheckLoopOptimization.cpp

        PLUGIN_TOOL
        opt
        )
add_llvm_library( BoundsCheckPass MODULE
        ../Scalar/WasmerMemoryAccessAnalysis.cpp

        PLUGIN_TOOL
        opt
        )


