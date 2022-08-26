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
        ../Scalar/BoundsCheckLoopPass.cpp

        PLUGIN_TOOL
        opt
        )
add_llvm_library( BoundsCheckPass MODULE
        ../Scalar/BoundsCheckPass.cpp

        PLUGIN_TOOL
        opt
        )


