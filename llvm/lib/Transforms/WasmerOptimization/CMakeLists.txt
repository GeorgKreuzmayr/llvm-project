add_llvm_library( WasmerFunctionPass MODULE
        WasmerFunctionPass.cpp

        PLUGIN_TOOL
        opt
        )