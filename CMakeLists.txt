cmake_minimum_required(VERSION 3.5)
find_package(LLVM REQUIRED CONFIG)

list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
include(AddLLVM)

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS} /usr/lib /usr/include)

if(WIN32 OR CYGWIN)
  set(LLVM_LINK_COMPONENTS Core Support)
endif()


add_library(InPSPass MODULE
    # List your source files here.
    IntraProceduralSlicing.cpp
)

# Use C++11 to compile our pass (i.e., supply -std=c++11).
target_compile_features(InPSPass PRIVATE cxx_range_for cxx_auto_type)

# LLVM is (typically) built with no C++ RTTI. We need to match that;
# otherwise, we'll get linker errors about missing RTTI data.
set_target_properties(InPSPass PROPERTIES
    COMPILE_FLAGS "-fno-rtti -no-pie"
)

