# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.10

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/nitish/LLVM_Workspace/IntraProceduralSlicing

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/nitish/LLVM_Workspace/IntraProceduralSlicing/build

# Include any dependencies generated for this target.
include CMakeFiles/InPSPass.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/InPSPass.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/InPSPass.dir/flags.make

CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o: CMakeFiles/InPSPass.dir/flags.make
CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o: ../IntraProceduralSlicing.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/nitish/LLVM_Workspace/IntraProceduralSlicing/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o -c /home/nitish/LLVM_Workspace/IntraProceduralSlicing/IntraProceduralSlicing.cpp

CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/nitish/LLVM_Workspace/IntraProceduralSlicing/IntraProceduralSlicing.cpp > CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.i

CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/nitish/LLVM_Workspace/IntraProceduralSlicing/IntraProceduralSlicing.cpp -o CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.s

CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o.requires:

.PHONY : CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o.requires

CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o.provides: CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o.requires
	$(MAKE) -f CMakeFiles/InPSPass.dir/build.make CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o.provides.build
.PHONY : CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o.provides

CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o.provides.build: CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o


# Object files for target InPSPass
InPSPass_OBJECTS = \
"CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o"

# External object files for target InPSPass
InPSPass_EXTERNAL_OBJECTS =

libInPSPass.so: CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o
libInPSPass.so: CMakeFiles/InPSPass.dir/build.make
libInPSPass.so: CMakeFiles/InPSPass.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/nitish/LLVM_Workspace/IntraProceduralSlicing/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX shared module libInPSPass.so"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/InPSPass.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/InPSPass.dir/build: libInPSPass.so

.PHONY : CMakeFiles/InPSPass.dir/build

CMakeFiles/InPSPass.dir/requires: CMakeFiles/InPSPass.dir/IntraProceduralSlicing.cpp.o.requires

.PHONY : CMakeFiles/InPSPass.dir/requires

CMakeFiles/InPSPass.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/InPSPass.dir/cmake_clean.cmake
.PHONY : CMakeFiles/InPSPass.dir/clean

CMakeFiles/InPSPass.dir/depend:
	cd /home/nitish/LLVM_Workspace/IntraProceduralSlicing/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/nitish/LLVM_Workspace/IntraProceduralSlicing /home/nitish/LLVM_Workspace/IntraProceduralSlicing /home/nitish/LLVM_Workspace/IntraProceduralSlicing/build /home/nitish/LLVM_Workspace/IntraProceduralSlicing/build /home/nitish/LLVM_Workspace/IntraProceduralSlicing/build/CMakeFiles/InPSPass.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/InPSPass.dir/depend

