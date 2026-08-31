CXX ?= g++
CXXFLAGS ?= -O3 -std=c++17

BIN_DIR := bin
BUILD_INDEX := $(BIN_DIR)/build_index
QUERY := $(BIN_DIR)/query

.PHONY: all clean

all: $(BUILD_INDEX) $(QUERY)

$(BIN_DIR):
	mkdir -p $(BIN_DIR)

$(BUILD_INDEX): src/build_index/build_index.cpp src/build_index/Utility.h src/build_index/Timer.h src/build_index/LinearHeap.h | $(BIN_DIR)
	$(CXX) $(CXXFLAGS) src/build_index/build_index.cpp -o $(BUILD_INDEX)

$(QUERY): src/query/query.cpp src/query/Utility.h src/query/Timer.h src/query/LinearHeap.h src/query/Heu.h | $(BIN_DIR)
	$(CXX) $(CXXFLAGS) src/query/query.cpp -o $(QUERY)

clean:
	rm -rf $(BIN_DIR)
