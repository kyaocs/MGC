# MGC: Maximum Generalized Clique Computation

Source code for maximum generalized clique (MGC) computation and the index structures used by our indexed algorithms.

The repository contains two executables:

- `build_index`: builds DB-Index or BC-Index;
- `query`: runs global MGC computation or an MGC query containing a specified vertex.

## Requirements

- Linux
- `g++` with C++17 support
- GNU Make

No third-party library is required.

## Compilation

```bash
make
```

This generates:

```text
bin/build_index
bin/query
```

## Input graph

For a graph named `<graph>`, the program reads:

```text
<data_dir>/<graph>/b_degree.bin
<data_dir>/<graph>/b_adj.bin
```

`b_degree.bin` stores the integer size, the number of vertices, the number of adjacency entries, and the degree of each vertex. `b_adj.bin` stores all adjacency lists consecutively. Vertex IDs must be in `[0,n-1]`, and each adjacency list must be sorted increasingly.

## Index construction

```bash
./bin/build_index <data_dir> <graph> <index_type> [parameters]
```

### DB-Index

Standard construction:

```bash
./bin/build_index DATA_DIR GRAPH DB \
    TAU MAX_ROUND K BANDS THRESHOLD RHO MIN_CLUSTER MIN_GAIN
```

Memory-bounded batch construction:

```bash
./bin/build_index DATA_DIR GRAPH DB-Batch \
    TAU MAX_ROUND K BANDS THRESHOLD RHO MIN_CLUSTER MIN_GAIN
```

`DB` and `DB-Batch` construct the same **DB-Index** based on rho-dense blocks. `DB-Batch` is the memory-bounded implementation used when the intermediate graph is too large to construct in memory at once.

The generated files are named:

```text
<graph>_<config>_DBa.bin
<graph>_<config>_DBb.bin
```

or, for the memory-bounded construction:

```text
<graph>_<config>_DBBatcha.bin
<graph>_<config>_DBBatchb.bin
```

### BC-Index

```bash
./bin/build_index DATA_DIR GRAPH BC \
    TAU MAX_ROUND MIN_CLUSTER MIN_GAIN
```

BC-Index is constructed from bicliques.

All index files are written to `./index/`.

## Global MGC computation

```bash
./bin/query <data_dir> <graph> <epsilon> <size_threshold> global <method> [parameters]
```

### MGC-Mat

```bash
./bin/query DATA_DIR GRAPH EPS SIZE global MGC-Mat
```

### Mat-Prog

```bash
./bin/query DATA_DIR GRAPH EPS SIZE global Mat-Prog
```

### MGC-DB

Using a DB-Index built by the standard constructor:

```bash
./bin/query DATA_DIR GRAPH EPS SIZE global MGC-DB standard \
    TAU MAX_ROUND K BANDS THRESHOLD RHO MIN_CLUSTER MIN_GAIN
```

Using a DB-Index built by the memory-bounded constructor:

```bash
./bin/query DATA_DIR GRAPH EPS SIZE global MGC-DB batch \
    TAU MAX_ROUND K BANDS THRESHOLD RHO MIN_CLUSTER MIN_GAIN
```

Both commands run the same **MGC-DB** query algorithm. The `standard`/`batch` argument only specifies which DB-Index file to load.

### MGC-BC

```bash
./bin/query DATA_DIR GRAPH EPS SIZE global MGC-BC \
    TAU MAX_ROUND MIN_CLUSTER MIN_GAIN
```

## Vertex MGC query

The `vertex` mode computes an MGC containing a specified query vertex `Q`.

### MGC-Mat

```bash
./bin/query DATA_DIR GRAPH EPS SIZE vertex MGC-Mat Q
```

### MGC-DB

With a standard-built DB-Index:

```bash
./bin/query DATA_DIR GRAPH EPS SIZE vertex MGC-DB Q standard \
    TAU MAX_ROUND K BANDS THRESHOLD RHO MIN_CLUSTER MIN_GAIN
```

With a memory-bounded DB-Index:

```bash
./bin/query DATA_DIR GRAPH EPS SIZE vertex MGC-DB Q batch \
    TAU MAX_ROUND K BANDS THRESHOLD RHO MIN_CLUSTER MIN_GAIN
```

The index parameters supplied to `query` must match those used during index construction because the configuration is encoded in the index filename.

## Methods

| Paper name | Implementation |
|---|---|
| `MGC-Mat` | Materializes the similarity-augmented graph before MGC computation |
| `Mat-Prog` | Progressively computes similarity neighborhoods during MGC search |
| `MGC-DB` | Uses DB-Index constructed from rho-dense blocks |
| `MGC-BC` | Uses BC-Index constructed from bicliques |

## Repository structure

```text
MGC/
├── Makefile
├── README.md
├── index/
└── src/
    ├── build_index/
    │   ├── build_index.cpp
    │   ├── LinearHeap.h
    │   ├── Timer.h
    │   └── Utility.h
    └── query/
        ├── query.cpp
        ├── Heu.h
        ├── LinearHeap.h
        ├── Timer.h
        └── Utility.h
```
