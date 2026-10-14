## What changed

No Lean or DAG changes are needed. The sandbox module is byte-for-byte identical
to the repository module. Upstream review #1424's requested Mathlib repair already
landed as 20261014T030641-L-342008. The landed change record
coord/changes/tensor-bicomplex-mathlib-direct.md explicitly preserves the transparent
compatibility abbreviations and withdraws caller adaptations.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: none. Holes left: none. No statements split off.
HomologicalComplex₂.tensorBicomplex is the canonical Mathlib bifunctor object;
HomologicalComplex₂.tensorBicomplexMap is its uncurried map;
HomologicalComplex₂.chainTensorMap is a concrete composite of induced maps.

This retry compiled scratchpad/TensorBicomplex__probe.lean with exit code 0 in
1.6 seconds, with no warnings. All three declarations use only propext,
Classical.choice and Quot.sound. The retained probe checks terms and map components
at arbitrary natural degrees, including zero.

## No longer needed

No imports, nodes or modules pruned. No caller adaptations are necessary.

## Where the brief, the DAG or earlier work was wrong

The repair assignment is stale: the requested repair is already landed. The node
records exactly the Mathlib route now implemented. Removing the compatibility
names would contradict the landed return repair; manufacturing a cosmetic change
would not repair anything.

## Earlier second reading (a previous round; superseded)

The canonical Mathlib definitions and all public signatures were checked against
the upstream repair request. The module compiles independently, and no caller
adaptations are required. The added module documentation records why the
uncurried bifunctor map is the required construction.

## Second reading by Q4

1. **Visible changes.** Compared the delivered module with the repository version. All declaration
signatures and definitions are byte-for-byte identical; the only change is an explanatory sentence
in the module documentation. No DAG or change-record edits are present.

2. **Compilation and proof integrity.** Compiled the delivered module with `lcompile.py` (exit code
0, no warnings). Searched the delivered Lean files for `sorry`, `axiom`, `unsafe`, `opaque`,
`implemented_by`, and `extern`; none occur. The existing probe prints only the permitted axioms for
all three declarations and checks their term and map components.

3. **Statements and dependencies.** The three public declarations retain the exact canonical
Mathlib constructions and signatures recorded in the node. No theorem was split off, no statement
was weakened, and no hollow definition was introduced.

4. **Pruning and route.** The proof uses the canonical `mapBifunctorHomologicalComplex`, uncurried
map, and `chainTensorMap` route recorded by the node. All four public imports support declarations
or definitions in this module; no import or proof dependency can be removed. The unit route and
`realized` node are unchanged.

5. **Node/report consistency.** The node's `proof`, `proof_deps`, and `proof_origin` agree with the
Lean definitions. There are no new nodes, split statements, forced adaptations, or changed
interfaces.

Changed only the module documentation by clarifying that `tensorBicomplexMap` inherits its chain-map
identities from Mathlib.
