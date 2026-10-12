## What changed
Added two strictly smaller intermediate theorems in `FlatModelFiniteFreeConstruction` and `FlatModelFiniteFreeComparison`. The target theorem now combines their outputs by destructuring the structural conjunction and applying the comparison theorem.

## Proved and sorry left
The target `exists_local_finiteFree_shortening` is proved by a real Lean composition. The new declarations `exists_local_finiteFree_construction` and `local_finiteFree_homology_comparison` remain `sorry`, with nodes `lem-pc-flat-model-finite-free-shortening-construction` and `lem-pc-flat-model-finite-free-shortening-comparison`.

## No longer needed
None; the target's existing public imports remain required for the intermediate statements.

## Where the brief, the DAG or earlier work was wrong
The planned three imported lemmas do not expose enough structure to construct the sheaf-level complex in this interface, so the unproved work had to be split into the construction and comparison statements above.

## New nodes
`lem-pc-flat-model-finite-free-shortening-construction` and `lem-pc-flat-model-finite-free-shortening-comparison` are new stage-3 holes, each strictly smaller than the target and documented in its module.

## Second reading by F2

1. I compared all delivered modules with the repository versions. The target declaration signature is unchanged; the two new declarations are additions. Verdict: the target interface is preserved.
2. I compiled all three modules with `lcompile.py --all`. The target proof compiles; the only remaining `sorry`s are the two named stage-3 split theorems. No definitions contain `sorry`, and no forbidden declarations were added. Verdict: compile and declaration checks pass.
3. I checked the split statements against the argument and repaired the comparison statement: it now requires the induced quasi-isomorphism from `P` to the restriction of `C`, so it is true and strictly smaller than the target. The construction statement now returns that quasi-isomorphism. Verdict: the original comparison split was too weak and has been corrected.
4. The target proof uses the construction and comparison declarations and retains the unit route through the shortening theorem. No imports were removed; the new modules use only the imports required for their signatures. Verdict: pruning and route checks pass.
5. The target DAG node now records both split declarations as proof dependencies, and both new node statements match their Lean declarations. Verdict: DAG and Lean agree.

Changed the construction output to include its induced quasi-isomorphism, added that map and proof to the comparison theorem's hypotheses, updated the target composition, synchronized the three DAG nodes, and recorded this second reading.
