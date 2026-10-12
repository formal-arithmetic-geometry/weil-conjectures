## What changed
Added the core geometric construction and stalk-bijectivity intermediate modules, and rewrote the target proof to combine them. The target declaration and signature are unchanged.

## Proved and sorry left
The target `coherent_ideal_patching_generic_embedding` is proved by a real Lean proof from two strictly smaller intermediate statements. The added declarations `coherent_ideal_patching_generic_embedding_core` and `coherent_ideal_patching_generic_embedding_stalk_bijective` remain `sorry`, with DAG nodes `lem-weil-pbc-coherent-ideal-patching-generic-embedding-core` and `lem-weil-pbc-coherent-ideal-patching-generic-embedding-stalk-bijective`.

## No longer needed
No imports or planned nodes were pruned; the target proof uses the core construction and stalk-bijectivity steps.

## Where the brief, the DAG or earlier work was wrong
The original proof plan was too large to complete directly in the allotted session, so it was decomposed into the core construction and the generic stalk argument.

## New nodes
`lem-weil-pbc-coherent-ideal-patching-generic-embedding-core` records the construction through a monomorphism, before stalk bijectivity. `lem-weil-pbc-coherent-ideal-patching-generic-embedding-stalk-bijective` records the independent final stalk argument. No change records.

## Earlier second reading (a previous round; superseded)
The target proof was checked by compiling all three modules. The target signature is unchanged; each new statement is a strict intermediate component of the construction and has its own node.

## Second reading by C4

1. Compared the delivered target module with the repository version. The target signature is byte-for-byte unchanged; only its proof and proof-only imports changed.
2. Compiled all three sandbox modules with `lcompile.py`; they compile cleanly and contain no forbidden declarations. The two split intermediate theorems remain the only `sorry`s.
3. Reviewed the split statements and nodes. The core theorem now supplies the stalk-surjectivity actually consumed by the target, and the stalk theorem combines that with monomorphy; the previously unconstrained stalk claim was repaired. Their docstrings and DAG statements agree.
4. Checked the proof route and imports. The target uses both intermediate modules, and no planned import or unit route was pruned.
5. Checked the unit metadata and target interface; the target node and `sk-thm-p1` unit remain unchanged.

Changed the core interface to expose stalk surjectivity, added that hypothesis to the stalk-bijectivity intermediate, updated the target proof, synchronized both DAG nodes, and documented this review.
