## What changed

Completed `strictHenselizationPointedMap` by combining the two split intermediate theorems. The core and factorization declarations remain imported and stated in the same module.

## Proved and sorry left

`strictHenselizationPointedMap` is proved. `strictHenselizationPointedMap_core` remains sorry (node `lem-weil-pbc-strict-henselization-pointed-map-core`), and `strictHenselizationPointedMap_factorization` remains sorry (node `lem-weil-pbc-strict-henselization-pointed-map-factorization`).

## No longer needed

None; both split intermediate nodes are used by the completed proof.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox copy had an invalid adjacent documentation comment that prevented parsing; it was replaced with a valid block comment. No mathematical statement was changed.

## New nodes

`lem-weil-pbc-strict-henselization-pointed-map-core` and `lem-weil-pbc-strict-henselization-pointed-map-factorization` are split intermediate nodes already present in this delivery.

## Earlier second reading (a previous round; superseded)

A second worker should check that the top theorem combines the two split statements without changing its target statement, and that both intermediate statements match their declarations.

## Second reading by P1

1. Compared the delivered module with the repository version.  The existing
   target theorem's signature is byte-for-byte unchanged; only its proof and
   the two declared split intermediates were added.

2. Compiled the module and the complete sandbox with `lcompile.py`; both pass.
   The only remaining `sorry`s are the two named split theorems listed above.
   No forbidden declarations occur.  The split theorem docstrings now include
   their source and proof in words.

3. Checked both split statements against their Lean declarations and DAG nodes,
   and searched the project for duplicate declarations.  They are project
   specific and their hypotheses and conclusions match the declarations.

4. The top proof follows the stated route: obtain the map and its properties
   from `strictHenselizationPointedMap_core`, then discharge the neighbourhood
   equation with `strictHenselizationPointedMap_factorization`.  Both imports
   remain needed by the split declarations; no pruning was possible.

5. The DAG `proof`, `proof_deps`, and `proof_origin` entries agree with the
   Lean proof, and the unit `sk-thm-p1` route remains realized by the target
   node and its two split steps.

Changed only the split theorem documentation to make the required proof
sketches explicit; no mathematical statement or import was changed.
