## What changed
Added the proof-only import `ModuleCohomologyFMapSemilinear`. The target scalar
compatibility theorem now follows by obtaining a semilinear lift and applying
`LinearMap.map_smulₛₗ`.

## Proved and sorry left
`ModuleCohomologyFMapData.map_smul` is proved. The strictly stronger intermediate
`ModuleCohomologyFMapData.map_semilinear` remains a named sorry, with node
`lem-weil-pbc-module-cohomology-fmap-semilinear-lift`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned direct component proof was not completed in this item; it is recorded
as the semilinear-lift intermediate statement.

## New nodes
`lem-weil-pbc-module-cohomology-fmap-semilinear-lift` records the semilinear lift.

## Earlier second reading (a previous round; superseded)
The semilinear lift statement is strictly stronger than the target pointwise scalar equation; the target proof applies its standard map_smul theorem.

## Second reading by N2

1. **Diff and interface:** Compared both delivered modules with the repository versions. The existing `map_smul` statement is byte-for-byte unchanged; the only item-module change is the proof-only import and proof body. The added semilinear module is a separate named intermediate and does not alter an existing interface.

2. **Proof and axioms:** Compiled all sandbox modules with `lcompile.py --all`. The target proof has no local `sorry`; the sole remaining `sorry` is the named `ModuleCohomologyFMapData.map_semilinear` theorem, whose node and source are recorded above. The target's axioms are limited to the permitted base axioms plus `sorryAx` inherited from that open intermediate.

3. **Statements and new node:** Checked the semilinear-lift statement against the use in `map_smul`: it supplies a semilinear map whose underlying function is exactly `D.map p`, so `LinearMap.map_smulₛₗ` yields the target equation. The statement is true for the documented resolution-comparison construction, has a complete source and proof plan, and is strictly more structured than the pointwise compatibility conclusion. No duplicate declaration was found in the library.

4. **Pruning and imports:** The added `ModuleCohomologyFMapSemilinear` import is plain and proof-only. No prior import or proof dependency became unused, so no pruning was possible. The target's unit route remains the `sk-thm-p1` route; the intermediate is used only below that unit level.

5. **DAG agreement:** The item node's proof now consists of obtaining the semilinear lift and applying `map_smulₛₗ`; the new node records the corresponding declaration, dependencies, source, and `split` status. The Lean declarations and DAG statements agree exactly.

Changed during this second reading: added this review section only; no Lean statements or proofs were changed.

The import/interface accounting change record is `coord/changes/map-smul-semilinear-proof.md`.
