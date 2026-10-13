## What changed
Repair of return X-e4651: restored the target theorem's existential binder name
`hkl` (the split theorem retains `_hkl`). The target node's `lean.statement`
already records `hkl` and now matches the Lean source exactly. Scoped
`linter.unusedVariables false` to this theorem to preserve the required unused
binder without a compiler warning. Removed
`lem-pc-fp-local-map-pair-eventually` from the defect node's `stmt_deps`,
removing the reverse dependency that made the reduction cyclic.

Added the proof-only import of `Sheaf.AlgebraicGeometry.LocalMapPairDefect`. The target theorem is proved by reducing the transport step to the strictly lower `PairDefectZero` statement and applying the proved algebraic conversion from a common-value defect to `PairCompatibility`. The defect eventuality theorem is stated with its proof hole for the quasi-compact overlap construction.

## Proved and sorry left
Proved `AlgebraicGeometry.finitePresentation_local_map_pair_eventually` from
`finitePresentation_local_map_pair_eventually_defect_zero` and
`Pseudofunctor.DescentData.pairCompatibility_of_pairDefectZero`.
The only sorry left is `AlgebraicGeometry.finitePresentation_local_map_pair_eventually_defect_zero`, node `lem-pc-fp-local-map-pair-defect-zero`.
No sorry is present in `LocalMapPairDefect`.

## No longer needed
No imports or stated proof dependencies were removed. The direct construction lemmas suggested by the earlier attempt remain encapsulated in the new defect node.

## Where the brief, the DAG or earlier work was wrong
The previous second reading incorrectly reported that the target binder was
restored: the delivered source still had `_hkl`. This repair restores `hkl`.
The defect node also incorrectly treated the upper target as a statement
dependency; that reference is now removed. The earlier review records below
precede this return and do not certify this repair.

The earlier attempt stopped before writing the planned reduction. The hard overlap construction is now isolated as a strictly lower common-value defect theorem, while the target-level assembly is complete.

## New nodes
`lem-pc-fp-local-map-pair-defect-zero`: eventual common-value vanishing of the pairwise overlap defect, stated by `finitePresentation_local_map_pair_eventually_defect_zero` in the target module.

`def-pc-local-map-pair-defect-zero`: direct common-value defect definition and conversion theorem in `Sheaf.AlgebraicGeometry.LocalMapPairDefect`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module with the repository version. The existing target
   signature is unchanged; the only interface addition is the explicitly reported split
   theorem and its new defect module.
2. Compiled all sandbox modules. The target proof has no `sorry`; the sole remaining
   `sorry` is the named defect theorem, with its source, docstring, and node. No forbidden
   declarations or hollow definitions occur.
3. The defect statement is a strict reduction to common-value equality, and the conversion
   theorem is algebraically valid by transitivity. Both are needed for the target proof.
4. The proof follows the unit route: finite-presentation eventual vanishing is isolated on
   the pairwise overlap, then converted to pair compatibility. No shorter available theorem
   was found, and the proof-only defect import is private.
5. The target node's proof dependency is updated by the new defect node; the unit route and
   target statement remain unchanged.

Kept the defect import public because `PairDefectZero` occurs in the split theorem's public
signature, and wrapped the proof to satisfy the module style limits. No statements or
definitions were otherwise changed.

Change record: `coord/changes/finitePresentation_local_map_pair_eventually.md`.

## New nodes

`def-pc-local-map-pair-defect-zero` records the direct common-value defect definition and its conversion theorem in `Sheaf.AlgebraicGeometry.LocalMapPairDefect`; its node metadata and declaration record are included in the delivery.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module with the repository version. The original target theorem's elaborated statement and binder names are unchanged; the only added declaration is the explicitly reported defect reduction, and the public import is required by its public type. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`. Compilation succeeds with no errors. The target theorem is proved; the sole remaining `sorry` is the named `finitePresentation_local_map_pair_eventually_defect_zero`, and no forbidden declarations or hollow definitions occur. Verdict: pass.
3. Checked the split statement and defect definition. `PairDefectZero` is a genuine common-value formulation, and the conversion theorem follows by transitivity; the eventual defect statement is strictly below the target and has the required source, docstring, and node. No duplicate library theorem was found. Verdict: pass.
4. The target proof uses the defect theorem followed by the algebraic conversion, preserving the unit route; no shorter available declaration was found. The proof-only import set is minimal for the declarations used, and no old proof dependency was removed. Verdict: pass.
5. Checked the DAG nodes against the Lean declarations and proof dependencies. The target node records the reduction through `lem-pc-fp-local-map-pair-defect-zero`, while the new nodes record their declarations and source. Verdict: pass.

Changed in this second reading: restored the original `hkl` binder name in the target theorem so the existing declaration is byte-for-byte unchanged, and added this review record.

## Second reading by J1

1. Compared the delivered target module with the repository version. The target
   theorem's signature is unchanged byte for byte, including the `hkl` binder;
   the added defect theorem and defect module are recorded as new declarations.
   Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`; compilation
   succeeds. The only remaining `sorry` is the named
   `finitePresentation_local_map_pair_eventually_defect_zero`. No forbidden
   declarations or hollow definitions occur. Verdict: pass.
3. Checked `PairDefectZero` and its conversion theorem. The definition states
   existence of a common value for the two composites, and the conversion is
   exactly transitivity, hence true and strictly sufficient. The eventual
   defect statement is strictly below the target and has its node and source.
   Verdict: pass.
4. Checked the proof route and imports. The target invokes the defect theorem
   and then `pairCompatibility_of_pairDefectZero`, preserving the unit route;
   no shorter available declaration was found. The public defect import is
   required because the split theorem exposes `PairDefectZero` in its type.
   Verdict: pass.
5. Checked the DAG nodes against the Lean declarations and proof dependencies.
   The target node records both reduction steps, and the two new nodes record
   their declarations, sources, and split status. Verdict: pass.

Changed in this second reading: added this explicit review section and retained
the restored `hkl` binder and corrected defect-node dependency.
