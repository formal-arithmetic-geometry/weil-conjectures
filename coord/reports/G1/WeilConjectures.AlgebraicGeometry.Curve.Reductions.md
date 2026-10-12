## What changed

Repaired `WeilConjectures.AlgebraicGeometry.Curve.Reductions` after the landing review found that its private `shortExact_underlying` duplicated `AlgebraicGeometry.Etale.shortExact_map_forget₂` from `WeilConjectures.SixFunctors.Etale.Gabber`. Removed the duplicate helper and its private additive and finite-limit setup, imported `Gabber`, and used the existing theorem directly in `IsCurve.Assertions.of_shortExact`. Updated the node proof text and origin to record this route. The constructibility split module and node are retained unchanged.

## Proved and sorry left

`AlgebraicGeometry.IsCurve.Assertions.of_shortExact` remains fully proved. The remaining
sorries are `AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`,
`AlgebraicGeometry.IsCurve.Assertions.of_forall_isReduced`,
`AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_forall_isReduced`,
`AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_forall_lowerShriek`,
`AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_lowerShriek`,
`AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar`, and
`AlgebraicGeometry.Scheme.constructible_of_mono_noetherian` in the new split module. No new
sorry was added by this repair.

## No longer needed

The duplicate private declaration `shortExact_underlying`, its private `underlying_additive` instance, and its local finite-limit proof are no longer needed. The proof now depends on the existing `AlgebraicGeometry.Etale.shortExact_map_forget₂` theorem in `WeilConjectures.SixFunctors.Etale.Gabber`.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery re-proved a theorem already present word for word in the source library, which caused landing to reject it. The DAG proof description has been corrected to name the existing theorem. No target statement or definition was changed.

## Earlier second reading (a previous round; superseded)

A second reading confirms that `IsCurve.Assertions.of_shortExact` has the unchanged target
statement and now invokes the source theorem `Etale.shortExact_map_forget₂` rather than a duplicate.
The remaining named sorries are unchanged, and the constructibility split remains a strict
substatement used by the devissage. The unit route is retained.

## New nodes

`lem-weil-pbc-constructible-module-subobject-noetherian` remains the one new node, stated in
`lean/Sheaf/AlgebraicGeometry/ConstructibleModuleSubobjectNoetherian.lean`; its theorem is the
only newly introduced sorry and is listed above.

## Second reading by G1

1. **Statements:** compared the delivered module with the repository version. Existing
   declaration signatures, including `IsCurve.Assertions.of_shortExact`, are unchanged byte for
   byte; the new constructibility theorem is recorded by its node.
2. **Proof:** compiled both sandbox modules with `lcompile.py --all`; there are no errors,
   forbidden declarations, or sorries inside definitions. The proved devissage theorem has no
   `sorry`; the seven listed open theorems and the one split theorem are the only remaining
   sorries.
3. **Split statement:** checked the constructibility subobject statement against its source and
   searched the library for duplicates. It is a strict intermediate result and has the required
   docstring and DAG node.
4. **Pruning and route:** the proof uses the existing `Etale.shortExact_map_forget₂` and the
   generic Mathlib `ShortComplex.Exact.ab_finite`; the nonexistent finite-middle DAG dependency
   was removed. Imports are proof-only where appropriate, and the unit route remains intact.
5. **DAG agreement:** updated the devissage node's proof uses and dependencies to match the Lean
   proof, including the existing Gabber theorem and direct Mathlib finite argument.

Changed the DAG metadata as above and retained the repaired proof and constructibility split.
