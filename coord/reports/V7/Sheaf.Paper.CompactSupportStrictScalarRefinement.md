## What changed

Completed `WeilConjectures.PurStrictScalar.supportRefinement_isIso` in
`Sheaf.Paper.CompactSupportStrictScalarRefinement`. Apply the existing
`refinementComparison_isIso` to the supplied origins, whisker with reduction,
and transport through `supportModel`. Two proved private helpers make the
comparison equality and conjugation explicit, avoiding kernel expansion of the
large support-model construction. Public statements and definition bodies remain
verbatim. Local irreducibility controls only proof elaboration.

Validation: the proof compiled in 19.7 seconds before removal of debugging options
and unused proof imports; the final packet is checked again by delivery.

## Proved and sorry left

Closed 1 of the original 9 holes:
`WeilConjectures.PurStrictScalar.supportRefinement_isIso`.
Added 0 holes and split off 0 statements. This is a proof, not a decomposition.

The eight remaining original holes, all attached to
`lem-pur-compact-support-strict-scalar-refinement`, are:

- `WeilConjectures.PurStrictScalar.scalar_clopen_projection`
- `WeilConjectures.PurStrictScalar.scalar_properOpen_alpha`
- `WeilConjectures.PurStrictScalar.scalar_properOpen_gamma`
- `WeilConjectures.PurStrictScalar.supportRefinementIso_coherence`
- `WeilConjectures.PurStrictScalar.scalar_compactification_composition`
- `WeilConjectures.PurStrictScalar.scalar_refinement_origins`
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinement`
- `WeilConjectures.PurStrictScalar.compactSupportStrictScalarRefinementCoherence`

## No longer needed

Removed these unused private proof imports:

- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.Compactification.CategoryBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`
- `Sheaf.CategoryTheory.CompactSupportRoosCofinality`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.RefinementComparisonIsomorphism`

No node or module is withdrawn. These were prospective imports for the unfinished
clauses; their mathematical dependencies remain in the node because those clauses
still need them. The completed invertibility argument needs only the existing
refinement-exchange result, already imported by this module. The unit route is
unchanged. No source-library declaration is removed or altered.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Direct componentwise conjugation elaborates
quickly but its definitional conversions expand large support-model terms during
kernel checking. Transporting a whole natural-transformation equality through a
proved generic helper avoids this expansion. The existing node's Step 8 already
cites the normalized refinement-exchange theorem used here, so no route or node
change is needed.

Change record: `coord/changes/V7-support-refinement-proof-normalization.md`.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
