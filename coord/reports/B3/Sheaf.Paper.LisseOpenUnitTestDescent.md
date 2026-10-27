## What changed

Replaced the sole sorry in `Sheaf.Paper.LisseOpenUnitTestDescent` by an assembly from two
strict parts of its original argument. All existing public declarations, signatures,
definition bodies, and public imports are unchanged.

`ScalarTestsRegularOpenUnit` isolates the rank-one calculation: the actual scalar tests
make the specified open unit invertible on the regular module after any weakly etale base
change. It imposes no lisse-module assertion. `OpenUnitCoverDescent` isolates compatibility
of that same unit with covering restriction and joint conservativity; it concerns an
arbitrary module and has no scalar-test or local-freeness hypothesis.

Validation: after import pruning, the final all-files remote compile passed without
errors or warnings: OpenUnitCoverDescent 6.6 s, ScalarTestsRegularOpenUnit 5.5 s, and
LisseOpenUnitTestDescent 47.8 s. All three meet the 60-second per-file limit.

The original module proves propagation from rank one to finite free modules. Whiskering
the actual unit by the degree-zero single functor gives a transformation of additive
functors. `isIso_app_coconePt_of_preservesColimit` proves invertibility on each finite
biproduct, and `NatTrans.isIso_app_iff_of_iso` transports it through a finite-free
trivialization. The left derived pullback is additive via its canonical comparison to
the exact termwise pullback. Unpacking the lisse cover, composing its maps with a,
applying the rank-one result, and then applying covering descent completes the proof.

Only the item, the two new modules, and their three DAG records are changed. No shared
interface repair, consumer adaptation, deletion, new data construction, or change record
is required. Both new statements were checked against the original proof and Stacks
08FI, 0D6F and 0D6J; their full natural-language proofs accompany the declarations.

## Proved and sorry left

Original holes: 1. Closed in the item: 1, namely
`AlgebraicGeometry.ProEtale.isIso_lisse_open_unit_of_scalar_contractible_tests`.
There are zero sorries left in the assigned module.

Added holes: 2, each a named public theorem in its own new module:

- `AlgebraicGeometry.ProEtale.isIso_regular_open_unit_of_scalar_tests`
  (`lem-sfb-scalar-tests-regular-open-unit`, `Sheaf.Paper.ScalarTestsRegularOpenUnit`).
- `AlgebraicGeometry.ProEtale.isIso_open_unit_of_cover`
  (`lem-sfb-open-unit-cover-descent`, `Sheaf.Paper.OpenUnitCoverDescent`).

This is a decomposition, not a complete proof of the underlying mathematical result:
one upper hole becomes two lower holes, a net increase of one textual hole. The Lean
proof combining them is complete. The private finite-biproduct and finite-free lemmas
have complete proofs and add no holes.

The finite-biproduct argument includes `Fin 0`; it does not choose a basis or require
positive rank. The rank-one statement allows a nonaffine chart, so the definition's
possibly nonaffine trivializing cover fits without adding an affineness assumption.
For an empty open, the scalar hypothesis forces the regular coefficient sheaf to be
zero on the basis, consistent with the conclusion. The cover criterion allows the empty
cover, and both split statements include empty schemes and identity opens. The scalar hypothesis is always on weakly contractible
objects of the full X-site, never on the puncture or only on a chart's site.

## No longer needed

Removed these eight direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.CategoryTheory.SheafTensorStructure`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.AlgebraicGeometry.ProEtale.WeaklyContractibleBasis`

These dependencies remain in the proof plans of the split-off rank-one calculation and
covering descent. They are not imported by the new sorry-only modules: following the
stage-3 convention, their future proofs will import the ingredients they use. All fifteen
original planned dependencies are retained below the two new nodes; the lisse definition
and derived-functor interface also remain direct dependencies. They are moved out of the
assembly's immediate proof dependencies, not pruned from the mathematical argument.
No existing node or module is claimed globally unnecessary. No module is withdrawn.
The blueprint unit's statement and steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original eight-step plan lacks packaged Lean
statements for the derived rank-one calculation and the open-unit covering comparison;
the listed lower-level declarations supply their ingredients but not those conclusions
directly. The two new statements expose those specific unfinished steps rather than
renaming the original scalar-to-lisse theorem.

The finite-free step also needs explicit additivity of the K-flat left derived
pullback: it follows from the canonical exact comparison. Merely asking instance
synthesis for additivity of the composite did not provide it.

## New nodes

`lem-sfb-scalar-tests-regular-open-unit` is the rank-one part of original steps 1--5 and
7--8, for any open and any weakly etale base change. It is strictly restricted to the
regular module and does not perform finite-free or lisse descent. The source is the
original argument assembled from the three cited Stacks lemmas. LeanFinder, LeanSearch,
Loogle, and source searches found no existing theorem with the required condensed-ring
and specified-derived-unit signature.

`lem-sfb-open-unit-cover-descent` is the covering restriction and descent part of
original steps 1--4 and 7--8, separated from the scalar calculation. Its hypothesis
requires the units on a concrete cover, and its conclusion concerns their common base.
It can use the existing generic `condensed_cover_restriction_conservative` theorem.
It has no scalar criterion and no lisse hypothesis, so it cannot replace the assigned
theorem alone. The same searches found underived and finite-coefficient comparisons,
but no exact match for this arbitrary condensed-ring unit.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
