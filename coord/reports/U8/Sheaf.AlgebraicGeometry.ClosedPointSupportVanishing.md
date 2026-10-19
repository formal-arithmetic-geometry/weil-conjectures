## What changed

Proved `AlgebraicGeometry.Etale.isZero_cohomology_of_support_subset_closedPoints`
in `Sheaf.AlgebraicGeometry.ClosedPointSupportVanishing`, with its signature and public
imports unchanged. No definitions or other modules change.

The proof uses the declared finite-support approximation, then applies the already proved
`Etale.subsingleton_H_of_isZero_upperStar` instead of reconstructing the reduced finite
scheme and its cohomology. The approximation's closed immersion makes the complement open,
and `isZero_upperStar_lowerStar_of_disjoint_range` proves the restriction vanishes.
`closedPoint_iff_residueField_trdeg_zero_and_finite` supplies separably closed residue fields.
The arbitrary-size abelian cohomology-colimit theorem proves vanishing on the full filtered
category of finitely generated subobjects. Explicit injective-resolution and plus/unbounded
derived comparisons identify this with the precise cohomology object in the statement.

Updated `dag/nodes/sec-smooth-purity/lem-kun-0f1f-vanish.json` to follow this proof.
The unit record has no realized statement or steps to bypass. The route still uses finite
support approximation, finite-support vanishing, and filtered colimits, as in Stacks 0F1F.
The zero sheaf and empty finite support are included by the finite-support theorem.

Validation: the delivered module compiles cleanly through lcompile.py (8.7 seconds).
Mathlib searches via leanfinder and loogle found no matching support-vanishing theorem;
source searches found the finite-support theorem used here. No global build was run.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isZero_cohomology_of_support_subset_closedPoints`
(node `lem-kun-0f1f-vanish`).

No sorry remains in the item; no holes or modules were added or split off.
This is a proof from existing declared dependencies, including the still-unproved
`Scheme.closedPointSheaf_filteredColimit_finiteSupport`; its existing hole is unchanged.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`: the approximation already
  supplies the required pushforward isomorphism and publicly imports this interface.
- `Mathlib.AlgebraicGeometry.Properties`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, and
  `Mathlib.AlgebraicGeometry.ResidueField`: supplied through retained imports.
- `Sheaf.Paper.FiniteCoproductCohomologyAssembly`: its separate finite-product assembly is
  replaced by the already proved finite-support acyclicity theorem.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite` and
  `WeilConjectures.SixFunctors.Finite.Exact`: no direct finite pushforward calculation remains;
  the source finite-support theorem already includes the required finite direct-image theory.
- `Sheaf.AlgebraicGeometry.LerayBounded`: the separate bounded-below Leray calculation is
  replaced by that same finite-support theorem.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`: use the
  direct abelian arbitrary-size colimit theorem in
  `WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact` and
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: no exact-functor single-object
  calculation or etale lower-shriek calculation is needed.

Original node proof dependencies no longer needed directly:
`lem-kun-04ca` (its isomorphism is supplied by approximation),
`def-pc-reduced-scheme`, `def-weil-residue-field`,
`lem-kun-03qu-sep-closed`, `lem-weil-pbc-finite-coproduct-cohomology-assembly`,
`def-weil-finite-integral-morphism`, `lemma-weil-pbc-finite-direct-image-exact`,
`lem-kun-leray-bdd`, and `def-weil-pbc-etale-cohomology` (the cohomology definition remains
in the statement; the proof uses explicit comparison nodes).
Removed the obsolete top-level tool approvals for `lem-kun-03qu-sep-closed`,
`lem-weil-pbc-finite-coproduct-cohomology-assembly`, and
`lemma-weil-pbc-finite-direct-image-exact`; retained the colimit approval.
These are local dependency removals, not a claim that their modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The DAG's detailed finite-scheme decomposition and
bounded Leray glue were unnecessary because the source library already proves their needed
finite-support consequence. Its colimit attachment names a module-valued target, but the
source library also has a direct arbitrary-size abelian formulation, which fits the full
subobject category without an additional universe assumption.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
