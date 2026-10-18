## What changed

Proved the existing theorem
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE`
without changing its signature or the compactification definition. The existing source theorem
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt`
already states the amplitude bound at all separably closed field-valued points. The new Lean
argument factors each such point through its residue field and uses field-extension dimension
preservation twice to obtain that hypothesis from the canonical algebraic-closure fibre bounds.
It then transports the result to the specified compactification using the bounded-below
comparison on F[0], followed by homologyFunctor.mapIso and IsZero.of_iso.

Added three private proof imports: FieldBaseChangeDimension, the source
Derived.Finiteness.CohomologicalDimension, and Derived.LowerShriekIndependence. All public
imports and declaration signatures are unchanged. Updated the existing node's proof route and
mixed Lean record to identify the pre-existing source realization of the same blueprint node.
No new module, theorem, node, or change record is needed.

## Proved and sorry left

Closed the sole local hole:
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE`
(node `lem-dg-compact-support-amplitude`). The item has zero direct sorries remaining.
Holes closed: 1 of 1. Holes added: 0. Split off: 0.

The proof reuses the pre-existing sorry in
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt`
(`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension`), which realizes
this same blueprint node and is on the upstream hold `bundle/sec-smooth-purity-d5` in
coord/queue.md. This delivery does not prove that remaining source amplitude argument or
remove its sorry dependency. It proves the nontrivial dimension-hypothesis and compactification
interface bridges to the existing declaration. No new lower obligation is manufactured.

## No longer needed

Removed direct private proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Sheaf.AlgebraicGeometry.GeometricFiberFinite`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstantStalk`
- `Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget`
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Mathlib.AlgebraicGeometry.Properties`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.GeometricStalkSupport`

These are unnecessary as direct imports in the wrapper. The nine-step compactification,
proper-base-change, closed-support and torsion-dimension argument remains needed by the
pre-existing source amplitude theorem; it is not claimed pruned. The DAG keeps those proof
steps and dependencies, and records their realization in that source theorem. Consequently no
mathematical dependency node is claimed globally unnecessary. All retained public imports
remain because changing the public import interface is outside this proof-only change.

## Where the brief, the DAG or earlier work was wrong

The old searches missed the existing source realization of the same blueprint lemma in
Derived.Finiteness.CohomologicalDimension. Its hypothesis asks for bounds at all separably
closed field-valued points, while this item's hypothesis uses canonical algebraic closures.
These agree for the finite-type morphism by dimension preservation under field extension;
the Lean proof now establishes the conversion explicitly. The source declaration still has a
sorry, as the stage allows for existing dependency statements; its upstream-held module was
neither edited nor duplicated. The exact blueprint unit has no realized statement or steps to
bypass (dag/units/sk-prop-sf-cbc.json has empty realized lists).

Edge cases: field-extension dimension preservation includes the empty scheme, so the bridge
needs no nonempty-fibre hypothesis. The field-valued point need only be separably closed,
since dimension preservation works for every field extension. No constructibility, finite-stalk,
or bound on the whole compactified fibre was introduced. The existing finite-ring and
invertible-exponent hypotheses are retained exactly.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
