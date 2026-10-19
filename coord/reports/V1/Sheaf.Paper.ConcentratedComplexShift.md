## What changed

Retained and revised the earlier proof attempt for
`AlgebraicGeometry.Scheme.concentratedComplexShift`. The theorem signature and the
canonical pullback definition are unchanged. The first clause uses Mathlib's
single-degree t-structure result, then normalizes the resulting isomorphism using
`singleFunctorCompHomologyFunctorIso`; full faithfulness proves uniqueness. The
second clause compares intrinsic module sheaves with fixed-scalar module sheaves,
commutes exact pullback with homology, detects vanishing on the singleton etale
cover, and descends finite local constancy by composing the trivializing covers.
All new imports are proof-only; no other library module is adapted.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.concentratedComplexShift`
(node `lem-pur-concentrated-complex-shift`). Both clauses, including the normalized
isomorphism's uniqueness, now have complete Lean proofs. Holes added: zero.
Sorries left in the item: zero. Split off: zero.

The preserved proof compiled after correcting the local additive instance. The
unused-hypothesis warning was addressed without changing the theorem signature.
The delivery dry run checks compilation and the axiom probe again.

## No longer needed

Removed proof-only imports:
- `Sheaf.CategoryTheory.TruncationTriangle`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`
- `Mathlib.Algebra.Homology.Single`
- `Mathlib.CategoryTheory.Triangulated.Triangulated`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.ProEtaleStalkConservative`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`
- `Sheaf.Paper.SfCommonStageWeilCohomology`
- `WeilConjectures.CategoryTheory.TruncationTriangle`

The earlier sandbox's `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect`
import is also removed: the proof now composes the finite-model covers directly.
Removed direct proof dependencies:
`def-weil-derived-cohomology-sheaves`, `lem-weil-pbc-truncation-cohomology`,
`lem-weil-pbc-truncation-triangle`, `lem-weil-pbc-unbounded-derived-iso-cohomology`,
`def-pur-conventions` (retained as a statement dependency),
`def-weil-derived-pullback-tensor-hom` (retained as a statement dependency),
`def-weil-pbc-proetale-site`, `def-weil-proetale-inverse-image`,
`def-weil-proetale-locally-constant-sheaf` (retained as a statement dependency),
`lem-weil-pbc-etale-cover-geometric-point-lift`, and
`lem-pur-proetale-inverse-image-stalk`.
The first three truncation tool approvals are withdrawn from the node's top-level
`tool_uses`; the exactness, cover conservativity and localization approvals remain.

The explicit truncation-triangle construction is replaced by Mathlib's
`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`, which itself uses
standard truncation. Intrinsic/fixed-scalar comparison and existing covering
descent replace the separate geometric-stalk lifting argument. The node copy records the proposed shorter proof route and its dependencies. This list concerns
the item's direct imports; it does not claim global unreachability of these modules.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had a complete-looking proof but no delivery report or node
update. The DAG planned longer explicit truncation and stalk arguments although
existing Lean infrastructure supplies their required conclusions. No statement or
definition change is necessary. The finite Tor and structural scheme hypotheses
are stronger than this proof needs and remain in the unchanged signature.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
