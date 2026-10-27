## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.finitePerfectAdicFlatTensor_comparison`
with a complete assembly proof, keeping its signature and both public imports unchanged.
Ordinary coefficient balancing is applied degreewise, then localized using exactness.
The bounded-above flat criterion makes the algebraic level maps invertible; their
consecutive square gives the whole diagram through `NatTrans.ofOpSequence`.
Uniqueness of left derived functors identifies exact completed extension with the
selected completed derived extension and gives the cone-point comparison.

Added `Sheaf.Paper.AdicOrdinaryTensorDiagram`: actual quotient-module diagrams,
ordinary tensor complexes, the explicitly normalized adjoint-transpose level map,
its K-flat invertibility proof, and its unit equation. These constructions contain
no holes. The same-universe free flat resolution is a proved private theorem;
all data used by public definitions have public declarations.

Added `Sheaf.Paper.AdicOrdinaryTensorTransition` and
`Sheaf.Paper.FinitePerfectAdicOrdinaryCoefficientComparison` for the two remaining
steps. Neither is the original derived comparison under another name. The first
asserts only consecutive naturality of maps already constructed, for arbitrary
complexes without K-flatness. The second concerns only ordinary module sheaves,
with no complexes, bounds or derived functors.

The inverse-sequence assembly and degreewise ordinary comparison are proved
consequences in the new transition and coefficient modules respectively. This
keeps the categorical constructions independent of the scheme-specific derived
assembly and avoids repeating large elaboration contexts in the item.

Local irreducibility of `completedAdicChangeData` and `completedAdicScalar` prevents
expansion of the chosen scalar-extension witness during elaboration. This changes
no shared definition or interface. The derived uniqueness helper is a proved
private existence theorem, so no arbitrary comparison is defined as new data.
No source-library module was changed.

Validation: the three new modules compiled cleanly in 14.0, 10.0 and 17.3 seconds.
The final item module compiled cleanly in 40.3 seconds, with profiling removed.
Its original theorem signature was compared verbatim; node signatures, dependency
unions, new-node names and line widths were also checked.

## Proved and sorry left

Original holes: 1. Removed the body hole of
`AlgebraicGeometry.Scheme.finitePerfectAdicFlatTensor_comparison` by decomposition.
The item module now contains zero `sorry`s. This is a decomposition, not a net hole
reduction: one old hole closed and two strictly smaller holes added.

New proved declarations include
`AlgebraicGeometry.Scheme.adicOrdinaryTranspose_isIso`,
`AlgebraicGeometry.Scheme.adicOrdinaryTensorLevelMap_isIso`, and
`AlgebraicGeometry.Scheme.adicOrdinaryTensorLevelMap_unit`,
`AlgebraicGeometry.Scheme.adicOrdinaryTensorComplexDiagram_comparison`, and
`AlgebraicGeometry.Scheme.finitePerfectAdicTensorComplexDiagram_ordinaryComparison`.
The private helpers `algebraicFlatResolution` and `completedExactComparison` are proved too.
`adicOrdinaryTensorLevelMap` is constructed for every complex; the isomorphism
`adicOrdinaryTensorLevelComparison` uses the proved invertibility criterion,
not an arbitrary witness of existence.

Every remaining hole added by this delivery:

- `AlgebraicGeometry.Scheme.adicOrdinaryTensorLevelMap_transition`
  (`lem-weil-pbc-adic-ordinary-tensor-transition`): compatibility of the explicit
  maps with one consecutive quotient transition.
- `AlgebraicGeometry.Scheme.finitePerfectAdicOrdinaryCoefficient_comparison`
  (`lem-weil-pbc-finite-perfect-adic-ordinary-coefficient-comparison`): ordinary
  completed-extension exactness and natural quotient tensor balancing.

Both have a source and a full proof in words in their docstrings and nodes.
The constructions permit the zero complex, arbitrary ideals and zero rings;
the ordinary coefficient comparison also includes zero coefficient modules and
empty schemes. Only the original upper bound is needed by the assembly proof.

## No longer needed

No original public import was removed, and no module is withdrawn.

The proof route no longer needs these original direct proof dependencies:

- `lem-weil-pbc-independent-bounded-flat-kflat`
  (`Sheaf.Paper.BoundedFlatIndependentCoefficients`): the proof uses the ordinary
  algebraic bounded-above flat criterion, not K-flatness of realized sheaf complexes.
- `lem-weil-pbc-derived-module-scalar-adjunction`
  (`Sheaf.RingTheory.DerivedModuleScalarAdjunction`): the supplied adjunctions suffice;
  explicit representative invertibility uses the general exact-right-adjoint criterion.
- `lem-sfb-constant-realization-derived-scalar-extension`
  (`Sheaf.Paper.ConstantRealizationDerivedScalarExtension`): exact ordinary realization
  and uniqueness of left derived functors replace the derived scalar-extension mate.

These are route removals, not assertions that the modules have no other consumers.
Completed constant algebra flatness and finite reduction remain needed below the
ordinary coefficient lemma; the canonical quotient diagram remains needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or target correction was found. The original proof plan does
not directly supply the natural comparison for the actual ULift coefficient
presentation. Its finite-reduction theorem uses the larger constant-ring
presentation, so the normalization and coefficient-system identifications still
have to be carried out. The new ordinary lemma records exactly that calculation.

Objectwise quotient isomorphisms alone do not give an isomorphism of diagrams.
The proved unit-normalized level construction separates this issue from K-flat
computation; the remaining transition assertion records the precise missing square.
The exactness route also avoids proving K-flatness of the completed realization.
The unit route is unchanged: this is the completed quotient-complex comparison
before the inverse-limit argument, with no replacement of a unit-level step.

A read-only dependency audit found no cycle through any delivered node. It also
encountered the pre-existing source DAG cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`, already reachable from the
original item before this delivery; those nodes are untouched.


## New nodes

`lem-weil-pbc-adic-ordinary-tensor-levels` records the explicit algebraic maps,
their unit equation and their K-flat invertibility. Its module is
`Sheaf.Paper.AdicOrdinaryTensorDiagram` and contains no holes. The proof uses the
existing exact-right-adjoint K-flat criterion and scalar-extension preservation
of K-flat quasi-isomorphisms.

`lem-weil-pbc-adic-ordinary-tensor-transition` records only the consecutive square
for those explicit maps; it has one hole. Its mathematical proof uses the scalar
insertion equation, the quotient map's preservation of 1, exact restriction
composition and injectivity of the upper adjunction Hom bijection.

`lem-weil-pbc-finite-perfect-adic-ordinary-coefficient-comparison` records the
ordinary abelian-category calculation; it has one hole. Its proof uses completed
constant algebra flatness, finite reduction, ordinary constant realization and the
scalar-extension tensor constraint. The generic ordinary-realization and tensor
constraint nodes are used as tools for this ordinary calculation, without changing
any geometric or unit-level route.

All three nodes record LeanSearch, LeanFinder/Loogle and Mathlib grep searches.
The blueprint searches for quotient-transition and completed-constant tensor
comparisons found no matching imported blueprint node. No change record is needed:
all existing public signatures, data definitions, instances and imports are preserved.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
