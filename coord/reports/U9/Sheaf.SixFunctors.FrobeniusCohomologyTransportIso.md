## What changed

Proved the quotient-construction part of
`WeilConjectures.frobeniusCohomologyQbarFunctor_existsUnique` from the strictly
smaller coefficient-enlargement equality
`WeilConjectures.frobeniusCohomologyRealization_transport`.
The private `representativeDescent` constructs the arrow map with `Quotient.lift`,
proves well-definedness under eventual equality, preserves identities and
composition, and proves uniqueness by Pair hom induction and `Functor.hext`.

Moved fourteen existing scalar and realization declarations, with their names,
signatures, definition bodies and proved theorem bodies unchanged, to
`Sheaf.SixFunctors.FrobeniusCohomologyRealization`. The item publicly re-exports
this prerequisite. This lets the independent coefficient-transport statement
refer to the actual maps without importing its own consumer. The new statement
is in `Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport`, imported only
for the item's proof. This refactor addresses an import cycle; it was made
before any compilation, not as a response to a compile-time limit.

The change record is
`coord/changes/U9-frobenius-cohomology-realization-dependency.md`.
The target signatures and all existing mathematical definitions are unchanged.
The unit route is retained. No source-library module is changed.

## Proved and sorry left

Original holes: 3. Closed original body:
`WeilConjectures.frobeniusCohomologyQbarFunctor_existsUnique`
(node `lem-weil-frobenius-cohomology-transport-iso`). Its construction and functor
laws are proved, conditional on the new pre-quotient coefficient equality.
This is one decomposition, not a net proof: 1 original hole closed, 1 hole added,
net 0. The private generic quotient lemma is fully proved.

Untouched original holes, both on node
`lem-weil-frobenius-cohomology-transport-iso`:

- `WeilConjectures.frobeniusCohomologyTransport_isIso`.
- `WeilConjectures.frobeniusCohomologyTransport_natural`.

One added hole:

- `WeilConjectures.frobeniusCohomologyRealization_transport`, node
  `lem-weil-frobenius-cohomology-realization-transport`. It asserts equality of
  two explicitly specified arrows at two coefficient stages. It asserts no
  quotient functor, functor laws, uniqueness, or Frobenius invertibility. Its
  docstring gives the coefficient-tower/naturality argument and checks repeated
  stages and zero objects.

There are 3 actual theorem holes in the delivery; none is in a definition.
The realization prerequisite has 0 holes.

## No longer needed

Removed the duplicate direct public imports from the parent:
`Sheaf.Paper.FiniteFieldFiber`,
`Sheaf.AlgebraicGeometry.FrobeniusDetailed`,
`Sheaf.SixFunctors.FrobeniusCohomologyTransport`,
`Sheaf.Paper.FieldDerivedScalarTower`,
`Sheaf.Paper.FiniteCoefficientPoint`,
`Sheaf.Paper.DerivedPullbackTensorHom`,
`Sheaf.Paper.SfCommonStageDirectImage`,
`Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`,
`Sheaf.Paper.CommonStageCompactWeilCohomology`, and
`WeilConjectures.Compactification.RefinementCategory`.
All remain publicly available through the realization prerequisite. The private
`Mathlib.LinearAlgebra.TensorProduct.Tower` proof import moves with its proof.
No mathematical module or DAG dependency is pruned: the declared point-inverse
and exchange-inverse dependencies remain needed by the two untouched holes.
The original coefficient-localization proof steps now belong to the realization
data node, which the parent uses.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan omitted an independently stated
coefficient-enlargement equality needed to descend the precise normalized
representative formula to the actual quotient. The delivery exposes this
missing step and proves the subsequent quotient argument. Existing operation
`stageBeta_coherence` concerns operation-stage targets; it does not itself state
the scalar-and-size point realization equality in D(Omega).

The blueprint-reference search found no duplicate for the cohomology realization
formula; the generic common-stage calculus provides the quotient API used here.
Mathlib searches found scalar-extension associativity and isomorphism
cancellation, but no theorem about these specified derived operation and
point-fibre composites.

## New nodes

`def-weil-frobenius-cohomology-realization-data` owns the fourteen relocated,
unchanged coefficient-realization declarations. It records the canonical stage
functor, the normalized comparison, and the already proved scalar-localization
and tensor-tower steps. It introduces no new mathematical construction.

`lem-weil-frobenius-cohomology-realization-transport` is the single new
coefficient-enlargement obligation. It is strictly part of the original descent
argument: the parent must additionally construct the quotient map and prove its
laws and uniqueness, all of which are proved in Lean in this delivery. The
source is Deligne Weil II (1.1.10)--(1.1.14) and the parent's coefficient descent
step. The change record is
`coord/changes/U9-frobenius-cohomology-realization-dependency.md`.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
