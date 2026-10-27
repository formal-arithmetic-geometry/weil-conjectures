## What changed

Replaced the proof hole in `Sheaf.Paper.AdicPerfectReductionHomML` by a direct
finite-marking argument. For any triple of indices, reduce one marking from its
highest level. Composition with the three inverse markings gives a finite-triple
comparison with the fixed model's endomorphism tower. Private helpers prove that
the actual normalized Hom transitions preserve composition and identities, that
successor comparisons extend to every arrow, and that the algebraic Hom terms
are finite over the Noetherian ring.

The endomorphism tower is compared with actual quotient cohomology sections via
`Sheaf.Paper.AdicPerfectHomCohomologyComparison`. Artin--Rees and exact constant
sections are the existing proved theorems of
`Sheaf.Algebra.Homology.AdicShortComplexCohomologyML`. The existing proved
`Sheaf.CategoryTheory.FiniteTripleMittagLeffler` transfers stable images twice.
The original public theorem signature, including all hypotheses, is unchanged.

## Proved and sorry left

Original holes: 1. Its body is now proved from the named comparison theorem:
`AlgebraicGeometry.Scheme.adicResidueHomTower_mittagLeffler`
(node `lem-sfb-adic-perfect-reduction-hom-ml`). No sorry remains in the item module.

Added holes: 1, in
`AlgebraicGeometry.Scheme.adicPerfectHomCohomologyComparison`
(node `lem-sfb-adic-perfect-hom-cohomology-comparison`). This is a decomposition,
not a net hole closure: one upper hole is closed and one strictly smaller
comparison obligation is added. It concerns two fixed constant perfect complexes,
asserts explicit cohomology bijections and successor compatibility, and contains
no Mittag--Leffler assertion, arbitrary varying target, Noetherian hypothesis or
completeness hypothesis. Its source and complete proof in words are in the
module and node. No definition contains a hole.

## No longer needed

The proof no longer needs the complete internal-Hom construction, product/Roos
commutation or reconstruction of an internal-Hom object from its reductions.
Consequently the following original proof dependencies are absent from the
item's proof route:

- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, module
  `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `lem-sfb-wcontractible-constant-reductions-ml`, module
  `Sheaf.Paper.WContractibleConstantReductionsML`.

The original `lem-pc-kflat-closure`, `lem-pur-derived-change-of-rings`,
`lem-sc-bounded-above-projective-kprojective`,
`lem-coef-kprojective-derived-hom-bijection`,
`lem-weil-pbc-proetale-weakly-contractible-evaluation-exact`, and
`lem-weil-pbc-constant-completion-equivalence` are no longer direct dependencies
of the item, but remain dependencies of the new fixed-model comparison. They
are not claimed pruned from the target closure. The complete equivalence itself
is stronger than the new lemma needs; its quotient normalization and K-flat
extension calculations still apply.

Removed redundant direct proof imports of `WeilConjectures.Algebra.Homology.ModuleHomComplex`
and `Mathlib.RingTheory.Noetherian.Basic`; the comparison module already provides
their required declarations. The two original public imports are preserved. None of the old proof-dependency
modules was imported by the initial item. No module is withdrawn or deleted;
other consumers may still need every dependency listed here.

## Where the brief, the DAG or earlier work was wrong

The original route was valid but unnecessary for this stronger hypothesis: every
finite reduction of M is individually isomorphic to the same fixed perfect
model. A marking at the highest of finitely many levels supplies all lower
markings required for a comparison of images. Artin--Rees may therefore be
applied directly to the fixed algebraic endomorphism complex. Completeness of M
and affineness of U are unused; their binders remain verbatim.

The unit route is unchanged: this is a calculation below the local-perfect-lift
step of `sk-lem-integral-models`, with the same completed-coefficient models and
normalized quotient transitions. The edge cases checked mathematically are the
empty slice, zero complex, empty support interval, unit ideal, zero ring, and
repeated indices; the source-zero argument and identity-map induction include
them. No finite underlying quotient set or compatible infinite marking is
assumed.

## New nodes

`def-sfb-adic-perfect-hom-cohomology-tower` records the actual quotient short
complex of the existing algebraic Hom complex, followed by constant-module
sections. Its construction uses no unproved existence or arbitrary chosen data.

`lem-sfb-adic-perfect-hom-cohomology-comparison` records precisely the fixed-model
Hom/cohomology comparison, including the successor equation for the existing
scalar-reassociation conjugations. Stacks Tags 09C5 and 09C6 give the calculation;
the docstring expands the K-flat reduction, projectivity on the weakly
contractible slice, finite-projective Hom and quotient-compatibility steps.
The Mathlib searches are recorded from actual msearch runs. The blueprint
searches for "perfect Hom" and "Hom complex" found no duplicate statement.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
