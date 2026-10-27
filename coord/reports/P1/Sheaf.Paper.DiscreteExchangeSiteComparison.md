## What changed

Proved `AlgebraicGeometry.ProEtale.discrete_exchange_site_comparison` in
`Sheaf.Paper.DiscreteExchangeSiteComparison`, without changing its signature, any
public import, any definition, or any target. Updated its proof docstring and DAG
proof to match the implemented route.

The existing `comparison_derivedBaseChangeMap` has exactly the required canonical
comparison equality for arbitrary commutative rings. The proved
`Etale.baseChange_eq_derivedBaseChangeMapPlus` identifies the etale map appearing
there with this item's etale map. The chosen Cartesian identification supplies its
`IsPullback` premise. Its source and target natural isomorphisms are literally
those in this item's statement, including compatibility with the ambient categories.

For both etale endpoints, exact comparison preserves a cohomological lower bound.
`classicalDerivedImage` supplies classicality, with its unit premise supplied by
`boundedBelowComparison`. Plus-to-unbounded compatibility identifies the images.
Transport through the two specified endpoint isomorphisms gives all four remaining
clauses. Lower-bound transport is written using `DerivedCategory.isGE_iff` and
homology isomorphisms. Classicality transport uses
`Scheme.proEtaleFixedClassical_iso_iff`.

Added proof imports of `ClassicalDerivedImage`, `BoundedBelowProEtaleComparison`,
`ProEtaleConstantDerivedEncoding`, and `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`.
All public imports are preserved. The final file compiles cleanly through `lcompile.py`.
No change record is needed: only a theorem proof, its documentation, private proof
imports, and the matching node proof changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.discrete_exchange_site_comparison`
(node `lem-weil-pbc-discrete-exchange-site-comparison`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean file.
The exchange clause uses the existing theorem
`AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`, whose shared source
currently still has a hole. This is an existing declared dependency, not a new
statement or a claim that its proof is closed. The delivery proves this item's
assembly from existing declarations, as requested by stage 3.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageComparisonCoherence`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageMateCompatibility`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`

The original proof plan's direct dependencies
`sk-thm-pe-direct-image-comparison`,
`lem-pe-inverse-image-comparison-coherence`,
`def-weil-pbc-ambient-ringed-exchange`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-weil-pbc-localization-universal-property`,
`lem-pe-direct-image-mate-compatibility`,
`def-weil-pbc-adjunction-mate`, and
`sk-thm-pe-classical-sheaves` are no longer used directly by this proof. The
canonical transport theorem already handles the comparison equality, and the
classical-image theorem already handles cohomology of comparison pullback.
`sk-def-exchange` and `lem-weil-pbc-exact-functor-bounded-below` remain direct
proof dependencies. The DAG now names the additional existing results actually
used. No module is withdrawn: some of the removed direct dependencies remain
needed transitively or by other consumers, and public reexports are preserved.

## Where the brief, the DAG or earlier work was wrong

The seven-step proof plan repeats the canonical exchange-transport argument
already stated in `comparison_derivedBaseChangeMap`. Its Lean statement has no
finiteness premise on the coefficient ring. The current blueprint's
`lem-weil-pbc-transport-identifies-exchange.md` also explicitly allows any
commutative ring; its DAG's older prose still says finite, but its `blueprint_update`
and Lean attachment both record the arbitrary-ring statement. No statement repair
was necessary. Likewise, the classical-derived-image theorem already proves the
cohomology assertion used by the last planned step.

Checked the unit `sk-thm-properbasechange`: none of its realized statement or
proof-step nodes is bypassed or changed. Checked that the newly used existing
nodes have no dependency path back to this item. Edge cases require no extra
hypotheses: the proof applies to the zero ring, zero complex, empty schemes and
identity squares; it uses neither properness nor invertibility of either exchange.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
