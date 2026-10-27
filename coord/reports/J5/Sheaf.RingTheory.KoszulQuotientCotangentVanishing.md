## What changed

Completed `Algebra.KoszulQuotientCotangent.exists_canonical_iso_and_vanishing` without
changing its signature or the existing definitions and public imports. The proof combines
concentration in degree minus one with a separately normalized identification of that
cohomology module. A private categorical lemma lifts the prescribed homology isomorphism
to the single complex, so the resulting isomorphism has precisely the original relation-cycle
normalization.

Three new modules supply the missing interfaces: `QuotientCotangentConormal` proves the
general quotient comparison using the existing naive comparison; `KoszulPolynomialSquare`
proves invertibility of the actual canonical derived multiplication from the existing
Koszul derived-quotient theorem; `KoszulCotangentConcentration` computes the polynomial
base change on a flat single complex. All new constructions have explicit data. All
helpers and the three new public theorems are proved. No source-library file is changed,
no consumer adaptation is needed, and no target statement or definition changes.

The main DAG proof and its proof dependencies now follow this argument. The unit
`sk-i-curve-zero` has no realized node at this level; its statement and route are unchanged.

## Proved and sorry left

Closed the original one hole in
`Algebra.KoszulQuotientCotangent.exists_canonical_iso_and_vanishing`.

The new proved public theorems are
`Algebra.CotangentResolution.quotient_conormal_homology`,
`Algebra.CotangentResolution.isIso_koszulPolynomialSquare`, and
`Algebra.CotangentResolution.koszul_cotangent_concentrated`.

There are zero `sorry` occurrences left in the delivered Lean modules and zero added
holes. No unfinished statement is split off. Existing dependency theorems remain as
provided by the project; this delivery proves the item from their declared interfaces.

## No longer needed

Removed the item's proof import `WeilConjectures.RingTheory.KoszulConormalBasis` and the
proof dependency and top-level tool approval `lem-sc-koszul-conormal-basis`. We never need
to identify a tensor of polynomial conormal modules with I/I² by a regular-sequence basis:
base change supplies concentration, while the arbitrary-quotient comparison supplies
H⁻¹=I/I² with its canonical normalization. This is pruning of this proof route; no
upstream declaration or module is withdrawn, and other consumers may still need it.

Removed the item's direct proof imports `Sheaf.RingTheory.KoszulDerivedQuotient` and
`Sheaf.RingTheory.CotangentFlatBaseChange`. Their results remain needed through the new
polynomial-square and concentration modules; these are relocated uses, not pruned nodes.
The polynomial augmentation theorem and cotangent resolution coherence remain needed.
During cleanup of the new modules, removed unused imports of
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful` from the conormal module,
`WeilConjectures.RingTheory.KoszulRegularSequence` from the square module (already public
through `KoszulDerivedQuotient`), and
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`,
`WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit`, and
`Mathlib.Algebra.Homology.SingleHomology` from the concentration module. The universal
counit calculation uses the existing source functor API already exposed by base change;
it does not apply the separately bundled scalar-counit theorem.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The original plan did not supply the Lean bridges from the
mixed-tensor universal derived functor to the specified scalar extension, or from an
unnormalized single-complex isomorphism to the specified relation-cycle normalization.
The new proofs supply these bridges rather than assuming their compatibility. For the
polynomial square, an arbitrary derived comparison suffices: adjunction naturality shows
that the resulting R-linear endomorphism of R/I has 1 in its image, hence is invertible.
This avoids assuming an unstated equality of two normalized derived comparison maps.

The general quotient comparison is valid without Koszul regularity. Regularity is used
only in the concentration argument. Empty sequences, the unit ideal, and zero rings
are covered by the same constructions, with no nontriviality assumptions.

## New nodes

`lem-trf-quotient-cotangent-conormal-homology` records the normalized H⁻¹ conormal
identification for an arbitrary quotient, proved in
`Sheaf.RingTheory.QuotientCotangentConormal` from the existing naive comparison.

`lem-trf-koszul-polynomial-square` records the explicit polynomial square and invertibility
of its canonical derived multiplication, proved in `Sheaf.RingTheory.KoszulPolynomialSquare`
from the existing Koszul comparison, universal derived functors, and adjunction naturality.

`lem-trf-koszul-cotangent-concentration` records the two standard t-structure bounds,
proved in `Sheaf.RingTheory.KoszulCotangentConcentration` from that square, cotangent base
change, and the free polynomial augmentation calculation. All three nodes carry complete
proofs in words, search records, and Lean attachments. No change record is required.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
