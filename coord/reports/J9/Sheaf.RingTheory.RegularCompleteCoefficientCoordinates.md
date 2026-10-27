## What changed

Proved `IsLocalRing.exists_ringEquiv_regular_complete_coefficients` in
`Sheaf.RingTheory.RegularCompleteCoefficientCoordinates`, preserving its complete signature,
public imports, and docstring. The proof constructs evaluation from the existing universal
property, proves its maximal-ideal image and residue surjectivity, applies completeness to
obtain surjectivity, and uses the equal finite dimensions to prove injectivity. It then proves
the comap equality for every ideal power and the separate zero-variable assertion.

Replaced the private proof import `Mathlib.RingTheory.KrullDimension.Regular` by
`Mathlib.RingTheory.KrullDimension.NonZeroDivisors`, and added the private proof import
`Mathlib.RingTheory.MvPowerSeries.Equiv` for the zero-variable equivalence.
Updated the item's DAG proof and recorded the directly used dimension bound as a Mathlib leaf.
No definitions, statement signatures, public imports, or consumer modules changed.

Validation: the complete module compiled through `lcompile.py` with exit code 0 and no
warnings (6.5 seconds). The proof covers d = 0 without a positive-dimension assumption and
covers r = 0 in the ideal-power equality. No new Lean declarations were introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`IsLocalRing.exists_ringEquiv_regular_complete_coefficients`
(node `lem-trf-regular-complete-coefficient-coordinates`).

Added 0 holes; split off 0 holes. No sorry remains in the item or is added elsewhere.
The new DAG leaf attaches an already proved Mathlib declaration, not an unproved lemma.

## No longer needed

Removed private import `Mathlib.RingTheory.KrullDimension.Regular`.
The proof no longer uses `lem-weil-pbc-dimension-quotient-nonzerodivisor`, whose exact
principal-quotient dimension equality is stronger than needed. The replacement is Mathlib's
`ringKrullDim_succ_le_of_surjective`, directly applied to the evaluation map. This also avoids
calculating the constant coefficient of a hypothetical kernel element and proving that it
lies in the source maximal ideal. No library modules are withdrawn: the pruned node and its
Mathlib module can still serve other consumers.

The source-property theorem's residue equivalence, Noetherianity and regularity conclusions,
and the universal property's truncation and uniqueness conclusions are not needed separately
by this proof. Both source modules remain necessary and imported. All other original DAG
dependencies remain used; no unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was found. The DAG's dimension argument can be
shortened to a proved Mathlib inequality, so the principal-quotient dimension equality and
constant-coefficient preliminary argument are unnecessary. The original docstring describes
the valid longer argument and is preserved.

## New nodes

`lem-trf-surjective-kernel-nonzerodivisor-dimension-drop` records the existing Mathlib theorem
`ringKrullDim_succ_le_of_surjective`: a surjective map killing a nonzerodivisor satisfies
`dim S + 1 ≤ dim R`. Its source is the complete proof in
`Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean`, lines 60–66. LeanSearch, Loogle,
and grep identified and verified the exact signature; a blueprint/DAG search found no
existing node attaching that theorem. It introduces no Lean file and no hole.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
