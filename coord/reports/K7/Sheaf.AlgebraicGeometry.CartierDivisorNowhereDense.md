## What changed

Proved `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.compl_support_dense`
in `Sheaf.AlgebraicGeometry.CartierDivisorNowhereDense`, preserving its complete signature.
On a point-indexed affine cover the complement is a basic open, hence its inverse image
is compact. Quasi-compactness glues by `IsZariskiLocalAtTarget.of_iSup_eq_top`.
The existing proved `IsInvertible.isSchemeTheoreticallyDominant_compl_support` in
`WeilConjectures.Blowup.Density` supplies scheme-theoretic dominance. Mathlib then gives
dense range; density contradicts any nonempty open contained in the support.
Added only a private proof import of `WeilConjectures.Blowup.Density`; public imports
and all declarations and definitions retain their interfaces. Updated the item's DAG proof.

The single-file server compile passes without warnings (2.3 seconds). The proof handles
the empty scheme and the unit ideal: no nonemptiness or proper-support assumption is used.
Mathlib searches via LeanFinder, Loogle, LeanSearch and grep found the local compactness
API; source grep found the exact scheme-theoretic dominance theorem.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.compl_support_dense`
(node `lem-pc-cartier-divisor-nowhere-dense`). Zero holes remain in the item. Zero holes
added; zero statements split off. The new node attaches an existing completely proved
source theorem; no new Lean declaration or module is introduced.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.AffineNonZeroDivisorComplementDense` and
`WeilConjectures.Blowup.BlowupUniversal`. Their declarations are not directly used by this
proof. The item's proof no longer depends on nodes
`lem-pc-affine-nonzerodivisor-complement-dense` or
`lem-pc-localization-preserves-nonzerodivisor`: the source theorem already proves global
scheme-theoretic dominance, and local compactness only requires a principal generator.
No upstream declaration or module is withdrawn. `BlowupUniversal` can still be reached
transitively through source imports; no claim is made that it leaves the target closure.
The unit's own statement and realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The plan was valid but unnecessarily repeated the already proved general dominance
argument from `WeilConjectures.Blowup.Density`. Its existing theorem does not alone
prove our conjunction: quasi-compactness, topological density and the final open-set
assertion are supplied by this delivery. Existing docstrings are preserved.

## New nodes

`lem-pc-invertible-ideal-complement-schematic-dominance` records the exact existing
source theorem used in the proof, with its source, localization proof and three searches.
This is an attachment to existing Lean, not a new statement or a decomposition.
No change record is needed: no public signature, definition or public import changes.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
