## What changed

Replaced the hole in `continuousFiniteEtaleLattice_sheet_matrices` by a complete
combination of geometric refinement, forward frame coordinates, and an analytic
range argument. The original proposition and all original public imports stay unchanged. The unused
existential proof binder `w` is renamed `_w` to satisfy the unused-binder linter;
this is only an alpha-renaming.

The geometric proof reuses the proved `exists_split_sections`, `finiteCommonCover`,
`free_standardPullback`, and `free_standard_refine` helpers from
`Sheaf.Paper.FiniteEtaleLocallyFreeModels` through a proof-only `import all`.
It constructs the point-indexed splitting cover, proves simultaneous freeness on a
finite common refinement, and preserves the section coproduct under arbitrary base
change using universal finite coproducts of schemes. The common-refinement and splitting-cover helpers
keep their member properties abstract, so the cover construction does not unfold
coefficient-module objects.

The range argument is proved directly: apply the inverse matrix to a rational
continuous vector, use pointwise membership to give it codomain in the integral
subring, and use the integral coordinate presentation to lift the resulting
continuous vector to an actual section. Matrix inverse identities prove both
inclusions. Empty bases, empty opens, and rank zero require no exclusions.

Added `Sheaf.Paper.ContinuousFreeSheetFrames`, containing only the remaining
forward-coordinate assertion for already globally free modules. Updated the item
node's proof and dependencies to match the implementation. No existing module
besides the item, and no other existing node, is changed.

Validation: `lcompile.py --all` succeeds for both modules. The item compiles in
43.4 seconds and the new frame module in 1.7 seconds, below the 60-second limit.
The first delivery check also compiled both modules (32.6 and 9.6 seconds),
but refused the unused existential-binder warning; the alpha-renaming above
removes it. No profiling or timeout options remain.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleLattice_sheet_matrices`
(node `lem-sfb-continuous-finite-etale-sheet-matrices`). The item and all its private
helpers have no `sorry`.

Added one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.continuousFreeSheet_frames`
(node `lem-sfb-continuous-free-sheet-frames`). Its proof is exactly `by sorry`.

This is a decomposition: one original hole closed, one strictly smaller hole
added, net zero holes closed. The new statement has no cover construction,
finite-etale splitting, positive-degree requirement, coproduct conclusion, or
section-range equality. It assumes the globally free modules obtained by the
proved refinement and states their forward coordinate equation. The parent proves
the missing geometric and analytic parts in Lean; it is not an application of a
renamed copy of the original statement.

## No longer needed

No module is withdrawn, and no original import is removed. The original encoding,
scalar-extension, and restriction dependencies remain needed by the free-frame
calculation; they are not claimed as pruned. The finite-etale splitting dependency
is used through the proved splitting-section helper. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was corrected. The original plan separates into a
geometric common-refinement construction, a normalized coefficient-frame
calculation, and an inverse-matrix range test. The stated encoding dependencies
provide object comparisons; their compatibility with the actual normalized sheet
map remains the substantive obligation recorded in the new frame lemma.

Direct common-cover and composed-cover proofs exceeded the kernel-checking
limit. Abstracting their member predicates separates the generic cover
construction from coefficient-module conversion; no shared definition or
compiler limit is changed.

## New nodes

`lem-sfb-continuous-free-sheet-frames` states the globally free forward-coordinate
step from the blueprint's stratified-lattice trace proof, Local computation,
paragraphs 1--2. Its module is `Sheaf.Paper.ContinuousFreeSheetFrames`. The node
includes a complete proof in words, the exact Lean statement, and searches of
Mathlib, the library, and the blueprint. `LatticePairMatrixAtBasis` concerns a
different sectionwise slice-module encoding; `IntegralContinuousPresentationMatrix`
does not supply the canonical internal sheet-map compatibility. Neither is a
duplicate of this remaining lemma. No change record is required because no
existing statement, definition, or public interface is changed.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
