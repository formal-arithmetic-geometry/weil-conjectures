## What changed

Replaced the assigned theorem's hole by an explicit etale antecedent. If G is an
antecedent of the open restriction, its etale open extension is the candidate over X.
The proof composes the constructed open-extension comparison at G, the pro-etale
extension of the given antecedent isomorphism, and the open-closed kernel isomorphism.
The original signature is unchanged.

Validation: launcher compilation of all three modules passed without errors or warnings:
`CoefficientOpenExtension` in 16.4 s, `CoefficientOpenClosedKernel` in 12.0 s, and
the assigned module in 12.8 s. Each is below the 60-second file limit.

Added `CoefficientOpenExtension`, which constructs both site-composition functors and
both extension functors by Kan extension and sheafification in `max v (u+1)`. It proves
their continuity and constructs `coefficientOpenExtensionComparisonIso` by conjugating
the identity isomorphism between composite right adjoints. This file has no holes,
no existence-based data, and no coefficient finiteness assumption.

Isolated the remaining geometric step in `CoefficientOpenClosedKernel`. Its statement
identifies the actual open extension of the actual open pullback with the kernel of the
canonical closed unit. It has no etale comparison hypothesis or essential-image
conclusion. This is the Tag 09AH part of the argument; the Tag 09AF part is now complete.
The new module includes a source and full proof in words for that remaining obligation.

Updated the assigned node's proof route and added nodes for the extension construction
and kernel identification. No existing definition, statement, or public import changed.

## Proved and sorry left

Closed the hole in
`AlgebraicGeometry.ProEtale.coefficientFixed_localization_kernel_comparison`
(node `lem-pe-coefficient-fixed-kernel-comparison`) by decomposition.

Added one hole:
`AlgebraicGeometry.ProEtale.coefficientOpenClosedKernelIso`
(node `lem-pe-coefficient-open-closed-kernel`). Its entire proof is `by sorry`.

Thus one original hole is closed and one geometric hole is added: net zero holes.
This is a decomposition with the open-extension comparison fully proved, not a claim
that the remaining localization theorem has been proved. No hole remains in the
assigned module or in any definition.

The new statement was checked on empty U, empty Z, the identity open, and zero
coefficients: it reduces respectively to a zero kernel, the kernel of a map to zero,
the identity extension, and the zero module sheaf. It retains quasi-compactness of j.
A closed immersion with full image need not be an isomorphism; no such inference is used.

## No longer needed

No existing Lean import was removed and no existing module is claimed prunable globally.
The assigned proof no longer directly uses `lem-sf-proetale-open-closed-sequence` or
`lem-cbc-proetale-extension-zero-comparison` in their original module universes.
The former remains a proof dependency of the geometric kernel node; it is not pruned.
The latter is replaced on this branch by the fully constructed coefficient-sized
comparison. The old theorem and all its other users remain intact. No source-library
declaration or file was removed.

The extension construction imports `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small`
for the etale composition-continuity theorem. It does not import the old finite-universe
extension comparison, open-closed sequence, or their derived coherence modules.

## Where the brief, the DAG or earlier work was wrong

The two original declared dependencies do not instantiate at the independent module
universe `max v (u+1)`: their ModuleCat universes are tied to scheme universe `u`.
The same restriction affects the existing ringed and internal-module localization
interfaces. Merely importing them does not prove the assigned theorem. The comparison
part can nevertheless be reconstructed directly using small-site Kan extensions and
Mathlib's adjunction mates; the delivery does that in Lean.

The remaining theorem is a different structural claim, not this item's essential-image
assertion under a new name. Its source is the first half of this item's proof in words.
The final proof supplies an actual etale object and three composable isomorphisms.
The unit route through open-closed localization and extension comparison is retained.

`blueprint_refs.py ancestor lem-pe-coefficient-fixed-kernel-comparison` reports no
blueprint ancestor, because the earlier created.item chain terminates in a module name.
The new nodes therefore use the tool's null ancestor and a concrete source place;
existing blueprint metadata is preserved.

## New nodes

`lem-pe-coefficient-open-extension` records the constructed coefficient-sized open
extension functors and their proved canonical comparison, realized by
`AlgebraicGeometry.ProEtale.coefficientOpenExtensionComparisonIso` and its supporting
site functors and continuity instances in `CoefficientOpenExtension`.

`lem-pe-coefficient-open-closed-kernel` records only the geometric identification
`j_!j^*F ≅ kernel(unit_i(F))` from Tag 09AH, independently of etale origin. It is realized
by the single remaining theorem in `CoefficientOpenClosedKernel`.

No change record is required: all existing public signatures and definitions are unchanged.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
