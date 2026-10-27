## What changed

Proved `AlgebraicGeometry.Scheme.relativeFiniteModelSliceEquivalence` in
`lean/Sheaf/Paper/RelativeFiniteModelSliceEquivalence.lean`, preserving its signature.
Added the proof-only import `Sheaf.CategoryTheory.NativeRingedRestrictionSlices`.
The existing proved `sliceDense`, `sliceModulesEquivalence`, and
`restrictModules_standardIso` supply module transport on the corresponding slices.
A proved private helper establishes that scalar restriction along a ring-sheaf
isomorphism is an equivalence using Mathlib's `pushforwardPushforwardEquivalence`.
The composite agrees definitionally with the displayed transport, and `mapIso` and
`preimageIso` prove the two directions. Updated the item's own DAG proof and
proof dependencies to record these steps. No other existing module or node changes.

The single-file server compile passed in 8.0 seconds. The statement imposes no
nonempty-object, nonzero-ring, finite-module, or nonzero-module assumption; the
categorical equivalences apply unchanged in these edge cases and on every slice.

Searches: LeanFinder for equivalences of module sheaves on slice sites returned
sheaf-equivalence APIs but no exact project statement. Loogle for
`"pushforwardPushforwardEquivalence"` found the module-sheaf equivalence and its
component equations. The prescribed grep search and local `rg` found the already
proved `NativeRingedRestrictionSlices` specialization used here. The source
ring-isomorphism scalar-restriction argument in `RelativeFiniteCoefficientTransport`
was reused privately because that helper is private to its module.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.relativeFiniteModelSliceEquivalence`
(node `lem-weil-pbc-relative-finite-model-slice-equivalence`).

Holes closed: 1. Holes added: 0. Split off: 0. Holes remaining in the item: 0.
The new private helper `isoRestriction_isEquivalence` is fully proved.

## No longer needed

None. No imports were removed. The original coefficient-transport dependency
remains needed for the actual coefficient isomorphism and the transport definition.
No existing node or module is withdrawn. The proof uses already proved generic
slice-restriction tools instead of introducing another slice-equivalence obligation.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is valid; its generic slice-equivalence step already has
proved Lean declarations in `NativeRingedRestrictionSlices`, which the original
node did not name. These are categorical tools and do not replace any step of the
proper-base-change unit route. No statement or definition repair was necessary.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
