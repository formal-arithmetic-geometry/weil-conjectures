## What changed

Proved `AlgebraicGeometry.Scheme.closed_proper_support_locality` in
`Sheaf.AlgebraicGeometry.ClosedProperSupportLocality`, with its signature unchanged.
The proof constructs the pullback of the reduced closed immersion, identifies its
range using `Scheme.Pullback.range_snd`, and pastes pullback squares. The first
clause follows from proper base change and independence of closed structure. For
the second clause, the jointly surjective étale family defines a small étale cover,
hence an fpqc cover by `fpqcCover_of_smallEtaleCover`; independence of closed
structure and the canonical pullback isomorphisms give the hypotheses of
`isProper_of_fpqc_cover`.

Updated the theorem's proof docstring and its existing DAG node to match this
implementation. Added the proof-only import `Mathlib.AlgebraicGeometry.PullbackCarrier`.
All public imports and declaration signatures are unchanged.

Validation: single-file compilation through `lcompile.py` succeeds. Empty closed
subsets and empty covering index types need no special exclusions: the range and
cover equivalences used in the proof include these cases. The proof does not
assume a pulled-back reduced scheme remains reduced. No definitions were changed.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Scheme.closed_proper_support_locality`
(node `lem-cbc-closed-proper-support-locality`).

Proved 1 of 1 original sorries; added 0; split off 0. There are no remaining
sorries in the item module or any new delivery module. The declared dependency
`AlgebraicGeometry.isProper_of_fpqc_cover` is used as stated; its existing hole
is unchanged and is not claimed as proved here.

## No longer needed

Removed proof-only imports:
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`: already supplied
  by the public closed-subset definition import.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`: redundant re-export;
  the vanishing-ideal construction and range API are already available.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: already available from the
  retained dependencies.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: already available from the public
  closed-subset definition import.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: already publicly imported by the retained
  `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` dependency.

Removed DAG proof dependencies `lem-weil-pbc-open-fibre-product` and
`lem-weil-pbc-fibre-product-affine-spectra`. The proved Mathlib pullback range
formula supplies the entire support identification, so neither the open
restriction nor the affine tensor-product calculation is needed for this item.
These are Mathlib leaves, not additional Sheaf modules withdrawn by this delivery.
The reduced closed structure, closed immersion base change, local finite type
base change, proper base change, closed-structure independence, small étale site,
étale-to-fpqc conversion and fpqc properness descent all remain in the argument.
No top-level tool-use approval is removed.

## Where the brief, the DAG or earlier work was wrong

No incorrect mathematical statement or interface was found. The DAG's affine
calculation was unnecessary because Mathlib already proves the exact underlying
pullback range formula. The unit has no realized steps prescribed here, and its
statement and route are unchanged. No new nodes or statement repairs were needed.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
