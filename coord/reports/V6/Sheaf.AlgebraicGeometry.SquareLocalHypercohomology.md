## What changed

Replaced the body of `AlgebraicGeometry.square_localHypercohomology` without changing
its signature or its two public imports. Its proof now constructs an augmented injective
roof, proves that its denominator is a quasi-isomorphism on every open, applies the two
roof calculations and cancels the invertible denominator.

Added `SquareResolutionRoofModels`: actual constructions of
`squareResolutionCohomologyIso` and `squareInjectiveLocalComparison`, with a proved
`squareLocalResolutionComparison_factor`. The restriction/direct-image section identities
live in `RestrictedRoofSectionModels`,
whose natural section comparison is constructed and whose auxiliary lemmas are proved.
This separates the two model computations to keep each file below the compile limit.

Added `RestrictedCoefficientNatRoof` and `RestrictedCoefficientRoof`. They prove the
classical cohomology roof calculation by restricting the given roof, building explicit
`ModuleCohomologyFMapData`, using independence of those data, and transporting from
natural to integer indices, using private proved extension-naturality and composition
helpers in `RestrictedCoefficientRoof`. The natural-indexed calculation is in a separate
module to keep elaboration within the per-file limit. Local irreducibility attributes prevent
unnecessary unfolding of the large comparison constructions. Explicit category and
resolution presentations support the proofs with transparency checking. No shared
definition was changed.

Added `SquareInjectiveRoofAction` for the remaining raw derived calculation. The item
imports it and the proved classical calculation only for their proofs. No existing
module other than the assigned item was edited, and no source-library declaration,
public import, instance or attribute was changed.

Server validation through `lcompile.py`: `RestrictedRoofSectionModels` compiled in
23.7 seconds, `SquareResolutionRoofModels` in 31.9 seconds,
`RestrictedCoefficientNatRoof` in 50.6 seconds, and `RestrictedCoefficientRoof` in
31.8 seconds, all without diagnostics. Delivery runs the final packet compilation and
mechanical checks. All new node attachments were checked against their Lean signatures.

## Proved and sorry left

Closed the original one hole in `AlgebraicGeometry.square_localHypercohomology`.
Its combining proof is complete. New proved declarations are
`AlgebraicGeometry.squareLocalResolutionComparison_factor`,
`AlgebraicGeometry.restrictedCoefficient_natRoof`, and
`AlgebraicGeometry.restrictedCoefficient_roof`, together with the two constructed
comparison isomorphisms and their private proved helpers. The item also proves private
roof existence, local-sections quasi-isomorphism, and cancellation lemmas.

Added exactly one hole: `AlgebraicGeometry.square_injectiveRoof_action`, node
`lem-weil-pbc-square-injective-roof-action`, in `SquareInjectiveRoofAction`.
Its proof body is exactly `by sorry`. All other delivered declarations have zero holes.
Thus this is a decomposition: one original hole closed, one strictly smaller hole added,
net zero holes. It is not an axiom-free proof of the original statement.

The remaining equation contains no classical cohomology, no
`moduleCohomologyFMap`, and no choices of restricted resolutions. The classical
restriction and independence argument has been proved separately. The remaining task
is specifically the action of the normalized derived square on a prescribed augmented
injective roof, with its detailed source proof in its docstring and node. The main
proof supplies roof existence and invertibility and performs the cancellation, so it
is more than an application of a renamed copy of its original statement.

Edge cases: none of the constructions requires U or V to be nonempty or q positive.
Extension by zero and `extendHomologyIso` use q in the natural indices, including zero.
No preservation of injectives by an arbitrary scheme direct image is assumed; exact
open restriction is the functor used to preserve injectives in the classical proof.

## No longer needed

No original public import was removed, and no module or declaration is withdrawn.
The original planned direct dependency `lem-sc-bounded-below-injective-resolution`
(`WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution`) is not used on
this route: the already proved natural-indexed replacement and augmentation-lifting
helpers of `ModuleCohomologyFMap` construct the roof, and Mathlib supplies K-injectivity
of the extended bounded-below injective complexes directly. This removes that local
DAG dependency; it does not claim that the source module is globally unused.

The other original proof ingredients are retained either in the proved classical
calculation or in the stated derived calculation. No other node or module is claimed
as pruned. Proof imports were restricted to those used by the delivered constructions.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no statement or hypothesis was changed. The old
plan did not materialize the restriction/direct-image and natural-to-integer section
transport calculations. Those calculations are now proved explicitly. The unresolved
derived normalization step has been separated from that completed classical argument.
The blueprint unit route and all ancestor obligations remain intact.

## New nodes

`def-weil-pbc-square-resolution-roof-models`, module `SquareResolutionRoofModels`,
records the two actual comparison constructions and their proved factorization. It has no sorry.

`def-weil-pbc-restricted-roof-section-models`, module `RestrictedRoofSectionModels`,
records the natural restriction section comparison and its private direct-image section
API. It has no sorry.

`lem-weil-pbc-restricted-coefficient-nat-roof`, module `RestrictedCoefficientNatRoof`,
records the proved natural-indexed restricted coefficient roof formula, including
construction of the data and independence of choices. It has no sorry.

`lem-weil-pbc-restricted-coefficient-roof`, module `RestrictedCoefficientRoof`, records
the proved integer-indexed formula obtained by naturality and composition of extension
comparisons. It has no sorry.

`lem-weil-pbc-square-injective-roof-action`, module `SquareInjectiveRoofAction`, records
the raw derived action on the fixed roof, the only remaining sorry of this packet.
All five nodes inherit the assigned item's chapter, unit and blueprint ancestry.
The original item's proof/dependency records were updated to match the Lean proof.
No change record is needed: no existing definition or statement was changed.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
