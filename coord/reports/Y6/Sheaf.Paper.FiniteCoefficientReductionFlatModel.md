## What changed

Filled both proofs in `Sheaf.Paper.FiniteCoefficientReductionFlatModel`, preserving every
existing declaration signature, definition body, public import, and docstring.

The pro-etale proof uses bounded-above flat K-flatness and the existing independent-universe
change-of-rings theorem. The chosen universal counit's K-flat component produces the model
isomorphism. The public ringed tensor-with-single comparison identifies every K-flat representative
with the published derived site tensor. The single-factor total comparison then reduces
vanishing to the unchanged support interval of the actual model, proving the original
universal resolution-based Tor predicate.
The original amplitude assumption is used only for its ordered-interval clause.

The etale proof checks reduced-term flatness on geometric stalks using ordinary module base
change. An explicit natural isomorphism between scalar extension followed by restriction and
tensor with the constant target ring is lifted to complexes and localized. The existing
bounded-flat derived tensor comparison and Tor theorem complete the proof. In particular,
no flatness of the quotient ring map is asserted or used.

Added only private proof imports and updated the item's DAG proof and dependencies to this
argument. Added proved private helpers for bounded-flat Tor amplitude, flat scalar extension, and
localization comparisons; no new public declarations, nodes, definition changes, or consumer adaptations.
Local irreducibility attributes keep existing localization, scalar extension, and tensor constructions
abstract during elaboration; the proof uses their stated comparison APIs. The private
interfaces preserve the standard pro-etale localization and the smaller etale localization.
The etale assembly takes its functors and their additive/exact instances explicitly,
avoiding repeated structural instance search in the statement of a concrete comparison.
A local priority for `CommRing.toRing` keeps generic and lifted coefficient-ring data
consistent in the etale section; it avoids repeated kernel normalization through the
chosen ring of integers without changing any ring operation or declaration statement.
The direct generic computations use the same canonical tensor that the original predicate
uses. Edge cases checked: m=n; zero complexes; a>b (the etale support forces zero); and
arbitrary test sheaves without a flatness assumption.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Scheme.finiteCoefficient_reduction_flatModel`.
- `AlgebraicGeometry.Etale.finiteCoefficient_etale_reduction_flatModel`.

Both belong to node `lem-sf-reduction-flat-model`. Zero holes remain in the item; zero holes
are added, and zero statements are split off. This is a proof, not a decomposition.

## No longer needed

Removed these proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: supplied publicly by
  the ringed tensor-with-single comparison module.

- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: already supplied by public imports.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`: replaced with its already proved
  independent-universe version `ChangeOfRingsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: the chosen homotopy counit already
  in the item's definition gives the needed computation directly.
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`: the conclusion uses the original
  pro-etale Tor predicate and requires no small-model transport.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: the public flat-model import supplies the
  existing bounded etale predicate and its categorical comparison.
- `Sheaf.Paper.SfCommonStageWeilCohomology`: no intrinsic common-stage Weil category occurs.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`: no fixed-ring
  ModuleCat-valued pro-etale derived tensor occurs.

The proof no longer directly needs `lem-pur-kflat-change-of-rings`, replaced by
`lem-pur-kflat-change-of-rings-independent`. The fixed-ring
`def-weil-derived-tensor` proof citation is replaced by the actual
native total tensor underlying the pro-etale predicate and its ringed comparison.
No module is withdrawn; other consumers may still require the removed proof imports.

The generic tools now cited include geometric-stalk detection of etale flatness, the Mathlib
flat-module base-change leaf, independent-universe tensor comparisons, and K-flat computations. They supply auxiliary facts rather than bypassing a unit step.
The unit record has no realized statement or step removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The original `lem-pur-kflat-change-of-rings` interface fixes the coefficient universe to the
maximum of the site universes and operates on a prescribed raw change-of-rings complex.
The independent-universe version instead accepts the exact chosen functor used by this item,
including its object/map specifications, so it applies directly.

The public ringed comparison identifies the published site-derived tensor with termwise
tensor on every K-flat first factor and arbitrary degree-zero second factor. This is exactly
what connects the original pro-etale universal resolution predicate to the reduced model. The
etale ideal-quotient theorem uses a different literal target ring/functor; we preserve this
item's actual quotient-factor extension and write its tensor comparison explicitly.

No mathematical statement or definition repair was necessary. The local elaboration commands
are recorded in `coord/changes/finite-coefficient-reduction-proof-elaboration.md`, as required
by preflight. The coefficient-extension import is retained explicitly because it belongs to
the unit route, even though its declarations are also available through public imports. The compile server returned
intermittent 'no answer' responses; validation was retried without altering the tools.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
