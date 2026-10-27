## What changed

Proved `AlgebraicGeometry.Etale.affineTraceLine_localization` with its existing signature.
Tensor the normalized projective decomposition with K and use the existing unbounded proper
projection formula. The existing tensor-projection adjunct theorem identifies the first
component with the adjunct of a pullback isomorphism. Restriction along the infinity section
then gives an invertible first-coordinate map by the composite adjunction unit. Rescaling
that coordinate gives the requested normalization without computing the closed vertex by
finite direct-image composition. Push the existing open-closed triangle and transport its
open vertex using the actual exact/derived inverse-image comparison.

All proof imports are private. Added the existing tensor-projection adjunct and section
pullback coherence imports, and replaced the reordered projection-formula wrapper import
with its underlying finite proper projection theorem.

Two proved private categorical helpers record the composite-unit argument and the coordinate
rescaling. Updated the existing node's proof, proof dependencies and proof origin to match.
No public definition or statement changed, and no consumer requires adaptation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.affineTraceLine_localization`
(node `lem-amb-affine-trace-line-localization`).

Validation: the remote compiler checked the full proof in 32.4 seconds. The delivery
gate additionally enforces warning-free compilation; explicitly reference the retained
positivity hypothesis to preserve the exact existing signature without its unused-variable
warning. The required delivery checks validate the final version.

Added zero holes; zero holes remain in the item. No new nodes or split-off obligations.
Existing dependencies retain their own independent axiom status; this delivery proves the
assigned theorem from the library's declared interfaces.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: use the given normalized transport,
  not its existence theorem. Node `lem-asd-etale-finite-twist-pullback` is unnecessary here.
- `Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions`: use the actual existing
  adjunctions and their equations directly. Node
  `prop-weil-open-closed-recollement-adjunctions` is unnecessary here.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`: the theorem takes D as input;
  its construction theorem `lem-asd-ordinary-finite-p1-adjunction` is unnecessary here.
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`: use the proved underlying
  `isIso_rightDerivedLowerStarProjectionMap_of_finite` directly, followed by invertible
  signed symmetries. Node `lem-amb-proper-coproducts-projection` is unnecessary here.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`: retain the pushed
  closed vertex and normalize it by its invertible first-coordinate map. Node
  `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is unnecessary here.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  transport the open vertex directly; node `lem-pur-etale-open-derived-tensor` is unnecessary.
- `WeilConjectures.SixFunctors.Finite.Exact`: the closed direct image need not be replaced
  by its termwise model. Nodes `lemma-weil-pbc-finite-direct-image-exact` and
  `lem-weil-pbc-closed-immersion-finite` are unnecessary here.

These are local dependency removals; no module or declaration is withdrawn. Other consumers
may still need every listed node or module. The unit's affine localization and projection
formula route is retained.

## Where the brief, the DAG or earlier work was wrong

The original plan computes a specific model for the existential closed vertex B. The
statement only needs that vertex and the two normalized coordinates. Keeping the actual
pushed vertex and rescaling the first summand proves the same statement while avoiding the
finite-direct-image and general ringed-topos composition machinery. No false statement,
hollow definition, changed hypothesis or target modification was needed.

A substantial prior draft was already present in the assigned sandbox on starting this
session. It was reviewed against the live source and completed by repairing the tensor
biproduct calculation and the final triangle comparison; it was not assumed to compile.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
