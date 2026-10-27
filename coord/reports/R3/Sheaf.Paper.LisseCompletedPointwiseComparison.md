## What changed

The pointwise theorem is assembled explicitly from a normalized finite-level site
comparison and rational Hom localization. The private constructions transport finite
local bases across the coefficient isomorphism, compose the three integral equivalences,
and transport the reduction cokernels and completion limits. Their naturality and
unit/counit equations are verified. Tensor induction constructs the rational functor,
checks identity, composition and additivity, and turns the Hom bijections into full
faithfulness. The prescribed coefficient datum and coefficient isomorphism are retained.

Two new modules isolate the genuinely geometric parts of the original proof: descent
of normalized finite-free towers, and localization of Hom between completed lattices.
Scalar extension preserves finite local freeness by comparison with the ringed-site
pullback adjunction and the proved finite-free pullback theorem.

No source-library statement, definition, attribute or public import changes.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.CompletedLisse.completed_pointwise_comparison` is replaced
by the explicit assembly. This is a decomposition, not a complete proof without sorry.

Two holes are added, and are the only remaining holes in this packet:

- `AlgebraicGeometry.ProEtale.CompletedLisse.normalized_tower_site_comparison`, node
  `lem-per-normalized-tower-site-comparison`.
- `AlgebraicGeometry.ProEtale.CompletedLisse.completed_lisse_rational_hom`, node
  `lem-per-completed-lisse-rational-hom`.

Thus one original hole is closed and two strictly smaller geometric obligations remain.
There is no sorry in a definition or a private declaration. The tower witness is eliminated
inside the theorem's existence proof; the additive Hom maps are uniquely determined on
pure tensors.

## No longer needed

No original import is removed. No module is withdrawn and no unit route is bypassed.
All original geometric dependencies remain needed through the two new nodes. The assembly
uses the supplied continuous-coefficient reduction datum directly, including its quotient,
completion and projection properties; it does not construct that datum again. The new
proof imports include the scalar-naturality construction and module-forgetful preservation
results. No global-lattice existence theorem or idempotent completion is needed.

## Where the brief, the DAG or earlier work was wrong

The mathematical route is unchanged. The existing finite-level site comparisons do not
immediately apply as one Lean equivalence to the normalized tower categories used here:
constant-ring module structures, geometric-stalk freeness, and the descended transition
maps must be reconciled. Similarly the bounded-continuity declaration does not itself state
the scalar-compatible Hom map for the recorded raw rational category. These are the two
remaining obligations; their source arguments and edge cases (empty charts, rank zero,
and varying local rank) are retained in the new docstrings and nodes.

## New nodes

`lem-per-normalized-tower-site-comparison` records the equivalence of continuous finite
quotient towers with the recorded etale systems, retaining an isomorphism of their actual
abelian diagrams and every integral scalar map. It is steps 2–3 of the original argument,
without integral reconstruction or rational realization.

`lem-per-completed-lisse-rational-hom` records the pure-tensor Hom bijection under actual scalar extension for a supplied integral comparison. It is steps
5–6 of the original argument, without tower descent or construction of that comparison.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
