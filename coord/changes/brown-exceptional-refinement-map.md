# brownCompactificationRefinementMap

## Reason

The definition duplicated `compactificationRefinementComponent` while using a propositionally equal final equality morphism. That duplication caused dependent elaboration to unfold the full derived-category construction during the normalization proof and exceed the heartbeat limit. The existing canonical refinement component has exactly the same source, target, and formula, so the definition now delegates to it. The coherence-cocycle module is public-imported because the definition's public body names this existing declaration.

## Old

`brownCompactificationRefinementMap` was the explicit three-factor composite of the right-derived lower-star map, the inverse derived compositor, and an `eqToHom` term.

## New

`brownCompactificationRefinementMap Λ r K := compactificationRefinementComponent Λ r K`. The theorem's public type and mathematical meaning are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.BrownExceptionalAdjoint | G3 | Uses the canonical component directly in the normalization proof. |

## Status

landed 20261019T192737-L-1862058 2026-10-19 (merge of deliver/G3/Sheaf.Paper.BrownExceptionalAdjoint)
