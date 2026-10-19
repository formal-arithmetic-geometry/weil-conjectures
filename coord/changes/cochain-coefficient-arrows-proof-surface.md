# Private proof surface in CochainCoefficientArrows

## Reason

The module now contains private, fully proved construction lemmas needed to prove
four existing theorem obligations. The delivery gate conservatively classifies the
additional scoped universes, sections, and private declarations as a change to the
static command surface. This record documents that change; no public declaration,
definition, signature, visibility, or import is changed.

## Old

`Sheaf.SecSmoothPurity.CochainCoefficientArrows` contained the existing public
coefficient-arrow declarations and five theorem obligations, all left as `sorry`; it had no private tensor-adjunction or total-complex
calculation helpers.

## New

The module contains private proved helpers for the sectionwise tensor/restriction
Hom equivalence, its adjunction and naturality, and the signed total-complex
component calculation. It also has a local generic universe section for the latter.
These commands are private or scoped to the proof and introduce no downstream
names or instances.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` | Y3 | imports the module; public API and all referenced declarations are unchanged |

## Status

landed 20261019T002510-L-2142261 2026-10-19 (merge of deliver/B8/Sheaf.SecSmoothPurity.CochainCoefficientArrows)
