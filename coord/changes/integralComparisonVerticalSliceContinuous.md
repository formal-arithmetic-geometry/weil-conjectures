# IntegralComparisonModelProof proof context

## Reason

The proof adds universe names for its generic private product-site helpers and a local
continuity instance for vertical slices. The delivery preflight records the universe
command as a context change. No existing signature, definition, public import, notation,
or global instance registration changes.

## Old

The private-helper namespace, universe declaration, and local continuity instance were
absent in `Sheaf.Paper.IntegralComparisonRealizationModels`.

## New

The added private helpers use the following universes inside their namespace:

```lean
namespace IntegralComparisonModelProof
universe j c hj hc r w
```

Their namespace is closed before the existing public declarations. The new continuity
instance is local to the file:

```lean
private theorem integralComparisonVerticalSliceContinuous (n : ℕ) :
    (Prod.sectR n X.ProEt).IsContinuous (ProEt.topology X)
      (verticalDiagramSiteTopology ℕ X.ProEt (ProEt.topology X)) :=
  coefficientSequenceEvaluationContinuous X n

attribute [local instance] integralComparisonVerticalSliceContinuous
```

It supplies continuity to private slice/pushforward identifications. Existing public
statements and definition bodies are unchanged.

## Users

`tools/downstream.py Sheaf.Paper.IntegralComparisonRealizationModels
--uses integralComparisonSystemRestriction_isRightAdjoint` reports 697 downstream
modules and no downstream textual occurrence of that theorem. Universe commands are
lexical; the new continuity registration is local. Thus all downstream modules see the
same existing signatures, definitions and public imports, with no adaptations needed.
No target statement or definition changes, and no target meaning review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralComparisonRealizationModels | J3 | Adds private helper universes and local continuity for the completed proof. |

## Status

landed 20261019T122553-L-468787 2026-10-19 (merge of deliver/J3/Sheaf.Paper.IntegralComparisonRealizationModels)
