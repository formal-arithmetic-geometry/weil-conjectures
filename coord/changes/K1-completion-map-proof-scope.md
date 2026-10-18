# Sheaf.Paper.CompletionMap proof scopes

## Reason

The stage-3 preflight conservatively requests a change record for additional `open`
commands. The proofs use the pretriangulated namespace and tensor/change-of-rings
notation. Declaration-local elaboration options assist the existing augmentation
and tower-map proofs and the new private, proved mapping-cocone helper.

These commands select names, notation and elaboration behavior within this module.
They introduce no exported notation, instance, attribute or declaration. All 26
existing signatures, all existing definition bodies, all existing declaration
visibility, and every public import are unchanged. The two new helper theorems
are private and have complete proofs. Theorem proofs and private proof imports
are the only other Lean changes.

No target statement or definition meaning changes. No target statement review
is reopened. There are no forced adaptations.

## Old

Original opening commands, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits
```

There were no declaration-local elaboration option prefixes at the affected proofs.
The variable and universe commands are unchanged.

## New

Delivered opening commands, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct ChangeOfRings
```

The following declaration-local prefix is used immediately before the unchanged
existing docstrings and signatures of `adicReductionAugmentation_exists` and
`adicCompletionTowerMap_exists`:

```lean
set_option backward.isDefEq.respectTransparency false in
```

The new private helper `mappingCoconeMap_exists` uses these declaration-local prefixes:

```lean
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

There are no development profiler options, temporary checkpoint declarations,
or heartbeat-limit changes in the delivered file.

## Users

`tools/downstream.py Sheaf.Paper.CompletionMap` lists exactly the two downstream
modules below. Their source was reviewed: AdicCompletionReduction uses the existing
quotient augmentations, projections, completion objects and strict tower maps;
KoszulQuotientLimit uses the same objects and both coordinate formulas. All these
signatures and definitions are unchanged. Neither consumer is edited. Holders were
read using the project's read-only `stage3_delivery.claim_holder` helper.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicCompletionReduction | J3 | Identical public API and definition bodies; no adaptation. |
| Sheaf.Paper.KoszulQuotientLimit | Y2 | Identical public API and coordinate formulas; no adaptation. |

## Status

landed 20261018T062820-L-659255 2026-10-18 (merge of deliver/K1/Sheaf.Paper.CompletionMap)
