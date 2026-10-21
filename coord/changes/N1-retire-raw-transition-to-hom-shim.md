# Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom

## Reason

The assigned queue row in coord/queue.tsv is `retire`. The corresponding row in
coord/retire-items.tsv explicitly requests replacement by
`WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHom`.
The reviewed D2 canonicalization already changed the Sheaf module to a declaration-free
public re-export and attached its DAG node to the canonical upstream theorem.
This delivery completes that retirement against the current source.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHom

/-! # Raw pullback and the derived-Hom comparison

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical comparison maps.
(blueprint: sbc-lem-higher-image-raw-transition-to-hom).
-/

@[expose] public section
```

## New

Withdraw the redundant Sheaf shim through deleted.txt. The delivery tool lands an
empty module at this path. The upstream theorem
`AlgebraicGeometry.Etale.higherDirectImageRawTransition_toHom`, its complete proof,
its signatures and public imports are preserved verbatim.

The node sbc-lem-higher-image-raw-transition-to-hom continues to name the upstream
module and theorem. Only its lean.note is updated to explain retirement of the shim.
Its parent sbc-lem-higher-image-raw-over-comparison still depends on this theorem:
the actual upstream consumer imports the upstream module directly and applies the theorem.
No mathematical dependency or unit step is removed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality | unclaimed locally | Historical inventory consumer; current source re-exports its upstream twin directly, so no adaptation. |
| WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality | unclaimed locally | Actual theorem consumer; already imports the canonical upstream theorem directly, so no adaptation. |

A search of all current lean/ sources finds no imports of the retired Sheaf shim.
The read-only tools/downstream.py invocation, including --uses
higherDirectImageRawTransition_toHom, reports zero downstream modules and zero uses
through this shim. The consumer's complete comparison proof and the upstream theorem
remain in place. No changed definition, signature, attribute or target requires adaptation.
No forced adaptations are needed.

The owning unit sk-lem-failure-field has empty realized.statement and realized.steps
entries; no unit route requires this Sheaf path. The only live parent node is
sbc-lem-higher-image-raw-over-comparison, attached to the canonical upstream consumer.
There is no matching coord/rework.tsv quarantine entry or current N1 return for this item.
Thus the explicit retirement request agrees with the current Lean and DAG source;
this is retirement of a redundant path, not withdrawal of a mathematical statement.

## Status

landed 20261021T012413-L-2186024 2026-10-21 (merge of deliver/N1/Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom)
