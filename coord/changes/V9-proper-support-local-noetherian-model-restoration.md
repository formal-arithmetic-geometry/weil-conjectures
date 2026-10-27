# AlgebraicGeometry.properSupport_local_noetherian_model

## Reason

Restore the module assigned by coord/rework.tsv from
quarantine/Sheaf/AlgebraicGeometry/ProperSupportLocalNoetherianModel.lean.
The archived proof imports two retired Sheaf modules, both now empty. Their
adopted source replacements contain the derived pullback and composition API.
Restore the complete archived statement and proof, replacing only these imports.
The item compiles against the current library in 25.1 seconds, without warnings.
No definition or theorem signature changes; no target meaning changes.

## Old

The assigned module is absent from lean/. Its archived imports are:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
```

## New

Restore the archived module at its original Lean attachment, with these imports:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

Every existing declaration, binder, universe, visibility and proof body from the
archive is preserved verbatim. The public replacement supplies the definition
used by the statement; the private replacement supplies the composition theorem
used by the proof. The quarantine archive itself is untouched.

## Users

`tools/downstream.py --allow-missing --uses properSupport_local_noetherian_model`
reports zero live downstream modules and zero live declaration users. A separate
search of quarantine finds the parent below; its call uses the exact preserved
signature and therefore needs no adaptation. The parent's separate quarantine
repair is not part of this delivery. All five existing DAG proof dependencies and
the item's Lean attachment remain intact; no withdrawal or unit-route change.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | V9 | Restored; imports redirected to adopted source API; signature and proof unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | quarantined; no live holder found | Archived caller's application is unchanged; no adaptation. |

## Status

landed 20261025T061038-L-2394762 2026-10-25 (merge of deliver/V9/Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel)
