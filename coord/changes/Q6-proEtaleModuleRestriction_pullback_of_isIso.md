# proEtaleModuleRestriction_pullback_of_isIso

## Reason

Repair reviewer C-68837's return of head 6883735ff. The original finite theorem must
retain its published signature and axiom dependencies. Its coefficient isomorphism
comes from the proved finite-level profinite comparison. The arbitrary-ring instance
belongs only in the constructible-classicality proof that needs it. No definition or
target statement changes; the support module is unclaimed.

## Old

```lean
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Type u) [CommRing B] [Finite B]

theorem proEtaleModuleRestriction_pullback
    (F : proEtaleRingModules Y (proEtaleConstantRing Y B)) :
    Nonempty ((proEtaleModuleRestriction X B).obj (proEtaleConstantModulePullback f B F) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj
        ((proEtaleModuleRestriction Y B).obj F))
```

## New

The section variables are now f, B and CommRing B. The original theorem has its own
Finite B binder, retaining its elaborated type. The added comparison theorem assumes
invertibility of the specified coefficient map explicitly. Its proof is the original
adjunction argument; the finite theorem supplies the instance through the published
profinite coefficient theorem, without importing the holed arbitrary-ring comparison.

```lean
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Type u) [CommRing B]

theorem proEtaleModuleRestriction_pullback_of_isIso
    [IsIso (proEtaleCoefficientInverseImageMap f B)]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y B)) :
    Nonempty ((proEtaleModuleRestriction X B).obj (proEtaleConstantModulePullback f B F) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj
        ((proEtaleModuleRestriction Y B).obj F))

theorem proEtaleModuleRestriction_pullback [Finite B]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y B)) :
    Nonempty ((proEtaleModuleRestriction X B).obj (proEtaleConstantModulePullback f B F) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj
        ((proEtaleModuleRestriction Y B).obj F))
```

## Users

Direct users were checked with tools/downstream.py and declaration search. The finite
consumer and its published origin theorem are recompiled unchanged against this delivery.
The independent reader checks the axiom probe as well as compilation. The old record
coord/changes/Q6-proEtaleModuleRestriction_pullback.md is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleConstantModulePullbackEncoding | unclaimed | Add explicit-IsIso theorem; keep finite theorem and its axiom dependencies. |
| Sheaf.Paper.ProEtaleConstantModuleConstructibility | unclaimed | Unchanged; calls the original finite theorem. |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical | Q6 | Both comparison calls use the added theorem; arbitrary-ring instance imported here. |
| Sheaf.Paper.FiniteRingConstructibleSheafOrigin | unclaimed | Unchanged transitive consumer; remains free of sorryAx. |

## Status

landed 20261019T005405-L-2762980 2026-10-19 (merge of deliver/Q6/Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical)
