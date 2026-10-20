# AlgebraicGeometry.Etale.closedConstantRestriction and proof witnesses

## Reason

Only proof terms inside these three existing declarations change. The closed-immersion instance uses an explicit `change` for the composite. The two restrictions exclude fiber-product simplification lemmas which cause excessive simplification after the proof imports are present. Each restriction still calls the identical `constantModulePushforwardMap` with the identical maps; only the proof of its equality argument changes. Proof irrelevance identifies the old and new map bodies. No public signature or mathematical definition changes.

## Old

```lean
instance intersectionSupport_isClosedImmersion {C D X : Scheme.{u}}
    (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (intersectionSupport i j) := by
  dsimp [intersectionSupport]
  infer_instance

noncomputable def closedConstantRestriction (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A i ⟶ closedConstantModule A (intersectionSupport i j) :=
  constantModulePushforwardMap A (ModuleCat.of A A) i (intersectionSupport i j)
    (pullback.fst i j) (by simp [intersectionSupport, pullback.condition])

noncomputable def closedConstantRestriction₂ (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A j ⟶ closedConstantModule A (intersectionSupport i j) :=
  constantModulePushforwardMap A (ModuleCat.of A A) j (intersectionSupport i j)
    (pullback.snd i j) (by simp [intersectionSupport, pullback.condition])
```

## New

```lean
instance intersectionSupport_isClosedImmersion {C D X : Scheme.{u}}
    (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (intersectionSupport i j) := by
  change IsClosedImmersion (pullback.fst i j ≫ i)
  infer_instance

noncomputable def closedConstantRestriction (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A i ⟶ closedConstantModule A (intersectionSupport i j) :=
  constantModulePushforwardMap A (ModuleCat.of A A) i (intersectionSupport i j)
    (pullback.fst i j) (by simp [intersectionSupport, pullback.condition,
      -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase])

noncomputable def closedConstantRestriction₂ (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A j ⟶ closedConstantModule A (intersectionSupport i j) :=
  constantModulePushforwardMap A (ModuleCat.of A A) j (intersectionSupport i j)
    (pullback.snd i j) (by simp [intersectionSupport, pullback.condition,
      -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase])
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor | U4 | Identical statements and arrows; proof witnesses simplified. |
| Sheaf.Paper.SupportedCup | unclaimed | Uses both restriction arrows; compiles unchanged against the delivery (17.6 s). |

The transitive consumers `Sheaf.Paper.PurityFramePrincipalBoundary` and `Sheaf.Paper.PurityFrameClass` also compile unchanged (23.7 s and 13.9 s). No consumer adaptation is needed.

## Status

landed 20261020T233227-L-908718 2026-10-20 (merge of deliver/U4/Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor)
