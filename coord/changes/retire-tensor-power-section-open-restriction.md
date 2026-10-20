# AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_open_restriction

## Reason

The queue assigns retirement of the duplicate Sheaf module. The proved upstream twin
provides the same theorem. The only signature spelling difference is that the image
equality binder hW is anonymous upstream. An exact application of the upstream theorem
type-checks against the complete original statement, including all universes and
quantifiers. No target statement or upstream file is changed.

## Old

In Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction:

```lean
theorem exists_tensorPowSection_open_restriction (X : Scheme.{u}) (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) :
    let LU := L.restrict U.ι
    let FU := F.restrict U.ι
    let sU : Γ(LU, ⊤) :=
      (L.restrictAppIso U.ι ⊤).inv (L.presheaf.map (homOfLE le_top).op s)
    ∃ N : ∀ n : ℕ, Γ(F ⊗ L.tensorPow n, U) ≃+ Γ(FU ⊗ LU.tensorPow n, ⊤),
      (∀ (n b : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)),
        N (n + b) ((mulTensorPowSection (homOfGlobalSection L s) F n b).app U t) =
          (mulTensorPowSection (homOfGlobalSection LU sU) FU n b).app ⊤ (N n t)) ∧
      ∀ (V : U.toScheme.Opens) (W : X.Opens) (hW : U.ι ''ᵁ V = W) (hWU : W ≤ U),
        ∃ T : Γ(FU, V) ≃+ Γ(F, W),
          ∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)) (z : Γ(FU, V)),
            tmulSection z (tensorPowSectionOne (homOfGlobalSection LU sU) n V) =
                (FU ⊗ LU.tensorPow n).presheaf.map (homOfLE le_top).op (N n t) ↔
              (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
                  F ⟶ (F ⊗ L.tensorPow n : X.Modules)).app W (T z) =
                (F ⊗ L.tensorPow n).presheaf.map (homOfLE hWU).op t
```

## New

The Sheaf module is withdrawn using deleted.txt, leaving no declarations. The existing
node points to WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestriction:

```lean
theorem exists_tensorPowSection_open_restriction (X : Scheme.{u}) (L F : X.Modules)
    (s : Γ(L, ⊤)) (U : X.Opens) :
    let LU := L.restrict U.ι
    let FU := F.restrict U.ι
    let sU : Γ(LU, ⊤) :=
      (L.restrictAppIso U.ι ⊤).inv (L.presheaf.map (homOfLE le_top).op s)
    ∃ N : ∀ n : ℕ, Γ(F ⊗ L.tensorPow n, U) ≃+ Γ(FU ⊗ LU.tensorPow n, ⊤),
      (∀ (n b : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)),
        N (n + b) ((mulTensorPowSection (homOfGlobalSection L s) F n b).app U t) =
          (mulTensorPowSection (homOfGlobalSection LU sU) FU n b).app ⊤ (N n t)) ∧
      ∀ (V : U.toScheme.Opens) (W : X.Opens), U.ι ''ᵁ V = W → ∀ (hWU : W ≤ U),
        ∃ T : Γ(FU, V) ≃+ Γ(F, W),
          ∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)) (z : Γ(FU, V)),
            tmulSection z (tensorPowSectionOne (homOfGlobalSection LU sU) n V) =
                (FU ⊗ LU.tensorPow n).presheaf.map (homOfLE le_top).op (N n t) ↔
              (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
                  F ⟶ (F ⊗ L.tensorPow n : X.Modules)).app W (T z) =
                (F ⊗ L.tensorPow n).presheaf.map (homOfLE hWU).op t
```

## Users

| module | group holding it | effect |
|---|---|---|
| None importing the Sheaf copy | none | No consumer adaptation is necessary. |
| WeilConjectures.AlgebraicGeometry.AffineOpenSectionFractionLocalization | unchanged | Already imports the upstream twin and uses its theorem; recompiled unchanged. |

A full source search found zero imports of the retired Sheaf module. The sole external
use of the theorem name is the upstream affine localization consumer above. All
upstream declarations, signatures, attributes, and public imports remain verbatim.

## Status

landed 20261020T144308-L-2263404 2026-10-20 (merge of deliver/V1/Sheaf.AlgebraicGeometry.TensorPowerSectionOpenRestriction)
