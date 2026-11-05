/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle
import WeilConjectures.CategoryTheory.DerivedCategory.TelescopeFlat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# The Künneth formula in ordinary étale cohomology

This file proves the base change theorems for a pushforward tensored with a complex
(`lem-kun-0f1j`, `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_isGE`, and
`lem-kun-0f1n`, `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`) and deduces the Künneth
formula over a separably closed field (`thm-kun-0f1p`,
`AlgebraicGeometry.Etale.isIso_kunnethMap_of_isSepClosed`). The Künneth map and the inputs which
do not depend on these base change theorems are in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Inputs

/-- First step of the proof of blueprint `lem-kun-0f1j`: reduction to single sheaves.

Under the hypotheses of `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_isGE`, the base
change map `Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)` is an isomorphism provided it
is an isomorphism when `E` is a flat sheaf and `F` is a sheaf, both placed in degree `0`
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_single`). -/
theorem isIso_tensorBaseChangeMap_of_isGE_of_single [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K))
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (_sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m n : ℤ)
    (_hE : DerivedCategory.TStructure.t.IsGE E m)
    (hEt : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), q < n →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
        X).obj E).obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (hF : DerivedCategory.TStructure.t.IsGE F m)
    (hsingle : ∀ 𝓔 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), ObjectProperty.flat 𝓔 →
      ∀ 𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
        IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
          ((L((p)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓔))
          ((DerivedCategory.singleFunctor _ 0).obj 𝓕))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj E) F) :=
  have := hF
  isIso_tensorBaseChangeMap_of_single (ModuleCat.{u + 1} Λ) h e f' g sq₂.w p E F m n
    hEt hsingle

/-- Blueprint `lem-kun-0f1j`: base change for a pushforward tensored with a bounded below complex
of finite Tor amplitude.

Let `K` be a field and `Λ` a finite ring whose exponent is invertible in `K`. For a diagram

```
  X <--p-- X' <--h-- Y
  |        |         |
  a        f'        e
  v        v         v
Spec K <-b- S' <--g-- T
```

with both squares cartesian, `X` of finite type over `K` and `g` quasi-compact and quasi-separated,
the base change map (`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)`

is an isomorphism for every bounded below `E ∈ D(X_ét, Λ)` of Tor amplitude in `[n, ∞)` and every
bounded below `F ∈ D(T_ét, Λ)`.

The blueprint statement does not require `X` to be of finite type over `K`, but its proof uses
it: it applies `lem-kun-0f1i`, which is stated for schemes of finite type, to the `Xᵢ`. -/
theorem isIso_tensorBaseChangeMap_of_isGE [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (_sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m n : ℤ)
    (_hE : DerivedCategory.TStructure.t.IsGE E m)
    (_hEt : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), q < n →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (((derivedTensor (ModuleCat.{u + 1} Λ)
        X).obj E).obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (_hF : DerivedCategory.TStructure.t.IsGE F m) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj E) F) :=
  isIso_tensorBaseChangeMap_of_isGE_of_single Λ a b p f' h e g _sq₁ sq₂ E F m n _hE _hEt _hF
    (fun 𝓔 h𝓔 𝓕 ↦
      isIso_tensorBaseChangeMap_singleFunctor_of_flat Λ a b p f' h e g _sq₁ sq₂ 𝓔 h𝓔 𝓕)

variable {Λ} in
/-- Blueprint `lem-kun-0f1n`, for `E` a strictly bounded complex of flat sheaves: the
reduction of `F` to strictly bounded complexes, which are bounded below, and an application of
blueprint `lem-kun-0f1j` (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_isGE`). -/
lemma isIso_tensorBaseChangeMap_Q_obj_of_flat [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] [QuasiCompact h] [QuasiSeparated h]
    (hg : HasFiniteCohomologicalDimensionMorphism Λ g)
    (hh : HasFiniteCohomologicalDimensionMorphism Λ h)
    (sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) (m n : ℤ)
    [P.IsStrictlyGE m] [P.IsStrictlyLE n] (hP : ∀ i, ObjectProperty.flat (P.X i))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj (DerivedCategory.Q.obj P)) F) := by
  have := preservesColimitsOfShape_nat_rightDerivedLowerStar Λ g hg
  have := preservesColimitsOfShape_nat_rightDerivedLowerStar Λ h hh
  refine DerivedCategory.isIso_app_of_isIso_app_Q_obj_bounded
    (tensorBaseChangeMapRight (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj (DerivedCategory.Q.obj P))) (fun L m' _ _ _ ↦ ?_) F
  exact isIso_tensorBaseChangeMap_of_isGE Λ a b p f' h e g sq₁ sq₂ _ _ (min m m') m
    (DerivedCategory.TStructure.t.isGE_of_ge _ _ m (min_le_left _ _))
    (isZero_homology_derivedTensor_Q_obj_of_flat _ P m n hP)
    (DerivedCategory.TStructure.t.isGE_of_ge _ _ m' (min_le_right _ _))

/-- Blueprint `lem-kun-0f1n`: base change for a pushforward tensored with an arbitrary complex.

Let `K` be a field and `Λ` a finite ring whose exponent is invertible in `K`. For a diagram

```
  X <--p-- X' <--h-- Y
  |        |         |
  a        f'        e
  v        v         v
Spec K <-b- S' <--g-- T
```

of `K`-schemes of finite type with both squares cartesian, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)`

is an isomorphism for all `E ∈ D(X_ét, Λ)` and `F ∈ D(T_ét, Λ)`, unbounded. -/
theorem isIso_tensorBaseChangeMap [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) (t : T ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a] [LocallyOfFiniteType b] [QuasiCompact b]
    [LocallyOfFiniteType t] [QuasiCompact t]
    (p : X' ⟶ X) (f' : X' ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') (hg : g ≫ b = t)
    (sq₁ : IsPullback p f' a b) (sq₂ : IsPullback h e f' g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj E) F) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  -- the schemes `X'`, `Y`, `T` and `S'` are of finite type over `K`, hence locally Noetherian
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sq₁ ‹LocallyOfFiniteType a›
  have : QuasiCompact f' := MorphismProperty.of_isPullback sq₁ ‹QuasiCompact a›
  have : LocallyOfFiniteType e := MorphismProperty.of_isPullback sq₂ ‹LocallyOfFiniteType f'›
  have : QuasiCompact e := MorphismProperty.of_isPullback sq₂ ‹QuasiCompact f'›
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian b
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (f' ≫ b)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (e ≫ t)
  have hw : h ≫ f' ≫ b = e ≫ t := by rw [← Category.assoc, sq₂.w, Category.assoc, hg]
  -- hence `g` and `h` are quasi-compact and quasi-separated
  have : QuasiCompact g := by
    have : QuasiCompact (g ≫ b) := by rw [hg]; infer_instance
    exact QuasiCompact.of_comp g b
  have : QuasiCompact h := by
    have : QuasiCompact (h ≫ f' ≫ b) := by rw [hw]; infer_instance
    exact QuasiCompact.of_comp h (f' ≫ b)
  -- and of finite cohomological dimension, so that `Rg_*` and `Rh_*` commute with direct sums
  have hgd := hasFiniteCohomologicalDimensionMorphism Λ hΛ t b g hg
  have hhd := hasFiniteCohomologicalDimensionMorphism Λ hΛ (e ≫ t) (f' ≫ b) h hw
  have := preservesColimitsOfShape_nat_rightDerivedLowerStar Λ h hhd
  -- reduce `E` to strictly bounded complexes of flat sheaves
  exact DerivedCategory.isIso_app_of_isIso_app_Q_obj_flat
    (Functor.whiskerLeft L((p)^*[ModuleCat.{u + 1} Λ])
      (tensorBaseChangeMapLeft (ModuleCat.{u + 1} Λ) h e f' g sq₂.w F))
    (fun P m n _ _ hP ↦ isIso_tensorBaseChangeMap_Q_obj_of_flat a b p f' h e g hgd hhd sq₁ sq₂
      P m n hP F) E

end Inputs

section Kunneth

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]

end Kunneth

end Etale

end AlgebraicGeometry
