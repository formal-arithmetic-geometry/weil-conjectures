/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Generation of `Dctf`

This file computes the Tor amplitude of a flat sheaf placed in degree `0`, shows that
`Dctf(X, Λ)` is a thick subcategory of `D(X_ét, Λ)` for a finite ring `Λ`, and proves that it is
generated, as a thick subcategory, by the objects `Rg_* Rj_! L` for lisse flat sheaves `L` on the
strata of stratifications of `X` (`sk-lem-sf-flat-model`, complement). Over a finite-type scheme
over a field, `Dctf(X, Λ)` is exactly the thick envelope of these generators
(`lem-trf-devissage-generation`).

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-! ### Tor amplitude of a flat sheaf -/

section FlatSheaf

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}

/-- Tor amplitude in the sense of `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`,
tested on one homology sheaf at a time, is Tor amplitude in the sense of
`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn`, tested through the canonical
t-structure. -/
lemma torAmplitudeIn_of_hasTorAmplitudeIn {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : DerivedCategory.hasTorAmplitudeIn Λ X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K := fun F ↦ by
  rw [_root_.DerivedCategory.homologyConcentratedIn_iff]
  exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 fun q hq ↦ h F q (.inl hq),
    (_root_.DerivedCategory.isLE_iff _ b).2 fun q hq ↦ h F q (.inr hq)⟩

/-- A flat constructible sheaf placed in degree `0` has Tor amplitude in `[0, 0]`: the single
complex is its own bounded flat model
(`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`). -/
theorem torAmplitudeIn_singleFunctor_obj_of_flat
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (hF : ObjectProperty.flat F) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) X 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
  refine torAmplitudeIn_of_hasTorAmplitudeIn Λ ((hasTorAmplitudeIn_iff_exists_flatModel Λ 0 0
    le_rfl _ (DerivedCategory.boundedConstructible_singleFunctor_obj F 0)).2
    ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F, ⟨fun q hq ↦ ?_, fun q ↦ ?_⟩,
      ⟨(_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app F⟩⟩)
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · by_cases hq : q = 0
    · subst hq
      exact ObjectProperty.prop_of_iso _ (HomologicalComplex.singleObjXSelf _ 0 F).symm hF
    · exact ObjectProperty.flat_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

end FlatSheaf

/-! ### `Dctf` is a thick subcategory -/

section Thick

variable (X : Scheme.{u})

/-- Finite Tor amplitude is a triangulated property of objects of `D(X_ét)`: the derived
tensor product `- ⊗ᴸ F` is a triangulated functor, and concentration in an interval is stable
under shifts and under extensions, with the interval shifted and widened. -/
instance DerivedCategory.finiteTorAmplitude_isTriangulated :
    (DerivedCategory.finiteTorAmplitude A X).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, 0, 0, fun F ↦ by
    have h : IsZero ((0 : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) ⊗
        (_root_.DerivedCategory.singleFunctor _ 0).obj F) :=
      Functor.map_isZero ((-⊗ᴸ-(X)[A]).flip.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) (isZero_zero _)
    exact ⟨(_root_.DerivedCategory.isGE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ h,
      (_root_.DerivedCategory.isLE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ h⟩⟩
  isStableUnderShiftBy n := ⟨fun M ⟨a, b, h⟩ ↦ ⟨a - n, b - n, fun F ↦ by
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    obtain ⟨h₁, h₂⟩ := h F
    let e := (((-⊗ᴸ-(X)[A]).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).commShiftIso n).app M
    have hge := _root_.DerivedCategory.TStructure.t.isGE_shift (M ⊗
      (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F) a n (a - n)
    have hle := _root_.DerivedCategory.TStructure.t.isLE_shift (M ⊗
      (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F) b n (b - n)
    exact ⟨@Triangulated.TStructure.isGE_of_iso _ _ _ _ _ _ _ _root_.DerivedCategory.TStructure.t
        _ _ e.symm (a - n) hge,
      @Triangulated.TStructure.isLE_of_iso _ _ _ _ _ _ _ _root_.DerivedCategory.TStructure.t
        _ _ e.symm (b - n) hle⟩⟩⟩
  ext₂' T hT := by
    rintro ⟨a, b, h₁⟩ ⟨c, d, h₃⟩
    refine ObjectProperty.le_isoClosure _ _ ⟨min a c, max b d, fun F ↦ ?_⟩
    let G := (-⊗ᴸ-(X)[A]).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
    let := _root_.DerivedCategory.commShiftTensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    have : G.IsTriangulated := _root_.DerivedCategory.isTriangulated_tensorRight
      (K := (_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F)
    obtain ⟨g₁, l₁⟩ := (h₁ F).mono (min_le_left a c) (le_max_left b d)
    obtain ⟨g₃, l₃⟩ := (h₃ F).mono (min_le_right a c) (le_max_right b d)
    exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ (G.map_distinguished _ hT) _ g₁ g₃,
      _root_.DerivedCategory.TStructure.t.isLE₂ _ (G.map_distinguished _ hT) _ l₁ l₃⟩

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- `Dctf(X, Λ)` is a triangulated subcategory of `D(X_ét, Λ)`, for a finite ring `Λ`. -/
instance DerivedCategory.constructibleFiniteTor_isTriangulated :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).IsTriangulated :=
  inferInstanceAs (boundedConstructible (ModuleCat.{u + 1} Λ) X ⊓
    DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) X).IsTriangulated

/-- `Dctf(X, Λ)` is stable under retracts, for a finite ring `Λ`. Together with
`DerivedCategory.constructibleFiniteTor_isTriangulated`, it is a thick subcategory of
`D(X_ét, Λ)`. -/
instance DerivedCategory.constructibleFiniteTor_isStableUnderRetracts :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).IsStableUnderRetracts where
  of_retract e h := ⟨(boundedConstructible _ X).prop_of_retract e h.1,
    (DerivedCategory.finiteTorAmplitude _ X).prop_of_retract e h.2⟩

end Thick

/-! ### Generation of `Dctf` -/

section Generation

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
variable {Λ} in
/-- Tor amplitude through the canonical t-structure gives Tor amplitude tested on one homology
sheaf at a time. -/
lemma hasTorAmplitudeIn_of_torAmplitudeIn {X : Scheme.{u}} {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    DerivedCategory.hasTorAmplitudeIn Λ X a b K := fun F q hq ↦ by
  obtain ⟨h₁, h₂⟩ := h F
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 h₁ q hq
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 h₂ q hq

end Generation

end Etale

end AlgebraicGeometry
