/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility

/-!
# Tor amplitude and `Dᵇ_ctf(X,Λ)` with finite constant scalar models

The four notions below are the declarations of
`WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility` and the generic Tor amplitude
of
`WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`, which are not redefined here:

1. `Cons(X,Λ)` is `AlgebraicGeometry.ProEtale.ConstantModelConstructible`, the full
   subcategory of `IsConstantModelConstructible` (finite constant local models
   `HasFiniteConstantLocalModel` on the strata of a finite constructible stratification for
   qcqs `X`, imposed on affine opens otherwise).
2. `Dᵇ_c(X,Λ)` is `ConstantModelBoundedConstructible`, the full subcategory of
   `constantModelBoundedConstructible`: bounded for the canonical t-structure (`H^q = 0` for
   all but finitely many `q`) with every `H^q` in `Cons(X,Λ)`.
3. Tor amplitude in `[a,b]` is `DerivedCategory.torAmplitudeIn _ a b`: for every
   `Λ_X`-module `N`, `K ⊗ᴸ N[0]` has cohomology concentrated in `[a,b]`. Its tensor is,
   definitionally, the relative derived tensor `CondensedRing.derivedTensor Λ X` over
   `Λ_X`. Finite Tor amplitude is `DerivedCategory.finiteTorAmplitude _`.
4. `Dᵇ_ctf(X,Λ)` is `ConstantModelConstructibleFiniteTor`, the full subcategory of the
   intersection of `constantModelBoundedConstructible` with `finiteTorAmplitude`.

This module states the well-definedness assertions for these notions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped CategoryTheory.Obj ZeroObject
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- **Well-definedness of `Cons`, `Dᵇ_c`, Tor amplitude and `Dᵇ_ctf`.** Let `Λ` be a
commutative condensed ring and `X` a scheme. Constructibility, bounded constructibility,
Tor amplitude in `[a,b]` and finite Tor amplitude are invariant under isomorphism, and
Tor amplitude is stable under shifts, extensions and retracts, so the complexes of finite
Tor amplitude form a thick subcategory of `D(X_proét,Λ)`. -/
theorem constantModelConstructibleFiniteTor_wellDefined (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) ∧
    (constantModelBoundedConstructible Λ X).IsClosedUnderIsomorphisms ∧
    (∀ a b : ℤ, a ≤ b → (DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) a b
      ).IsClosedUnderIsomorphisms) ∧
    (DerivedCategory.finiteTorAmplitude
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      ).IsClosedUnderIsomorphisms ∧
    (∀ (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      (a b : ℤ), a ≤ b → DerivedCategory.torAmplitudeIn _ a b K →
        DerivedCategory.torAmplitudeIn _ (a - 1) (b - 1) (K⟦(1 : ℤ)⟧)) ∧
    (∀ (T : Triangle (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
      (a b : ℤ), a ≤ b → T ∈ distTriang _ →
        DerivedCategory.torAmplitudeIn _ a b T.obj₁ →
        DerivedCategory.torAmplitudeIn _ a b T.obj₃ →
        DerivedCategory.torAmplitudeIn _ a b T.obj₂) ∧
    (∀ a b : ℤ, a ≤ b → (DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) a b
      ).IsStableUnderRetracts) ∧
    (DerivedCategory.finiteTorAmplitude
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      ).IsTriangulated ∧
    (DerivedCategory.finiteTorAmplitude
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      ).IsStableUnderRetracts := by
  classical
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have hlocal (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨𝒰, h𝒰⟩ := hM
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩
  have hstrat (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (hM : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := hM
    exact ⟨S, fun a ↦ hlocal _
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  have hcons : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstantModelConstructible Λ X) := ⟨fun e hM ↦ by
    unfold IsConstantModelConstructible at hM ⊢
    split_ifs at hM ⊢ with hX
    · exact hstrat _ e hM
    · exact fun U hU ↦ hstrat _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)⟩
  have := hcons
  have hbounded : (constantModelBoundedConstructible Λ X).IsClosedUnderIsomorphisms :=
    ⟨fun e hK ↦ ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
      fun n ↦ ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩⟩
  have hshift (K : DerivedCategory C) (a b m : ℤ)
      (hK : DerivedCategory.torAmplitudeIn C a b K) :
      DerivedCategory.torAmplitudeIn C (a - m) (b - m) (K⟦m⟧) := by
    intro N
    let F := (curriedTensor (DerivedCategory C)).flip.obj
      ((DerivedCategory.singleFunctor C 0).obj N)
    obtain ⟨h₁, h₂⟩ := hK N
    let e := (F.commShiftIso m).app K
    have hg : DerivedCategory.TStructure.t.IsGE (F.obj K) a := h₁
    have hl : DerivedCategory.TStructure.t.IsLE (F.obj K) b := h₂
    have hg' := DerivedCategory.TStructure.t.isGE_shift (F.obj K) a m (a - m)
    have hl' := DerivedCategory.TStructure.t.isLE_shift (F.obj K) b m (b - m)
    exact ⟨⟨(DerivedCategory.TStructure.t.ge (a - m)).prop_of_iso e.symm hg'.ge⟩,
      ⟨(DerivedCategory.TStructure.t.le (b - m)).prop_of_iso e.symm hl'.le⟩⟩
  have hext (T : Triangle (DerivedCategory C)) (a b : ℤ) (hT : T ∈ distTriang _)
      (h₁ : DerivedCategory.torAmplitudeIn C a b T.obj₁)
      (h₃ : DerivedCategory.torAmplitudeIn C a b T.obj₃) :
      DerivedCategory.torAmplitudeIn C a b T.obj₂ := by
    intro N
    let F := (curriedTensor (DerivedCategory C)).flip.obj
      ((DerivedCategory.singleFunctor C 0).obj N)
    obtain ⟨g₁, l₁⟩ := h₁ N
    obtain ⟨g₃, l₃⟩ := h₃ N
    exact ⟨DerivedCategory.TStructure.t.isGE₂ _ (F.map_distinguished _ hT) _ g₁ g₃,
      DerivedCategory.TStructure.t.isLE₂ _ (F.map_distinguished _ hT) _ l₁ l₃⟩
  have htri : (DerivedCategory.finiteTorAmplitude C).IsTriangulated :=
    { exists_zero := ⟨0, isZero_zero _, 0, 0, fun N ↦ by
        let F := (curriedTensor (DerivedCategory C)).flip.obj
          ((DerivedCategory.singleFunctor C 0).obj N)
        have hz := F.map_isZero (isZero_zero _)
        exact ⟨(DerivedCategory.isGE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ hz,
          (DerivedCategory.isLE_iff _ _).2 fun q _ ↦ Functor.map_isZero _ hz⟩⟩
      isStableUnderShiftBy := fun m ↦ ⟨fun K ⟨a, b, hK⟩ ↦
        ⟨a - m, b - m, hshift K a b m hK⟩⟩
      ext₂' := by
        rintro T hT ⟨a, b, h₁⟩ ⟨c, d, h₃⟩
        exact ObjectProperty.le_isoClosure _ _ ⟨min a c, max b d, hext T _ _ hT
          (h₁.mono (min_le_left _ _) (le_max_left _ _))
          (h₃.mono (min_le_right _ _) (le_max_right _ _))⟩ }
  exact ⟨hcons, hbounded, fun _ _ _ ↦ inferInstance, inferInstance,
    fun K a b _ hK ↦ hshift K a b 1 hK, fun T a b _ hT h₁ h₃ ↦ hext T a b hT h₁ h₃,
    fun _ _ _ ↦ inferInstance, htri, inferInstance⟩

end AlgebraicGeometry.ProEtale
