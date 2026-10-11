/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplex

/-!
# Dual and Tate Weil data

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite MonoidalClosed

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor.LaxMonoidal

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] (F : C ⥤ C)
  [F.LaxMonoidal]

/-- The transpose of the *contragredient* `F [K, 𝟙] ⟶ [F K, F 𝟙] ⟶ [F K, 𝟙] ⟶ [K, 𝟙]` of a
lax monoidal endofunctor `F`, an isomorphism `φ : F K ≅ K` and a map `u : F 𝟙 ⟶ 𝟙`: it is
`K ⊗ F [K, 𝟙] ⟶ F K ⊗ F [K, 𝟙] ⟶ F (K ⊗ [K, 𝟙]) ⟶ F 𝟙 ⟶ 𝟙`. -/
lemma whiskerLeft_ihomComparison_comp_pre_comp_ev {K : C} (φ : F.obj K ≅ K)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ C) :
    K ◁ ((ihomComparison F K).natTrans.app (𝟙_ C) ≫ (ihom (F.obj K)).map u ≫
        (pre φ.inv).app (𝟙_ C)) ≫ (ihom.ev K).app (𝟙_ C) =
      φ.inv ▷ _ ≫ μ F K _ ≫ F.map ((ihom.ev K).app (𝟙_ C)) ≫ u := by
  rw [MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    id_tensor_pre_app_comp_ev, whisker_exchange_assoc, whisker_exchange_assoc,
    ihom.ev_naturality, ihomComparison_ev_assoc]
  rfl

section Monoidal

variable [F.Monoidal]

/-- The evaluation `K ⊗ [K, 𝟙] ⟶ 𝟙` intertwines `φ ⊗ ψ` and `u`, for the contragredient
`ψ : F [K, 𝟙] ⟶ [F K, F 𝟙] ⟶ [F K, 𝟙] ⟶ [K, 𝟙]` of `φ : F K ≅ K` and `u : F 𝟙 ⟶ 𝟙`. -/
lemma map_ev_comp_eq_δ_comp_ihomComparison_comp_pre {K : C} (φ : F.obj K ≅ K)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ C) :
    F.map ((ihom.ev K).app (𝟙_ C)) ≫ u =
      (OplaxMonoidal.δ F K _ ≫ φ.hom ▷ _ ≫
        K ◁ ((ihomComparison F K).natTrans.app (𝟙_ C) ≫ (ihom (F.obj K)).map u ≫
          (pre φ.inv).app (𝟙_ C))) ≫ (ihom.ev K).app (𝟙_ C) := by
  rw [Category.assoc, Category.assoc, whiskerLeft_ihomComparison_comp_pre_comp_ev,
    hom_inv_whiskerRight_assoc, Monoidal.δ_μ_assoc]

/-- The contragredient `F [K, 𝟙] ⟶ [F K, F 𝟙] ⟶ [F K, 𝟙] ⟶ [K, 𝟙]` of an isomorphism
`φ : F K ≅ K` and an isomorphism `u : F 𝟙 ⟶ 𝟙` is an isomorphism when `K` has a left dual. -/
lemma isIso_ihomComparison_comp_pre {Y K : C} [ExactPairing Y K] (φ : F.obj K ≅ K)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ C) [IsIso u] :
    IsIso ((ihomComparison F K).natTrans.app (𝟙_ C) ≫ (ihom (F.obj K)).map u ≫
      (pre φ.inv).app (𝟙_ C)) := by
  have e : (ihomComparison F K).natTrans.app (𝟙_ C) ≫ (ihom (F.obj K)).map u ≫
      (pre φ.inv).app (𝟙_ C) =
        curry (φ.inv ▷ _ ≫ μ F K _ ≫ F.map ((ihom.ev K).app (𝟙_ C)) ≫ u) := by
    rw [eq_comm, curry_eq_iff, uncurry_eq, whiskerLeft_ihomComparison_comp_pre_comp_ev]
  have := isIso_ihomUnitTensorToIhom Y K K
  letI := exactPairingOfIsIso K
  letI := ExactPairing.map F ((ihom K).obj (𝟙_ C)) K
  have hb : IsPerfectPairing (μ F K _ ≫ F.map ((ihom.ev K).app (𝟙_ C)) ≫ u) := by
    refine ⟨?_⟩
    have h : μ F K _ ≫ F.map ((ihom.ev K).app (𝟙_ C)) ≫ u =
        ε_ (F.obj ((ihom K).obj (𝟙_ C))) (F.obj K) ≫ LaxMonoidal.ε F ≫ u := by
      simp only [ExactPairing.evaluation, Category.assoc, Monoidal.η_ε_assoc]
      rfl
    rw [h, ← Category.assoc, curry_natural_right]
    infer_instance
  rw [e]
  exact (hb.whiskerRight_comp φ.inv).isIso

/-- For `K = 𝟙` and `φ : F 𝟙 ≅ 𝟙` compatible with the left unitor, the canonical
identification `𝟙 ≅ [𝟙, 𝟙]` intertwines `φ` and its contragredient. -/
lemma map_curry_leftUnitor_comp_ihomComparison_comp_pre (φ : F.obj (𝟙_ C) ≅ 𝟙_ C)
    (hφ : OplaxMonoidal.δ F (𝟙_ C) (𝟙_ C) ≫ φ.hom ▷ F.obj (𝟙_ C) ≫ (λ_ (F.obj (𝟙_ C))).hom =
      F.map (λ_ (𝟙_ C)).hom) :
    F.map (curry (λ_ (𝟙_ C)).hom) ≫ (ihomComparison F (𝟙_ C)).natTrans.app (𝟙_ C) ≫
        (ihom (F.obj (𝟙_ C))).map φ.hom ≫ (pre φ.inv).app (𝟙_ C) =
      φ.hom ≫ curry (λ_ (𝟙_ C)).hom := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_ihomComparison_comp_pre_comp_ev, MonoidalCategory.whiskerLeft_comp_assoc,
    ← uncurry_eq, uncurry_curry, leftUnitor_naturality, whisker_exchange_assoc,
    μ_natural_right_assoc, ← F.map_comp_assoc, ← uncurry_eq, uncurry_curry, ← hφ,
    Monoidal.μ_δ_assoc, inv_hom_whiskerRight_assoc]

end Monoidal

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.Functor

open MonoidalCategory

/-- A pairing `P : K ⊗ D ⟶ 𝟙` compatible with data `φ`, `ψ`, `u` stays compatible after
twisting by `T` with a datum `τ`: `K ⊗ (D ⊗ T) ≅ (K ⊗ D) ⊗ T ⟶ 𝟙 ⊗ T ≅ T` intertwines
`φ ⊗ (ψ ⊗ τ)` and `τ`, provided `u` is compatible with the left unitor. -/
lemma OplaxMonoidal.map_twistedPairing_comp {C : Type*} [Category* C] [MonoidalCategory C]
    (F : C ⥤ C) [F.OplaxMonoidal] {K D T : C} (φ : F.obj K ⟶ K) (ψ : F.obj D ⟶ D)
    (u : F.obj (𝟙_ C) ⟶ 𝟙_ C) (τ : F.obj T ⟶ T) (P : K ⊗ D ⟶ 𝟙_ C)
    (hP : F.map P ≫ u = (OplaxMonoidal.δ F K D ≫ φ ▷ F.obj D ≫ K ◁ ψ) ≫ P)
    (hu : OplaxMonoidal.δ F (𝟙_ C) T ≫ u ▷ F.obj T ≫ (λ_ (F.obj T)).hom = F.map (λ_ T).hom) :
    F.map ((α_ K D T).inv ≫ P ▷ T ≫ (λ_ T).hom) ≫ τ =
      (OplaxMonoidal.δ F K (D ⊗ T) ≫ φ ▷ F.obj (D ⊗ T) ≫
        K ◁ (OplaxMonoidal.δ F D T ≫ ψ ▷ F.obj T ≫ D ◁ τ)) ≫
        (α_ K D T).inv ≫ P ▷ T ≫ (λ_ T).hom := by
  rw [F.map_comp, F.map_comp, ← hu, ← OplaxMonoidal.δ_natural_left_assoc,
    ← comp_whiskerRight_assoc, hP]
  simp only [Category.assoc, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  rw [← OplaxMonoidal.associativity_inv_assoc]
  congr 1
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality,
    associator_inv_naturality_middle_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

section Comparison

variable [UpperStarPreservesFlat A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The lax monoidal structure map `μ` of the monoidal functor `Lg^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`) is the inverse of the tensor
comparison `Lg^*(K ⊗ᴸ M) ≅ Lg^* K ⊗ᴸ Lg^* M`. -/
lemma leftDerivedUpperStarMonoidal_μ (K M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A g
    Functor.LaxMonoidal.μ L((g)^*[A]) K M = (leftDerivedUpperStarTensorIso A g K M).inv := by
  let := leftDerivedUpperStarMonoidal A g
  rw [← cancel_mono (leftDerivedUpperStarTensorIso A g K M).hom, Iso.inv_hom_id]
  exact Functor.Monoidal.μ_δ _ _ _

/-- The canonical comparison `Lg^* RHom(K, N) ⟶ RHom(Lg^* K, Lg^* N)` of the derived pullback
with the derived internal hom: the comparison map of the monoidal functor `Lg^*`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), the transpose of
`Lg^* K ⊗ᴸ Lg^* RHom(K, N) ≅ Lg^*(K ⊗ᴸ RHom(K, N)) ⟶ Lg^* N`. This is the first arrow of the
contragredient datum of blueprint `def-pod-dual-tate-datum`. -/
noncomputable def leftDerivedUpperStarDerivedHomComparison
    (K N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).obj ((RHom(Y)[A].obj (op K)).obj N) ⟶
      (RHom(Z)[A].obj (op (L((g)^*[A]).obj K))).obj (L((g)^*[A]).obj N) :=
  letI := leftDerivedUpperStarMonoidal A g
  (Functor.LaxMonoidal.ihomComparison L((g)^*[A]) K).natTrans.app N

/-- The comparison `Lg^* RHom(K, N) ⟶ RHom(Lg^* K, Lg^* N)` is compatible with the
evaluations. -/
lemma derivedTensor_map_leftDerivedUpperStarDerivedHomComparison_comp_counit
    (K N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensor A Z).obj (L((g)^*[A]).obj K)).map
        (leftDerivedUpperStarDerivedHomComparison A g K N) ≫
      (derivedTensorHomAdjunction A (L((g)^*[A]).obj K)).counit.app (L((g)^*[A]).obj N) =
    (leftDerivedUpperStarTensorIso A g K _).inv ≫
      L((g)^*[A]).map ((derivedTensorHomAdjunction A K).counit.app N) := by
  let := leftDerivedUpperStarMonoidal A g
  rw [← leftDerivedUpperStarMonoidal_μ]
  exact Functor.LaxMonoidal.ihomComparison_ev _ _ _

end Comparison

section Datum

variable [UpperStarPreservesFlat A] {X : Scheme.{u}} (g : X ⟶ X)
  {K : DerivedCategory (Sheaf X.smallEtaleTopology A)}

/-- Blueprint `def-pod-dual-tate-datum`: Dual and Tate Weil data.

The *contragredient datum* `φ_{K^∨} : Lg^* K^∨ ⟶ K^∨` on the coefficient dual
`K^∨ = RHom(K, Λ_X)` of a complex `K` with a Weil datum `φ_K : Lg^* K ≅ K`, the typed composite
```
                      ≅                                 RHom(id, φ_Λ)
  Lg^* RHom(K, Λ_X) ────▶ RHom(Lg^* K, Lg^* Λ_X) ───────────────▶ RHom(Lg^* K, Λ_X)
                                     RHom(φ_K⁻¹, id)
                                   ───────────────▶ RHom(K, Λ_X)
```
of the comparison of `Lg^*` with the internal hom
(`AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedHomComparison`), the canonical datum
`φ_Λ : Lg^* Λ_X ≅ Λ_X` (`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`) and `φ_K⁻¹`. It
is an isomorphism for a dualizable (perfect) `K`
(`AlgebraicGeometry.Etale.isIso_contragredientWeilDatum`). -/
noncomputable def contragredientWeilDatum (φ : L((g)^*[A]).obj K ≅ K) :
    L((g)^*[A]).obj ((DerivedCategory.coefficientDual A X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual A X).obj (op K) :=
  leftDerivedUpperStarDerivedHomComparison A g K (𝟙_ _) ≫
    (RHom(X)[A].obj (op (L((g)^*[A]).obj K))).map (leftDerivedUpperStarUnitIso A g).hom ≫
      (RHom(X)[A].map φ.inv.op).app (𝟙_ _)

/-- The contragredient datum is characterised by the evaluation: `ev_K ∘ (K ⊗ᴸ φ_{K^∨})` is
```
                φ_K⁻¹ ⊗ᴸ id                        ≅                       Lg^* ev_K
  K ⊗ᴸ Lg^* K^∨ ──────────▶ Lg^* K ⊗ᴸ Lg^* K^∨ ────▶ Lg^*(K ⊗ᴸ K^∨) ──────────▶ Lg^* Λ_X
                   φ_Λ
                ──────▶ Λ_X.
``` -/
lemma derivedTensor_map_contragredientWeilDatum_comp_coefficientEvaluation
    (φ : L((g)^*[A]).obj K ≅ K) :
    ((derivedTensor A X).obj K).map (contragredientWeilDatum A g φ) ≫
        DerivedCategory.coefficientEvaluation K =
      ((derivedTensor A X).map φ.inv).app _ ≫ (leftDerivedUpperStarTensorIso A g K _).inv ≫
        L((g)^*[A]).map (DerivedCategory.coefficientEvaluation K) ≫
          (leftDerivedUpperStarUnitIso A g).hom := by
  let := leftDerivedUpperStarMonoidal A g
  rw [← leftDerivedUpperStarMonoidal_μ]
  exact Functor.LaxMonoidal.whiskerLeft_ihomComparison_comp_pre_comp_ev _ φ _


end Datum

end Etale

end AlgebraicGeometry
