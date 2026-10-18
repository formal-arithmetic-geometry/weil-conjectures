/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.SelfInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.TracePairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism

/-!
# Nondegeneracy of the untwisted Poincaré pairing

Let `k` be algebraically closed, `a : X ⟶ Spec k` proper and geometrically connected with a Tate
orientation `γ` of relative dimension `d`, and `Λ` a finite self-injective cogenerating quotient
ring of `ℤ` (e.g. `ℤ/ℓᵐ`) whose characteristic is invertible on `X`. Over `k` the Tate twists are
trivial: `Λ_X(d) ≅ Λ_X` and `Λ_k(-d) ≅ Λ_k`. Then the untwisted smooth trace
`(Ra_! Λ_X)[2d] ⟶ Λ(-d) ≅ Λ` is a counit of `Ra_! ⊣ Ra^!`
(`AlgebraicGeometry.Etale.TateOrientation.bijective_comp_untwistedSmoothTrace`): it differs from
the smooth trace of the orientation `Λ_X[2d] ≅ Λ_X(d)[2d] ≅ Ra^! Λ` by an endomorphism of `Λ_X`,
that is (`X` connected) by a scalar, which is a unit since the untwisted trace map is
bijective. Hence the untwisted derived pairing is perfect, and the untwisted degreewise pairing
`H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)`, `i + j = 2d`, is nondegenerate on both sides
(`AlgebraicGeometry.Etale.TateOrientation.injective_untwistedDegreewisePoincarePairing`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.TateOrientation

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {k : Type u} [Field k]
  [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X] {d : ℕ} {a : X ⟶ Spec (.of k)} [IsProper a]
  [GeometricallyConnected a] [ConnectedSpace X]

/-- Over a separably closed field the Tate twists are trivial: `Λ_X(d) ≅ Λ_X`. -/
noncomputable def tateObjectIsoUnit (a : X ⟶ Spec (.of k))
    (ψ : tateObject Λ (Spec (.of k)) d ≅ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k)))) :
    tateObject Λ X d ≅ 𝟙_ (DerivedCategoryModule Λ X) :=
  (leftDerivedUpperStarTateObjectIso a (d : ℤ)).symm ≪≫
    (L((a)^*[ModuleCat.{u + 1} Λ])).mapIso ψ ≪≫ leftDerivedUpperStarConstantComplexIso Λ a

variable [Module.Injective Λ Λ]

/-- **The untwisted smooth trace is a counit.** Read through `Λ_k(-d) ≅ Λ_k`, every morphism
`(Ra_! U)[2d] ⟶ Λ_k` is `(Ra_! z)[2d]` followed by the untwisted smooth trace, for a unique
`z : U ⟶ Λ_X`. -/
theorem bijective_comp_untwistedSmoothTrace (hΛ : Function.Surjective (Int.cast : ℤ → Λ))
    (γ : TateOrientation Λ a d)
    (ι : tateObject Λ (Spec (.of k)) (-d) ≅ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))))
    (U : DerivedCategoryModule Λ X) :
    Function.Bijective (fun z : U ⟶ 𝟙_ _ ↦ (R(a)_![ModuleCat.{u + 1} Λ]).map (z⟦(2 * d : ℤ)⟧') ≫
      ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        γ.untwistedSmoothTrace ≫ ι.hom) := by
  obtain ⟨ψ⟩ := nonempty_tateObject_iso_unit Λ k (d : ℤ)
  let γ' : (𝟙_ (DerivedCategoryModule Λ X))⟦(2 * d : ℤ)⟧ ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) a :=
    (shiftFunctor _ (2 * d : ℤ)).mapIso (tateObjectIsoUnit a ψ).symm ≪≫ γ.dualizingComplexIso
  have hb := bijective_rightDerivedLowerShriek_map_shift_comp_smoothTrace
    (ModuleCat.{u + 1} Λ) a γ'
  let c := ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).app
    (𝟙_ (DerivedCategoryModule Λ X))
  obtain ⟨w, hw⟩ := (hb (𝟙_ _)).2 (c.hom ≫ γ.untwistedSmoothTrace ≫ ι.hom)
  obtain ⟨r, rfl⟩ := (bijective_smul_id_unit Λ X).2 w
  obtain ⟨n, rfl⟩ := hΛ r
  simp only [Int.cast_smul_eq_zsmul, Functor.map_zsmul, CategoryTheory.Functor.map_id,
    Preadditive.zsmul_comp, Category.id_comp] at hw
  -- the integer `n` is a unit of `Λ`, the untwisted trace map being bijective
  obtain ⟨z', hz'⟩ := (bijective_untwistedTraceMap a γ).2 ι.inv
  have hz'' : z' ≫ γ.untwistedSmoothTrace ≫ ι.hom = 𝟙 _ := by
    rw [← Category.assoc]
    exact (congrArg (· ≫ ι.hom) hz').trans ι.inv_hom_id
  obtain ⟨r', hr'⟩ := (bijective_smul_id_unit Λ (Spec (.of k))).2
    (z' ≫ c.inv ≫ Etale.smoothTrace γ')
  obtain ⟨n', rfl⟩ := hΛ r'
  simp only at hr'
  have h1 : (𝟙 _ : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ _) =
      n • ((n' : Λ) • 𝟙 _) := by
    rw [hr', ← Preadditive.comp_zsmul, ← Preadditive.comp_zsmul, hw, Iso.inv_hom_id_assoc]
    exact hz''.symm
  have hn : ((n * n' : ℤ) : Λ) = 1 := by
    refine (bijective_smul_id_unit Λ (Spec (.of k))).1 ?_
    simp only
    rw [one_smul]
    conv_rhs => rw [h1]
    rw [← Int.cast_smul_eq_zsmul Λ n, smul_smul, Int.cast_mul]
  have hfun : (fun z : U ⟶ 𝟙_ _ ↦ (R(a)_![ModuleCat.{u + 1} Λ]).map (z⟦(2 * d : ℤ)⟧') ≫
      ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).hom.app _ ≫
        γ.untwistedSmoothTrace ≫ ι.hom) =
      (fun z : U ⟶ 𝟙_ _ ↦ (R(a)_![ModuleCat.{u + 1} Λ]).map (z⟦(2 * d : ℤ)⟧') ≫
        Etale.smoothTrace γ') ∘ (fun z ↦ n • z) := by
    funext z
    simp only [Function.comp_apply, Functor.map_zsmul, Preadditive.zsmul_comp]
    rw [← Preadditive.comp_zsmul, hw]
    rfl
  rw [hfun]
  have hnn (z : U ⟶ 𝟙_ _) : n' • n • z = z := by
    rw [smul_smul, mul_comm, ← Int.cast_smul_eq_zsmul Λ, hn, one_smul]
  refine (hb U).comp ⟨fun z₁ z₂ h ↦ ?_, fun z ↦ ⟨n' • z, ?_⟩⟩
  · rw [← hnn z₁, ← hnn z₂]
    exact congrArg (fun z ↦ n' • z) h
  · beta_reduce
    rw [smul_smul, ← Int.cast_smul_eq_zsmul Λ, hn, one_smul]

end AlgebraicGeometry.Etale.TateOrientation
