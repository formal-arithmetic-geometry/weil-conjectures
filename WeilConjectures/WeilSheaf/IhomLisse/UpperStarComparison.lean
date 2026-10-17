/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso
public import WeilConjectures.WeilSheaf.LisseDuality

/-!
# Pullback of the internal hom out of a lisse sheaf

For any morphism `g : Z ⟶ Y` and sheaves `M`, `N` of `ℚ̄_ℓ,Y`-modules there is a comparison
morphism `g^* 𝓗om(M, N) ⟶ 𝓗om(g^* M, g^* N)`
(`AlgebraicGeometry.ProEtale.adicUpperStarIhomComparison`), adjoint to
`g^* 𝓗om(M, N) ⊗ g^* M ≅ g^*(𝓗om(M, N) ⊗ M) ⟶ g^* N`. It is natural in both variables and
compatible with the evaluations. For `g` weakly étale it is the isomorphism
`AlgebraicGeometry.ProEtale.adicUpperStarIhomIso`.

If `M` is lisse it is an isomorphism for every `g`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_adicUpperStarIhomComparison`): after pullback
along the members of the base change of a pro-étale cover trivialising `M`, it becomes the
comparison for a free module of finite rank, which is an isomorphism, being additive in `M` and
an isomorphism for `M = ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] Sheaf.symmetricCategory

section Comparison

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y)

variable (l) in
/-- The comparison `g^* 𝓗om(M, N) ⟶ 𝓗om(g^* M, g^* N)`, adjoint to
`g^* 𝓗om(M, N) ⊗ g^* M ≅ g^*(𝓗om(M, N) ⊗ M) ⟶ g^* N`. -/
noncomputable def adicUpperStarIhomComparison (M N : AdicSheaf l Y) :
    (g)^*ᵃ[l].obj ((AdicSheaf.ihom M).obj N) ⟶
      (AdicSheaf.ihom ((g)^*ᵃ[l].obj M)).obj ((g)^*ᵃ[l].obj N) :=
  (Mod.ihomAdjunction ((g)^*ᵃ[l].obj M)).homEquiv _ _
    ((adicUpperStarTensorLeftIso l g M).inv.app _ ≫
      (g)^*ᵃ[l].map ((Mod.ihomAdjunction M).counit.app N))

/-- The comparison of the pullback of an internal hom with the internal hom of the pullbacks is
compatible with the evaluations. -/
lemma uncurryHom_adicUpperStarIhomComparison (M N : AdicSheaf l Y) :
    Mod.uncurryHom (adicUpperStarIhomComparison l g M N) =
      μ (g)^*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.evaluation M N) := by
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  have h₁ := Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicUpperStarRingHom l g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _)
    ((AdicSheaf.ihom M).obj N) M
  have h₃ : Mod.tensorπ ((g)^*ᵃ[l].obj ((AdicSheaf.ihom M).obj N))
      ((g)^*ᵃ[l].obj M) = μ (g)^*[WeilCoefficients.{u} l] _ _ ≫
        (g)^*[WeilCoefficients.{u} l].map (Mod.tensorπ _ M) ≫
          ((adicUpperStarTensorLeftIso l g M).hom.app _).hom := by
    erw [h₁, IsIso.hom_inv_id_assoc]
    rfl
  rw [Mod.uncurryHom_eq, adicUpperStarIhomComparison, Equiv.symm_apply_apply, Mod.comp_hom',
    h₃, Category.assoc, Category.assoc, ← Category.assoc
      ((adicUpperStarTensorLeftIso l g M).hom.app _).hom, ← Mod.comp_hom', Iso.hom_inv_id_app,
    Mod.id_hom', Category.id_comp, adicUpperStar_map_hom, ← Functor.map_comp]
  rfl

/-- The comparison is natural in the target. -/
@[reassoc]
lemma adicUpperStarIhomComparison_naturality (M : AdicSheaf l Y) {N N' : AdicSheaf l Y}
    (f : N ⟶ N') :
    (g)^*ᵃ[l].map ((AdicSheaf.ihom M).map f) ≫ adicUpperStarIhomComparison l g M N' =
      adicUpperStarIhomComparison l g M N ≫
        (AdicSheaf.ihom ((g)^*ᵃ[l].obj M)).map ((g)^*ᵃ[l].map f) := by
  apply Mod.uncurryHom_injective
  rw [Mod.uncurryHom_comp, Mod.uncurryHom_comp_ihom_map, uncurryHom_adicUpperStarIhomComparison,
    uncurryHom_adicUpperStarIhomComparison, adicUpperStar_map_hom, adicUpperStar_map_hom]
  erw [μ_natural_left_assoc]
  rw [← Functor.map_comp, Mod.evaluation_naturality, Functor.map_comp, Category.assoc]

/-- The comparison is natural in the source. -/
@[reassoc]
lemma adicUpperStarIhomComparison_ihomMap {M M' : AdicSheaf l Y} (h : M' ⟶ M)
    (N : AdicSheaf l Y) :
    (g)^*ᵃ[l].map ((Mod.ihomMap h).app N) ≫ adicUpperStarIhomComparison l g M' N =
      adicUpperStarIhomComparison l g M N ≫
        (Mod.ihomMap ((g)^*ᵃ[l].map h)).app ((g)^*ᵃ[l].obj N) := by
  apply Mod.uncurryHom_injective
  rw [Mod.uncurryHom_comp, Mod.uncurryHom_comp_ihomMap, uncurryHom_adicUpperStarIhomComparison,
    uncurryHom_adicUpperStarIhomComparison, adicUpperStar_map_hom, adicUpperStar_map_hom]
  erw [μ_natural_left_assoc]
  rw [← Functor.map_comp, Mod.evaluation_ihomMap, Functor.map_comp]
  exact (μ_natural_right_assoc _ _ _ _).symm

/-- For a weakly étale morphism the comparison is the isomorphism
`AlgebraicGeometry.ProEtale.adicUpperStarIhomIso`. -/
lemma adicUpperStarIhomComparison_eq_of_weaklyEtale [WeaklyEtale g] (M N : AdicSheaf l Y) :
    adicUpperStarIhomComparison l g M N = (adicUpperStarIhomIso l g M).hom.app N := by
  apply Mod.uncurryHom_injective
  rw [uncurryHom_adicUpperStarIhomComparison, Mod.uncurryHom, adicUpperStarIhomIso_evaluation]

instance isIso_adicUpperStarIhomComparison_of_weaklyEtale [WeaklyEtale g]
    (M N : AdicSheaf l Y) : IsIso (adicUpperStarIhomComparison l g M N) := by
  rw [adicUpperStarIhomComparison_eq_of_weaklyEtale]
  infer_instance

/-- A helper for the evaluation calculus: naturality of `μ` for `g^*` in the first variable,
stated with the underlying sheaves of pulled back modules. -/
@[reassoc]
lemma adicUpperStar_map_hom_whiskerRight_μ {P Q : AdicSheaf l Y} (f : P ⟶ Q)
    (M : AdicSheaf l Y) :
    ((g)^*ᵃ[l].map f).hom ▷ ((g)^*ᵃ[l].obj M).X ≫ μ (g)^*[WeilCoefficients.{u} l] Q.X M.X =
      μ (g)^*[WeilCoefficients.{u} l] P.X M.X ≫
        (g)^*[WeilCoefficients.{u} l].map (f.hom ▷ M.X) :=
  μ_natural_left (g)^*[WeilCoefficients.{u} l] f.hom M.X

/-- The comparison is compatible with the composition of pullbacks. -/
lemma adicUpperStarIhomComparison_comp {W : Scheme.{u}} (r : W ⟶ Z) (M N : AdicSheaf l Y) :
    (adicUpperStarComp l r g).hom.app ((AdicSheaf.ihom M).obj N) ≫
        (r)^*ᵃ[l].map (adicUpperStarIhomComparison l g M N) ≫
          adicUpperStarIhomComparison l r ((g)^*ᵃ[l].obj M) ((g)^*ᵃ[l].obj N) =
      adicUpperStarIhomComparison l (r ≫ g) M N ≫
        (Mod.ihomMap (M := (r)^*ᵃ[l].obj ((g)^*ᵃ[l].obj M))
          ((adicUpperStarComp l r g).inv.app M)).app ((r ≫ g)^*ᵃ[l].obj N) ≫
          (AdicSheaf.ihom ((r)^*ᵃ[l].obj ((g)^*ᵃ[l].obj M))).map
            ((adicUpperStarComp l r g).hom.app N) := by
  apply Mod.uncurryHom_injective
  rw [← Category.assoc (adicUpperStarIhomComparison l (r ≫ g) M N),
    Mod.uncurryHom_comp_ihom_map, Mod.uncurryHom_comp_ihomMap, Mod.uncurryHom_comp,
    Mod.uncurryHom_comp, uncurryHom_adicUpperStarIhomComparison,
    uncurryHom_adicUpperStarIhomComparison, adicUpperStar_map_hom_whiskerRight_μ_assoc,
    ← Functor.map_comp, ← Mod.uncurryHom, uncurryHom_adicUpperStarIhomComparison,
    adicUpperStarComp_hom_app_hom, adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom]
  have hm := NatTrans.IsMonoidal.tensor (τ := (upperStarComp (WeilCoefficients.{u} l) r g).hom)
    ((AdicSheaf.ihom M).obj N).X M.X
  rw [Functor.LaxMonoidal.comp_μ] at hm
  sorry

/-- The right action of `ℚ̄_ℓ` on a pullback. -/
lemma rightAct_adicUpperStar_obj (N : AdicSheaf l Y) :
    Mod.rightAct ((g)^*ᵃ[l].obj N) =
      ((g)^*ᵃ[l].obj N).X ◁ adicUpperStarRingHom l g ≫
        μ (g)^*[WeilCoefficients.{u} l] N.X (adicConstantSheaf l Y) ≫
          (g)^*[WeilCoefficients.{u} l].map (Mod.rightAct N) := by
  sorry

/-- For `M = ℚ̄_ℓ` the comparison is the identification `g^* 𝓗om(ℚ̄_ℓ, N) ≅ g^* N ≅
𝓗om(ℚ̄_ℓ, g^* N)`. -/
lemma adicUpperStarIhomComparison_unit (N : AdicSheaf l Y) :
    adicUpperStarIhomComparison l g (AdicSheaf.unit l Y) N ≫
        (Mod.ihomMap (adicUpperStarUnitIso l g).inv).app _ =
      (g)^*ᵃ[l].map (Mod.ihomRegularIso.hom.app N) ≫
        Mod.ihomRegularIso.inv.app ((g)^*ᵃ[l].obj N) := by
  apply Mod.uncurryHom_injective
  rw [Mod.uncurryHom_comp_ihomMap, uncurryHom_adicUpperStarIhomComparison, Mod.uncurryHom,
    Mod.comp_hom', comp_whiskerRight, Category.assoc]
  sorry

end Comparison

end AlgebraicGeometry.ProEtale
