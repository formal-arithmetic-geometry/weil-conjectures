/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.OrientationTransitionLowerShriekUpperStar

/-!
# The open-immersion piece of the reduction square for `Rj_!`, from the pullback square

Write `Res` for the restriction of scalars along `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` on the étale site and
`T : red_{n+1} ⟶ red_n ⋙ Res` for the transpose of the compatibility of the derived extension of
scalars with the reductions (`ProEtale.CondensedRing.etaleReductionTransposeNatTrans`). For an
open immersion `j`, this file (blueprint `det-sp-purity-coefficient-change`) proves that the
comparisons `j^! ⋙ red ≅ red ⋙ D(j^*)` modulo `ℓⁿ⁺¹` and `ℓⁿ`
(`ProEtale.CondensedRing.etaleReductionUpperStarIsoOfIsOpenImmersion`) are intertwined by `T` and
the mate `D(j^*) ⋙ Res ⟶ Res ⋙ D(j^*)` of the commutation of `Res` with `D(j_!)`
(`ProEtale.CondensedRing.etaleReductionUpperStarIsoOfIsOpenImmersion_restrictScalars`). It follows
from the reduction square for the pullbacks
(`ProEtale.CondensedRing.etaleReductionUpperStarIso_restrictScalars`), since the mate above is the
inverse of the commutation of `Res` with `D(j^*)`
(`Etale.mateEquiv_derivedRestrictScalarsCompOpenImmersionLowerShriekIso_hom_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The rearrangement behind
`ProEtale.CondensedRing.etaleReductionUpperStarIsoOfIsOpenImmersion_restrictScalars`: for
composites `δ = s ≫ u ≫ l` and `rδ = r₁ ≫ r₂ ≫ r₃`, one has `t₁ ≫ rδ ≫ κ = δ ≫ d`, given a
naturality square `t₁ ≫ r₁ = s ≫ t₂`, the square `lt ≫ lur ≫ r₂⁻¹ = u⁻¹ ≫ t₂`, the identity
`lur ≫ r₃ ≫ κ = l'` and a naturality square `lt ≫ l' = l ≫ d`. -/
theorem comp_comp_eq_comp_of_comp_eq {C : Type*} [Category C] {A A₁ A₂ B B₁ B₂ E F G P : C}
    (t₁ : A ⟶ B) (rδ : B ⟶ E) (κ : E ⟶ F) (δ : A ⟶ G) (d : G ⟶ F)
    (r₁ : B ⟶ B₁) (r₂ : B₁ ⟶ B₂) (r₃ : B₂ ⟶ E) (hr : rδ = r₁ ≫ r₂ ≫ r₃)
    (s : A ⟶ A₁) (u : A₁ ⟶ A₂) (l : A₂ ⟶ G) (hδ : δ = s ≫ u ≫ l)
    (t₂ : A₁ ⟶ B₁) (hT : t₁ ≫ r₁ = s ≫ t₂)
    (lt : A₂ ⟶ P) (lur : P ⟶ B₂) (r₂' : B₂ ⟶ B₁) (u' : A₂ ⟶ A₁)
    (hu : u ≫ u' = 𝟙 _) (hr₂ : r₂' ≫ r₂ = 𝟙 _) (hgen : lt ≫ lur ≫ r₂' = u' ≫ t₂)
    (l' : P ⟶ F) (hH : lur ≫ r₃ ≫ κ = l') (hl' : lt ≫ l' = l ≫ d) :
    t₁ ≫ rδ ≫ κ = δ ≫ d := by
  have ht₂ : t₂ = u ≫ lt ≫ lur ≫ r₂' := by
    rw [hgen, reassoc_of% hu]
  subst hr hδ
  simp only [Category.assoc]
  rw [← hl', ← hH, reassoc_of% hT, ht₂]
  simp only [Category.assoc]
  rw [reassoc_of% hr₂]

end CategoryTheory

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The mate, under the derived adjunctions `D(j_!) ⊣ D(j^*)` over `Λ'` and `Λ`, of the
commutation of the restriction of scalars with `D(j_!)` is the inverse of its commutation with
`D(j^*)`. -/
lemma mateEquiv_derivedRestrictScalarsCompOpenImmersionLowerShriekIso_hom_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (mateEquiv (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ') j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j).hom).app K =
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ j)).inv.app K := by
  refine NatTrans.congr_app (mateEquiv_eq_of_unit _ _ _
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ j)).inv)
    fun a ↦ ?_) K
  rw [← derivedOpenImmersionLowerShriekUpperStarAdjunction_unit_app_restrictScalars ρ j a]
  simp

/-- The commutation of the restriction of scalars with `Lj^*`, followed by `Lj^* ≅ D(j^*)` and
the mate of the commutation of the restriction of scalars with `D(j_!)`, is `Lj^* ≅ D(j^*)`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_hom_app_comp_mateEquiv_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ j).hom.app K ≫
      (Sheaf.derivedRestrictScalars U.smallEtaleTopology ρ).map
        ((leftDerivedUpperStarIsoMapDerivedCategory _ j).hom.app K) ≫
      (mateEquiv (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ') j)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j).hom).app K =
    (leftDerivedUpperStarIsoMapDerivedCategory _ j).hom.app
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj K) := by
  rw [mateEquiv_derivedRestrictScalarsCompOpenImmersionLowerShriekIso_hom_app,
    leftDerivedUpperStarRestrictScalarsIso_hom_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

variable {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

-- unifying the categories of the pullback square with those of the target needs a deeper
-- recursion in the elaborator
set_option maxRecDepth 20000 in
/-- Blueprint `det-sp-purity-coefficient-change`, the open-immersion piece transposed to `j^*`:
through the transposes `T : red_{n+1} ⟶ red_n ⋙ Res` of `β`, the comparisons
`j^! ⋙ red ≅ red ⋙ D(j^*)` modulo `ℓⁿ⁺¹` and `ℓⁿ`
(`etaleReductionUpperStarIsoOfIsOpenImmersion`) are intertwined by the mate
`D(j^*) ⋙ Res ⟶ Res ⋙ D(j^*)` of the commutation of `Res` with `D(j_!)`
(`Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso`). -/
theorem etaleReductionUpperStarIsoOfIsOpenImmersion_restrictScalars
    (N : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    have := HasCompactification.of_over j
    (etaleReductionTransposeNatTrans ℓ E n U).app
        ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E j).obj N) ≫
      (Sheaf.derivedRestrictScalars U.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).map
        ((etaleReductionUpperStarIsoOfIsOpenImmersion ℓ E j n).hom.app N) ≫
      (mateEquiv (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) j.left)
        (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))) j.left)
        (Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso
          (integersModPowCoeffTransition ℓ E n) j.left).hom).app
        ((etaleReduction ℓ E n X).obj N) =
    (etaleReductionUpperStarIsoOfIsOpenImmersion ℓ E j (n + 1)).hom.app N ≫
      (Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1)))
        j.left).mapDerivedCategory.map ((etaleReductionTransposeNatTrans ℓ E n X).app N) := by
  intro _
  have hgen := etaleReductionUpperStarIso_restrictScalars ℓ E n j N
  have hr₂ : (Sheaf.derivedRestrictScalars U.left.smallEtaleTopology
      (integersModPowCoeffTransition ℓ E n)).map ((etaleReductionUpperStarIso ℓ E n j).inv.app N) ≫
      (Sheaf.derivedRestrictScalars U.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).map
          ((etaleReductionUpperStarIso ℓ E n j).hom.app N) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact CategoryTheory.Functor.map_id _ _
  exact comp_comp_eq_comp_of_comp_eq _ _ _ _ _
    ((Sheaf.derivedRestrictScalars U.left.smallEtaleTopology
      (integersModPowCoeffTransition ℓ E n)).map ((etaleReduction ℓ E n U).map
        ((boundedConstructibleUpperShriekIsoUpperStar_padicIntegers ℓ E j).hom.app N))) _ _
    (by simp [etaleReductionUpperStarIsoOfIsOpenImmersion]) _ _ _ rfl _
    ((etaleReductionTransposeNatTrans ℓ E n U).naturality
      ((boundedConstructibleUpperShriekIsoUpperStar_padicIntegers ℓ E j).hom.app N)).symm
    _ _ _ _ (Iso.hom_inv_id_app _ _) hr₂ hgen _
    (Etale.leftDerivedUpperStarRestrictScalarsIso_hom_app_comp_mateEquiv_app _ j.left _)
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ j.left).hom.naturality _)

end AlgebraicGeometry.ProEtale.CondensedRing
