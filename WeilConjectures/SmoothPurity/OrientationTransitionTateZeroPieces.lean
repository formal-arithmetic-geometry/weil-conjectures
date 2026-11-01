/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.OrientationTransitionUnit
public import WeilConjectures.TateTwist.IntegralReduction

/-!
# Pieces of the degree-zero reduction of the integral Tate twist
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor


/-- A categorical rearrangement for the degree-zero reduction of the integral Tate twist: from
`Gz ≫ c₁ = c_K ≫ Lsu`, `fl ≫ e ≫ su_B = Lsu ≫ εL`, `Φ (e ≫ su_B) ≫ Φ_U = m ≫ a ≫ su_P`,
`Rν b ≫ r ≫ su_E = Rν su_P ≫ R_U`, `t_N ≫ t_z = su_E` and `t = a ≫ b`, the composite
`Rν (Φ (c_K ≫ fl) ≫ m ≫ t) ≫ r ≫ t_N ≫ t_z` is `Rν (Φ Gz) ≫ Rν (Φ (c₁ ≫ εL) ≫ Φ_U) ≫ R_U`. -/
lemma CategoryTheory.map_comp_eq_of_unitIso_pieces {DB DP DE : Type*} [Category* DB]
    [Category* DP] [Category* DE] (Φ : DB ⥤ DP) (Rν : DP ⥤ DE)
    {GK G₁ LK L₁ sB sB₁ oB : DB} {sP sP₁ sP' oP : DP} {sE T oE : DE}
    (Gz : GK ⟶ G₁) (c₁ : G₁ ⟶ L₁) (cK : GK ⟶ LK) (Lsu : LK ⟶ L₁) (εL : L₁ ⟶ oB)
    (fl : LK ⟶ sB) (e : sB ⟶ sB₁) (suB : sB₁ ⟶ oB)
    (m : Φ.obj sB ⟶ sP) (a : sP ⟶ sP₁) (b : sP₁ ⟶ sP') (t : sP ⟶ sP') (suP : sP₁ ⟶ oP)
    (ΦU : Φ.obj oB ⟶ oP) (r : Rν.obj sP' ⟶ sE) (suE : sE ⟶ oE) (tN : sE ⟶ T) (tz : T ⟶ oE)
    (RU : Rν.obj oP ⟶ oE)
    (hN : Gz ≫ c₁ = cK ≫ Lsu) (h₁ : fl ≫ e ≫ suB = Lsu ≫ εL)
    (h₂ : Φ.map (e ≫ suB) ≫ ΦU = m ≫ a ≫ suP)
    (h₃ : Rν.map b ≫ r ≫ suE = Rν.map suP ≫ RU) (h₄ : tN ≫ tz = suE) (ht : t = a ≫ b) :
    (Rν.map (Φ.map (cK ≫ fl) ≫ m ≫ t) ≫ r ≫ tN) ≫ tz =
      Rν.map (Φ.map Gz) ≫ Rν.map (Φ.map (c₁ ≫ εL) ≫ ΦU) ≫ RU := by
  subst ht h₄
  have k : Φ.map (Gz ≫ c₁ ≫ εL) ≫ ΦU = Φ.map (cK ≫ fl) ≫ m ≫ a ≫ suP := by
    rw [reassoc_of% hN, ← h₁, ← Category.assoc cK fl, Functor.map_comp, Category.assoc, h₂]
  have k' := Rν.congr_map k
  simp only [Functor.map_comp, Category.assoc] at k' h₃ ⊢
  rw [h₃, reassoc_of% k']

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- `Rν_* ν^* Λ ≅ Λ` on the unit placed in degree zero
(`rightDerivedComparisonLowerStarSingleFunctorIso`) is the unit isomorphism
`rightDerivedComparisonLowerStarUnitIso`, through `ν^* Λ ≅ Λ` and `Λ[0] ≅ 𝟙_`. -/
lemma map_singleFunctor_map_ε_comp_rightDerivedComparisonLowerStarSingleFunctorIso_hom :
    (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map ((DerivedCategory.singleFunctor _ 0).map
        (Functor.LaxMonoidal.ε (ν^*(X)[ModuleCat.{u + 1} Λ]))) ≫
      (rightDerivedComparisonLowerStarSingleFunctorIso Λ X (𝟙_ _)).hom ≫
        (DerivedCategory.singleFunctorObjUnitIso
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).hom =
    (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map (DerivedCategory.singleFunctorObjUnitIso _).hom ≫
      (rightDerivedComparisonLowerStarUnitIso X Λ).hom := by
  simp only [rightDerivedComparisonLowerStarSingleFunctorIso,
    rightDerivedComparisonLowerStarUnitIso,
    DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso,
    Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom]
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X (𝟙_ _)
    ⟨0, DerivedCategory.TStructure.t.isGE_of_iso (DerivedCategory.singleFunctorObjUnitIso _) 0⟩
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} Λ) X
    ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ⟨0, inferInstance⟩
  have hu' : inv ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) ≫
        (DerivedCategory.singleFunctorObjUnitIso
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).hom =
      (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map ((D(ν^*(X)[ModuleCat.{u + 1} Λ])).map
        (DerivedCategory.singleFunctorObjUnitIso
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).hom) ≫
        inv ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).unit.app (𝟙_ _)) := by
    rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq]
    simp
  have hε : (comparisonUpperStarUnitIso Λ X).inv = Functor.LaxMonoidal.ε _ := rfl
  rw [hu', hε]
  simp


variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- `finiteCoefficientDerivedEquivalenceUnitIso` precomposed with a morphism `M[0] ⟶ 𝟙_[0]`
placed in degree zero is the image of that morphism under the abelian equivalence, followed by
`finiteCoefficientModEquivalenceUnitIso`, placed in degree zero. -/
lemma finiteCoefficientDerivedEquivalence_map_comp_unitIso_hom
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)} (x : M ⟶ 𝟙_ _) :
    (finiteCoefficientDerivedEquivalence X T).functor.map
        ((DerivedCategory.singleFunctor _ 0).map x ≫
          (DerivedCategory.singleFunctorObjUnitIso _).hom) ≫
      (finiteCoefficientDerivedEquivalenceUnitIso X T).hom =
    ((finiteCoefficientModEquivalence X T).functor.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map ((finiteCoefficientModEquivalence X T).functor.map x ≫
        (finiteCoefficientModEquivalenceUnitIso X T).hom) ≫
      (DerivedCategory.singleFunctorObjUnitIso _).hom := by
  have h := ((finiteCoefficientModEquivalence X T).functor.mapDerivedCategorySingleFunctor
    0).hom.naturality x
  simp only [finiteCoefficientDerivedEquivalenceUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _ (DerivedCategory.singleFunctorObjUnitIso _).hom, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (reassoc_of% h) _

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [NeZero (ringChar Λ)] (X : Scheme.{u})
  [HasInvertibleExponent Λ X]

/-- In degree zero, `Λ_X(0) ≅ (Λ_X(1)^{⊗ 0})[0] = 𝟙_[0]` (`tateObjectNatIsoSingleFunctor`) is
`Λ_X(0) ≅ Λ_X` (`HasTateTwist.twistObjectZeroIso`) followed by `𝟙_ ≅ 𝟙_[0]`. -/
lemma tateObjectNatIsoSingleFunctor_zero_inv_comp_twistObjectZeroIso_hom :
    (tateObjectNatIsoSingleFunctor Λ X 0).inv ≫ (HasTateTwist.twistObjectZeroIso (Λ := Λ) X).hom =
      (DerivedCategory.singleFunctorObjUnitIso _).hom := by
  sorry

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ) (X : Scheme.{u})

/-- On the unit `𝒪_E` placed in degree zero, the flat-object identification
`L(- ⊗ 𝒪_E ⧸ ℓⁿ)(𝒪_E[0]) ≅ (𝒪_E ⧸ ℓⁿ)[0]` (`Functor.leftDerivedFunctorSingleFunctorIsoOfFlat`)
is the unit isomorphism of the monoidal derived reduction
(`Functor.leftDerivedFunctorMonoidal`), through `𝟙_[0] ≅ 𝟙_` on both sides. -/
lemma leftDerivedFunctorSingleFunctorIsoOfFlat_unit_hom
    (hP : ObjectProperty.flat (integralTateTwistNat X ℓ E 0)) :
    letI := Mod.extendScalarsMonoidal (integersModPowReduction X ℓ E n)
    letI := (Mod.extendScalars (integersModPowReduction X ℓ E n)).leftDerivedFunctorMonoidal
    (Functor.leftDerivedFunctorSingleFunctorIsoOfFlat
        (Mod.extendScalars (integersModPowReduction X ℓ E n)) hP).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        (Functor.Monoidal.εIso (Mod.extendScalars (integersModPowReduction X ℓ E n))).inv ≫
      (DerivedCategory.singleFunctorObjUnitIso _).hom =
    L(Mod.extendScalars (integersModPowReduction X ℓ E n)).map
        (DerivedCategory.singleFunctorObjUnitIso (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))).hom ≫
      (Functor.Monoidal.εIso L(Mod.extendScalars (integersModPowReduction X ℓ E n))).inv := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
