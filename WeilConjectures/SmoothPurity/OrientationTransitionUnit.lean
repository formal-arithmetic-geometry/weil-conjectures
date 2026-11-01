/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizingUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionMate
public import WeilConjectures.SmoothPurity.OrientationTransitionUnitPieces

/-!
# The reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` and the units

Write `Ψ` for the derived extension of scalars along `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` on the étale site and
`β : Ψ(red_{n+1} K) ≅ red_n K` for its compatibility with the reductions
(`ProEtale.CondensedRing.etaleReductionExtendScalarsIsoApp`). This file shows (blueprint
`det-sp-purity-coefficient-change`) that `β` at the unit is compatible with the identifications
`red_Y 𝒪 ≅ Λ` (`etaleReductionUnitIso`) and `Ψ Λ ≅ Λ'`
(`Etale.derivedExtendScalarsConstantComplexIso`):
`ProEtale.CondensedRing.map_etaleReductionUnitIso_hom_comp_constantComplexIso`. The condensed
part is the compatibility of the transitivity of the derived extensions of scalars with the units
(`ProEtale.CondensedRing.map_ε_comp_derivedExtendScalarsCompIso_inv_app_comp_η`); the remaining
part concerns the étale reading only
(`ProEtale.CondensedRing.map_readingUnitIso_hom_comp_constantComplexIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

set_option linter.unusedSectionVars false in
-- the statement keeps the section variables of the file
/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity.

**The comparisons of `ν^*` and of `Φ` with `Ψ` preserve the units, on the pro-étale site**:
`Ψ` of the identifications `Φ(𝟙) ≅ 𝟙 ≅ ν^* 𝟙` modulo `ℓⁿ⁺¹`
(`finiteCoefficientDerivedEquivalenceUnitIso`,
`DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso`), followed by the commutation
`Ψ ν^* ≅ ν^* Ψ` (`ProEtale.comparisonUpperStarDerivedExtendScalarsIso`) and `ν^*(Ψ Λ ≅ Λ')`, is the
compatibility of `Φ` with the extensions of scalars
(`ProEtale.finiteCoefficientDerivedEquivalenceExtendScalarsIso`), followed by the unit comparison
of the condensed extension of scalars and the identifications modulo `ℓⁿ`. -/
theorem map_unitIso_hom_comp_comparisonUpperStarDerivedExtendScalarsIso_hom :
    letI := Mod.extendScalarsMonoidal (integersModPowTransition Y.left ℓ E n)
    letI := (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctorMonoidal
    (derivedExtendScalars (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) Y.left).map
        ((finiteCoefficientDerivedEquivalenceUnitIso Y.left
          (PadicAlgCl.integersModPow ℓ E (n + 1))).hom :
          (finiteCoefficientDerivedEquivalence Y.left
            (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.obj (𝟙_ (DerivedCategory
              (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
                (condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) Y.left)))) ⟶
            𝟙_ _) ≫
      (derivedExtendScalars (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) Y.left).map
        (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
          (integersModPowCoeff.{u} ℓ E (n + 1)) Y.left).inv ≫
      (comparisonUpperStarDerivedExtendScalarsIso (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) Y.left).hom.app (𝟙_ _) ≫
      D(ν^*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]).map
        (Etale.derivedExtendScalarsConstantComplexIso
          (integersModPowCoeffTransition_surjective ℓ E n)
          (ker_integersModPowCoeffTransition ℓ E n) Y.left).hom =
    (finiteCoefficientDerivedEquivalenceExtendScalarsIso Y.left
        (PadicAlgCl.integersModPowTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n)).hom.app (𝟙_ (DerivedCategory
          (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
            (condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) Y.left)))) ≫
      (finiteCoefficientDerivedEquivalence Y.left
        (PadicAlgCl.integersModPow ℓ E n)).functor.map
        (η (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctor) ≫
      ((finiteCoefficientDerivedEquivalenceUnitIso Y.left
        (PadicAlgCl.integersModPow ℓ E n)).hom :
        (finiteCoefficientDerivedEquivalence Y.left
          (PadicAlgCl.integersModPow ℓ E n)).functor.obj (𝟙_ (DerivedCategory
            (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
              (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y.left)))) ⟶
          𝟙_ _) ≫
      (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
        (integersModPowCoeff.{u} ℓ E n) Y.left).inv := by
  have h₁ := map_inv_comp_comparisonUpperStarDerivedExtendScalarsIso_hom_app_comp_map_hom
    (integersModPowCoeffTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
    Y.left
  have h₂ := finiteCoefficientDerivedEquivalenceExtendScalarsIso_hom_app_unit_comp Y.left
    (PadicAlgCl.integersModPowTransition_surjective ℓ E n)
    (ker_integersModPowCoeffTransition ℓ E n)
  refine (congrArg (_ ≫ ·) h₁).trans ?_
  have h₃ := h₂ =≫ (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
    (integersModPowCoeff.{u} ℓ E n) Y.left).inv
  simp only [Category.assoc] at h₃
  exact h₃.symm

set_option maxHeartbeats 1000000 in
-- the monoidal structures of the derived functors on sheaf categories are slow to unfold
/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity.

**The comparisons of the étale reading with `Ψ` preserve the units**: the derived extension of
scalars `Ψ` of the identification `Rν_* Φ(𝟙) ≅ 𝟙` modulo `ℓⁿ⁺¹`
(`finiteCoefficientDerivedEquivalenceUnitIso`, `rightDerivedComparisonLowerStarUnitIso`), followed
by `Ψ Λ ≅ Λ'`, is the base change map `Ψ Rν_* ⟶ Rν_* Ψ`
(`ProEtale.derivedExtendScalarsComparisonLowerStarMap`), followed by the compatibility of `Φ` with
the extensions of scalars (`ProEtale.finiteCoefficientDerivedEquivalenceExtendScalarsIso`), the
unit comparison of the condensed extension of scalars and the identification modulo `ℓⁿ`. -/
theorem map_readingUnitIso_hom_comp_constantComplexIso :
    letI := Mod.extendScalarsMonoidal (integersModPowTransition Y.left ℓ E n)
    letI := (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctorMonoidal
    (integersModPowDerivedExtendScalars ℓ E n Y.left).map
        ((R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))])).map
          ((finiteCoefficientDerivedEquivalenceUnitIso Y.left
            (PadicAlgCl.integersModPow ℓ E (n + 1))).hom :
            (finiteCoefficientDerivedEquivalence Y.left
              (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.obj (𝟙_ (DerivedCategory
                (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
                  (condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) Y.left)))) ⟶
              𝟙_ _) ≫
          (rightDerivedComparisonLowerStarUnitIso Y.left
            (integersModPowCoeff.{u} ℓ E (n + 1))).hom) ≫
      (Etale.derivedExtendScalarsConstantComplexIso
        (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) Y.left).hom =
    (derivedExtendScalarsComparisonLowerStarMap (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) Y.left).app
        ((finiteCoefficientDerivedEquivalence Y.left
          (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.obj (𝟙_ (DerivedCategory
                (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
                  (condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) Y.left))))) ≫
      (R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).map
        ((finiteCoefficientDerivedEquivalenceExtendScalarsIso Y.left
            (PadicAlgCl.integersModPowTransition_surjective ℓ E n)
            (ker_integersModPowCoeffTransition ℓ E n)).hom.app (𝟙_ (DerivedCategory
                (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
                  (condensedRingObj (Profinite.integersModPowRingObj ℓ E (n + 1)) Y.left)))) ≫
          (finiteCoefficientDerivedEquivalence Y.left
            (PadicAlgCl.integersModPow ℓ E n)).functor.map
            (η (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctor) ≫
          ((finiteCoefficientDerivedEquivalenceUnitIso Y.left
            (PadicAlgCl.integersModPow ℓ E n)).hom :
            (finiteCoefficientDerivedEquivalence Y.left
              (PadicAlgCl.integersModPow ℓ E n)).functor.obj (𝟙_ (DerivedCategory
                (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
                  (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y.left)))) ⟶
              𝟙_ _)) ≫
      (rightDerivedComparisonLowerStarUnitIso Y.left (integersModPowCoeff.{u} ℓ E n)).hom := by
  have hP := map_unitIso_hom_comp_comparisonUpperStarDerivedExtendScalarsIso_hom ℓ E n Y
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))) Y.left (𝟙_ _)
    ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Y.left (𝟙_ _)
    ⟨0, _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _) 0⟩
  -- the unit of `ν^* ⊣ Rν_*` and the base change map
  have hu := map_unit_app_comp_derivedExtendScalarsComparisonLowerStarMap_app
    (integersModPowCoeffTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
    Y.left (𝟙_ _)
  have h₁ : (integersModPowDerivedExtendScalars ℓ E n Y.left).map
        (CategoryTheory.inv ((derivedComparisonAdjunction
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))) Y.left).unit.app (𝟙_ _))) ≫
        (derivedComparisonAdjunction
          (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Y.left).unit.app
          ((integersModPowDerivedExtendScalars ℓ E n Y.left).obj (𝟙_ _)) =
      (derivedExtendScalarsComparisonLowerStarMap (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) Y.left).app
        (D(ν^*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))]).obj (𝟙_ _)) ≫
      R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]).map
        ((comparisonUpperStarDerivedExtendScalarsIso
          (integersModPowCoeffTransition_surjective ℓ E n)
          (ker_integersModPowCoeffTransition ℓ E n) Y.left).hom.app (𝟙_ _)) := by
    rw [Functor.map_inv, IsIso.inv_comp_eq, reassoc_of% hu, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hn := (derivedComparisonAdjunction
    (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Y.left).unit.naturality
      (Etale.derivedExtendScalarsConstantComplexIso
        (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) Y.left).hom
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hn
  have hPR := congrArg (R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).map hP
  simp only [Functor.map_comp] at hPR
  simp only [rightDerivedComparisonLowerStarUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, Functor.map_comp, Category.assoc]
  rw [← cancel_mono ((derivedComparisonAdjunction
    (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Y.left).unit.app (𝟙_ _))]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  erw [hn]
  erw [reassoc_of% h₁]
  rw [NatTrans.map_map_comp_app_comp, NatTrans.map_map_comp_app_comp]
  congr 1

/-- The condensed constituent `red_m 𝒪 ≅ 𝟙` of the identification `red_Y 𝒪 ≅ Λ`
(`etaleReductionUnitIso`): the compatibility of the bounded constructible reduction with the
inclusion, followed by the unit comparison of the monoidal derived extension of scalars. -/
noncomputable def integersModPowReductionUnitIso (m : ℕ) :
    ((boundedConstructibleIntegersModPowReduction Y.left ℓ E m).obj (𝟙_ _)).obj ≅
      𝟙_ (DerivedCategory (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
        (condensedRingObj (Profinite.integersModPowRingObj ℓ E m) Y.left))) :=
  letI := Mod.extendScalarsMonoidal (integersModPowReduction Y.left ℓ E m)
  letI := (Mod.extendScalars (integersModPowReduction Y.left ℓ E m)).leftDerivedFunctorMonoidal
  (boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E m).app (𝟙_ _) ≪≫
    (Functor.Monoidal.εIso _).symm

omit [Fact (ringChar k).Prime] in
/-- `etaleReductionUnitIso`, unfolded through `integersModPowReductionUnitIso`. -/
lemma etaleReductionUnitIso_hom_eq (m : ℕ) :
    (etaleReductionUnitIso ℓ E m Y).hom =
      (R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E m)])).map
        ((finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E m)).functor.map
            (integersModPowReductionUnitIso ℓ E Y m).hom ≫
          ((finiteCoefficientDerivedEquivalenceUnitIso Y.left
            (PadicAlgCl.integersModPow ℓ E m)).hom :
            (finiteCoefficientDerivedEquivalence Y.left
              (PadicAlgCl.integersModPow ℓ E m)).functor.obj (𝟙_ (DerivedCategory
                (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
                  (condensedRingObj (Profinite.integersModPowRingObj ℓ E m) Y.left)))) ⟶
              𝟙_ _)) ≫
        (rightDerivedComparisonLowerStarUnitIso Y.left (integersModPowCoeff.{u} ℓ E m)).hom :=
  rfl

set_option maxHeartbeats 4000000 in
-- the monoidal structures of the derived functors on sheaf categories are slow to unfold
omit [Fact (ringChar k).Prime] [IsSeparated Y.hom] in
/-- The condensed unit comparisons, composed with the bounded constructible inclusion, are
compatible with the transitivity of the derived extensions of scalars. -/
lemma map_η_comp_η_integersModPowReduction :
    letI := Mod.extendScalarsMonoidal (integersModPowReduction Y.left ℓ E (n + 1))
    letI := Mod.extendScalarsMonoidal (integersModPowTransition Y.left ℓ E n)
    letI := Mod.extendScalarsMonoidal (integersModPowReduction Y.left ℓ E n)
    letI :=
      (Mod.extendScalars (integersModPowReduction Y.left ℓ E (n + 1))).leftDerivedFunctorMonoidal
    letI := (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctorMonoidal
    letI := (Mod.extendScalars (integersModPowReduction Y.left ℓ E n)).leftDerivedFunctorMonoidal
    (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctor.map
        (η ((boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E)
          Y.left)).ι ⋙
            (Mod.extendScalars (integersModPowReduction Y.left ℓ E (n + 1))).leftDerivedFunctor)) ≫
      η (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctor =
    (Mod.derivedExtendScalarsCompIso _ _ _
        (integersModPowReduction_comp_integersModPowTransition Y.left ℓ E n)).inv.app
        ((boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E)
          Y.left)).ι.obj (𝟙_ _)) ≫
      η ((boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E)
          Y.left)).ι ⋙
            (Mod.extendScalars (integersModPowReduction Y.left ℓ E n)).leftDerivedFunctor) := by
  -- the condensed part: the transitivity isomorphism preserves the units
  have hc := map_ε_comp_derivedExtendScalarsCompIso_inv_app_comp_η
    (integersModPowReduction Y.left ℓ E (n + 1)) (integersModPowTransition Y.left ℓ E n)
    (integersModPowReduction Y.left ℓ E n)
    (integersModPowReduction_comp_integersModPowTransition Y.left ℓ E n)
  have K₀ :
      letI := Mod.extendScalarsMonoidal (integersModPowReduction Y.left ℓ E (n + 1))
      letI := Mod.extendScalarsMonoidal (integersModPowTransition Y.left ℓ E n)
      letI := Mod.extendScalarsMonoidal (integersModPowReduction Y.left ℓ E n)
      letI :=
        (Mod.extendScalars (integersModPowReduction Y.left ℓ E (n + 1))).leftDerivedFunctorMonoidal
      letI := (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctorMonoidal
      letI := (Mod.extendScalars (integersModPowReduction Y.left ℓ E n)).leftDerivedFunctorMonoidal
      (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctor.map
          (η (Mod.extendScalars (integersModPowReduction Y.left ℓ E (n + 1))).leftDerivedFunctor) ≫
        η (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctor =
      (Mod.derivedExtendScalarsCompIso _ _ _
          (integersModPowReduction_comp_integersModPowTransition Y.left ℓ E n)).inv.app (𝟙_ _) ≫
        η (Mod.extendScalars (integersModPowReduction Y.left ℓ E n)).leftDerivedFunctor := by
    rw [← hc]
    rw [← Functor.map_comp_assoc]
    rw [Functor.Monoidal.η_ε]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (Mod.derivedExtendScalarsCompIso _ _ _
    (integersModPowReduction_comp_integersModPowTransition Y.left ℓ E n)).inv.naturality
    (η (boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)).ι)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Functor.OplaxMonoidal.comp_η, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  congr 1

set_option maxHeartbeats 1000000 in
-- the monoidal structures of the derived functors on sheaf categories are slow to unfold
omit [Fact (ringChar k).Prime] [IsSeparated Y.hom] in
/-- The condensed transition `(𝒪_E ⧸ ℓⁿ) ⊗ᴸ red_{n+1} K ≅ red_n K` at the unit, through the
identifications `red_m 𝒪 ≅ 𝟙`, is the unit comparison of the derived extension of scalars along
`𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` (`map_ε_comp_derivedExtendScalarsCompIso_inv_app_comp_η`). -/
lemma boundedConstructibleIntegersModPowReductionTransitionIso_hom_app_unit :
    letI := Mod.extendScalarsMonoidal (integersModPowTransition Y.left ℓ E n)
    letI := (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctorMonoidal
    (boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n Y.left).hom.app (𝟙_ _) =
      (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctor.map
          (integersModPowReductionUnitIso ℓ E Y (n + 1)).hom ≫
        η (Mod.extendScalars (integersModPowTransition Y.left ℓ E n)).leftDerivedFunctor ≫
          (integersModPowReductionUnitIso ℓ E Y n).inv := by
  have K₁ := map_η_comp_η_integersModPowReduction ℓ E n Y
  rw [boundedConstructibleIntegersModPowReductionTransitionIso_hom_app]
  simp only [integersModPowReductionUnitIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.Monoidal.εIso_inv, Functor.Monoidal.εIso_hom, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  have hηε :
      letI := Mod.extendScalarsMonoidal (integersModPowReduction Y.left ℓ E n)
      letI := (Mod.extendScalars (integersModPowReduction Y.left ℓ E n)).leftDerivedFunctorMonoidal
      η ((boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E)
          Y.left)).ι ⋙
            (Mod.extendScalars (integersModPowReduction Y.left ℓ E n)).leftDerivedFunctor) ≫
        ε ((boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E)
          Y.left)).ι ⋙
            (Mod.extendScalars (integersModPowReduction Y.left ℓ E n)).leftDerivedFunctor) =
        𝟙 _ := by
    simp only [Functor.OplaxMonoidal.comp_η, Functor.LaxMonoidal.comp_ε, Category.assoc,
      Functor.Monoidal.η_ε_assoc, ← Functor.map_comp, Functor.Monoidal.η_ε,
      CategoryTheory.Functor.map_id]
    rfl
  rw [reassoc_of% K₁, reassoc_of% hηε]

set_option maxHeartbeats 1000000 in
-- the monoidal structures of the derived functors on sheaf categories are slow to unfold
/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity.

**The reduction `β` is compatible with the units**: through `β : Ψ(red_{n+1} 𝒪) ≅ red_n 𝒪`, the
derived extension of scalars `Ψ` of the identification `red_Y 𝒪 ≅ Λ` modulo `ℓⁿ⁺¹`
(`etaleReductionUnitIso`), followed by `Ψ Λ ≅ Λ'`
(`Etale.derivedExtendScalarsConstantComplexIso`), is the identification modulo `ℓⁿ`. -/
theorem map_etaleReductionUnitIso_hom_comp_constantComplexIso :
    (integersModPowDerivedExtendScalars ℓ E n Y.left).map
          (etaleReductionUnitIso ℓ E (n + 1) Y).hom ≫
        (Etale.derivedExtendScalarsConstantComplexIso
          (integersModPowCoeffTransition_surjective ℓ E n)
          (ker_integersModPowCoeffTransition ℓ E n) Y.left).hom =
      (etaleReductionExtendScalarsIsoApp ℓ E n Y (𝟙_ _)).hom ≫
        (etaleReductionUnitIso ℓ E n Y).hom := by
  have hr := map_readingUnitIso_hom_comp_constantComplexIso ℓ E n Y
  simp only [Functor.map_comp, Category.assoc] at hr
  rw [etaleReductionUnitIso_hom_eq, etaleReductionUnitIso_hom_eq,
    etaleReductionExtendScalarsIsoApp_hom, finiteEtaleReadingExtendScalarsMap_app]
  simp only [Functor.comp_map]
  rw [boundedConstructibleIntegersModPowReductionTransitionIso_hom_app_unit]
  simp only [Functor.map_comp, Category.assoc]
  refine (congrArg (fun t ↦ _ ≫ t) hr).trans ?_
  conv_rhs => rhs; rhs; rhs; rhs; rw [Functor.map_map_inv_comp_map_map_hom_comp]
  conv_rhs => rhs; erw [← NatTrans.map_map_map_comp_map_app_comp
    (R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]))
    (finiteCoefficientDerivedEquivalenceExtendScalarsIso Y.left
      (PadicAlgCl.integersModPowTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n)).hom]
  conv_rhs => erw [← NatTrans.map_map_comp_app_comp
    (derivedExtendScalarsComparisonLowerStarMap (integersModPowCoeffTransition_surjective ℓ E n)
      (ker_integersModPowCoeffTransition ℓ E n) Y.left)]

end AlgebraicGeometry.ProEtale.CondensedRing
