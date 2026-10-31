/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionResMate2

/-!
# The transpose of the étale reading of the reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`

The isomorphism `β : Ψ(ρ(red_{n+1} K)) ≅ ρ(red_n K)`
(`ProEtale.CondensedRing.etaleReductionExtendScalarsIsoApp`)
is determined by its transpose under `Ψ ⊣ Res`, a morphism `ρ(red_{n+1} K) ⟶ Res ρ(red_n K)`.
This file computes it: followed by the base change map `Res Rν_* ⟶ Rν_* Res`
(`ProEtale.derivedRestrictScalarsCompComparisonLowerStarMap`), it is `Rν_*` of the image under the
finite-coefficient comparison `Φ` of the condensed transition
`red_{n+1} K ⟶ Res((𝒪_E ⧸ ℓⁿ) ⊗ᴸ red_{n+1} K) ≅ Res(red_n K)`
(`ProEtale.CondensedRing.unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom`).

On the way, the compatibility of the extensions of scalars with the finite-coefficient comparison
is put in restriction form
(`ProEtale.unit_app_comp_map_finiteCoefficientDerivedEquivalenceExtendScalarsIso_hom_app`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

section ExtendScalars

variable (X : Scheme.{u}) {T T' : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
  [DiscreteTopology T'] [Finite T'] {ρ : T →+* T'} (hρ : Function.Surjective ρ)
  {a : ULift.{u + 1} T} (ha : RingHom.ker ρ.ulift = Ideal.span {a})

set_option maxHeartbeats 800000 in
-- the composites of derived functors between sheaf categories are slow to elaborate
/-- **The compatibility of the extensions of scalars with the finite-coefficient comparison, in
restriction form**: the transpose under `Ψ ⊣ Res` of `Ψ(Φ N) ≅ Φ'((𝒪') ⊗ᴸ N)` is `Φ` of the
unit `N ⟶ Res((𝒪') ⊗ᴸ N)` of the condensed extension of scalars, followed by the commutation of
`Φ` with the restrictions of scalars. -/
lemma unit_app_comp_map_finiteCoefficientDerivedEquivalenceExtendScalarsIso_hom_app
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))) :
    (ProEtale.derivedExtendScalarsAdjunction (φ := ρ.ulift) (fun y ↦ ⟨⟨(hρ y.down).choose⟩,
        ULift.ext _ _ (hρ y.down).choose_spec⟩) ha X).unit.app
          ((finiteCoefficientDerivedEquivalence X T).functor.obj N) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ.ulift).map
        ((finiteCoefficientDerivedEquivalenceExtendScalarsIso X hρ ha).hom.app N) =
    (finiteCoefficientDerivedEquivalence X T).functor.map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap
          (Profinite.continuousMapRingObjMap.{u} ρ continuous_of_discreteTopology) X)).unit.app N) ≫
      (finiteCoefficientDerivedEquivalenceComapIso X ρ).hom.app
        ((Mod.extendScalars (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) X)).leftDerivedFunctor.obj N) := by
  let Φ := finiteCoefficientDerivedEquivalence X T
  let Φ' := finiteCoefficientDerivedEquivalence X T'
  let ψ := coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ continuous_of_discreteTopology) X
  let adjP := ProEtale.derivedExtendScalarsAdjunction (φ := ρ.ulift) (fun y ↦ ⟨⟨(hρ y.down).choose⟩,
    ULift.ext _ _ (hρ y.down).choose_spec⟩) ha X
  let i := finiteCoefficientDerivedEquivalenceComapIso X ρ
  have h := unit_conjugateEquiv_symm ((Mod.derivedExtendMapDerivedCategoryAdjunction ψ).comp
    Φ'.toAdjunction) (Φ.toAdjunction.comp adjP)
    (Iso.isoCompInverse ((Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Φ'.inverse i ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight Φ'.counitIso _ ≪≫
      Functor.leftUnitor _))).hom N
  apply (Φ.toAdjunction.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Equivalence.toAdjunction_unit]
  have h' := h.symm
  simp only [Adjunction.comp_unit_app, Equivalence.toAdjunction_unit, Functor.comp_map,
    Category.assoc] at h'
  erw [h']
  have n1 := Φ.unitIso.hom.naturality
    ((Mod.derivedExtendMapDerivedCategoryAdjunction ψ).unit.app N ≫
      (Mod.comap ψ).mapDerivedCategory.map
        (Φ'.unitIso.hom.app ((Mod.extendScalars ψ).leftDerivedFunctor.obj N)))
  have n2 := i.hom.naturality (Φ'.unitIso.hom.app ((Mod.extendScalars ψ).leftDerivedFunctor.obj N))
  have t := Φ'.functor_unit_comp ((Mod.extendScalars ψ).leftDerivedFunctor.obj N)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at n1 n2
  simp only [Iso.isoCompInverse_hom_app, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Iso.symm_hom, Category.id_comp, Functor.map_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Functor.map_id,
    Category.comp_id]
  have key : Φ.functor.map ((Mod.comap ψ).mapDerivedCategory.map
      (Φ'.unitIso.hom.app ((Mod.extendScalars ψ).leftDerivedFunctor.obj N))) ≫
        i.hom.app
          (Φ'.inverse.obj (Φ'.functor.obj ((Mod.extendScalars ψ).leftDerivedFunctor.obj N))) ≫
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) ρ.ulift).map
          (Φ'.counitIso.hom.app (Φ'.functor.obj ((Mod.extendScalars ψ).leftDerivedFunctor.obj N))) =
      i.hom.app ((Mod.extendScalars ψ).leftDerivedFunctor.obj N) := by
    rw [reassoc_of% n2, ← Functor.map_comp]
    erw [t, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc]
  erw [n1]
  have key₂ := congrArg Φ.inverse.map key
  simp only [Functor.map_comp] at key₂
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun g ↦ Φ.unitIso.hom.app N ≫ Φ.inverse.map (Φ.functor.map
    ((Mod.derivedExtendMapDerivedCategoryAdjunction ψ).unit.app N)) ≫ g) key₂

end ExtendScalars
end AlgebraicGeometry.ProEtale

/-- An elementary transport of transposes along the functors of the étale reading, used for
`unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom`. -/
lemma _root_.CategoryTheory.Functor.transpose_comp_eq_aux {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category C₁]
    [Category C₂] [Category C₃] [Category C₄] [Category C₅] [Category C₆] (Re : C₂ ⥤ C₁)
    (Rν' : C₃ ⥤ C₂) (Rν : C₄ ⥤ C₁) (Rp : C₃ ⥤ C₄) (Φ : C₅ ⥤ C₄) (Φ' : C₆ ⥤ C₃) (Rc : C₆ ⥤ C₅)
    {p : C₂} {s₁ : C₃} {c₀ : C₅} {c₁ c₂ : C₆}
    (u : Rν.obj (Φ.obj c₀) ⟶ Re.obj p) (γ : p ⟶ Rν'.obj s₁) (ext : s₁ ⟶ Φ'.obj c₁)
    (ω : c₁ ⟶ c₂) (ω₁ : Re.obj (Rν'.obj s₁) ⟶ Rν.obj (Rp.obj s₁))
    (ω₂ : Re.obj (Rν'.obj (Φ'.obj c₂)) ⟶ Rν.obj (Rp.obj (Φ'.obj c₂)))
    (up : Φ.obj c₀ ⟶ Rp.obj s₁) (η : c₀ ⟶ Rc.obj c₁) (i₁ : Φ.obj (Rc.obj c₁) ⟶ Rp.obj (Φ'.obj c₁))
    (i₂ : Φ.obj (Rc.obj c₂) ⟶ Rp.obj (Φ'.obj c₂))
    (hstar : u ≫ Re.map γ ≫ ω₁ = Rν.map up)
    (hω : Re.map (Rν'.map (ext ≫ Φ'.map ω)) ≫ ω₂ = ω₁ ≫ Rν.map (Rp.map (ext ≫ Φ'.map ω)))
    (hExt : up ≫ Rp.map ext = Φ.map η ≫ i₁)
    (hi : Φ.map (Rc.map ω) ≫ i₂ = i₁ ≫ Rp.map (Φ'.map ω)) :
    u ≫ Re.map ((γ ≫ Rν'.map ext) ≫ Rν'.map (Φ'.map ω)) ≫ ω₂ =
      Rν.map (Φ.map (η ≫ Rc.map ω) ≫ i₂) := by
  rw [Category.assoc, ← Rν'.map_comp, Re.map_comp, Category.assoc, hω, reassoc_of% hstar,
    ← Rν.map_comp, Rp.map_comp, reassoc_of% hExt, ← hi, Φ.map_comp, Category.assoc]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

set_option maxHeartbeats 800000 in
-- the composites of derived functors between sheaf categories are slow to elaborate
/-- Blueprint `det-sp-purity-coefficient-change` (restriction form of `β`). **The transpose of
`β : Ψ(ρ(red_{n+1} K)) ≅ ρ(red_n K)` under `Ψ ⊣ Res`**, followed by the base change map
`Res Rν_* ⟶ Rν_* Res`, is `Rν_*` of `Φ` of the condensed transition
`red_{n+1} K ⟶ Res((𝒪_E ⧸ ℓⁿ) ⊗ᴸ red_{n+1} K) ≅ Res(red_n K)`, followed by the commutation of `Φ`
with the restrictions of scalars. -/
theorem unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (Etale.derivedExtendScalarsAdjunction (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) X.left).unit.app
        ((finiteEtaleReading ℓ E (n + 1) X).obj
          ((boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj K)) ≫
      (Sheaf.derivedRestrictScalars X.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).map
          (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom ≫
      (derivedRestrictScalarsCompComparisonLowerStarMap (integersModPowCoeffTransition ℓ E n)
        X.left).app ((finiteCoefficientDerivedEquivalence X.left
          (PadicAlgCl.integersModPow ℓ E n)).functor.obj ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K))) =
    (R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))])).map
      ((finiteCoefficientDerivedEquivalence X.left
          (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.map
          ((Mod.derivedExtendMapDerivedCategoryAdjunction
              (integersModPowTransition X.left ℓ E n)).unit.app
              ((boundedConstructible _).ι.obj
                ((boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj K)) ≫
            (Mod.comap (integersModPowTransition X.left ℓ E n)).mapDerivedCategory.map
              ((boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X.left).hom.app K)) ≫
        (finiteCoefficientDerivedEquivalenceComapIso X.left
          (PadicAlgCl.integersModPowTransition ℓ E n)).hom.app ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K))) := by
  have hstar := unit_app_comp_map_derivedExtendScalarsComparisonLowerStarMap_app X.left
    (integersModPowCoeffTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
    ((finiteCoefficientDerivedEquivalence X.left
      (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.obj
      ((boundedConstructible _).ι.obj ((boundedConstructibleIntegersModPowReduction X.left ℓ E
        (n + 1)).obj K)))
  have hExt := unit_app_comp_map_finiteCoefficientDerivedEquivalenceExtendScalarsIso_hom_app X.left
    (PadicAlgCl.integersModPowTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
    ((boundedConstructible _).ι.obj ((boundedConstructibleIntegersModPowReduction X.left ℓ E
        (n + 1)).obj K))
  have hω := (derivedRestrictScalarsCompComparisonLowerStarMap (integersModPowCoeffTransition ℓ E n)
    X.left).naturality
      ((finiteCoefficientDerivedEquivalenceExtendScalarsIso X.left
          (PadicAlgCl.integersModPowTransition_surjective ℓ E n)
          (ker_integersModPowCoeffTransition ℓ E n)).hom.app ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj K)) ≫
        (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor.map
          ((boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X.left).hom.app K))
  have hi := (finiteCoefficientDerivedEquivalenceComapIso X.left
    (PadicAlgCl.integersModPowTransition ℓ E n)).hom.naturality
      ((boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X.left).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hω hi
  rw [etaleReductionExtendScalarsIsoApp_hom, finiteEtaleReadingExtendScalarsMap_app]
  exact CategoryTheory.Functor.transpose_comp_eq_aux
    (Sheaf.derivedRestrictScalars X.left.smallEtaleTopology (integersModPowCoeffTransition ℓ E n))
    (R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]))
    (R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))]))
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X.left)
      (integersModPowCoeffTransition ℓ E n))
    (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E (n + 1))).functor
    (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor
    (Mod.comap (integersModPowTransition X.left ℓ E n)).mapDerivedCategory
    _ _ _ _ _ _ _ _ _ _ hstar hω hExt hi

end AlgebraicGeometry.ProEtale.CondensedRing
