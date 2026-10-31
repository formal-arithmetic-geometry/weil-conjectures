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

The isomorphism `β : Ψ(ρ(red_{n+1} K)) ≅ ρ(red_n K)` (`ProEtale.CondensedRing.etaleReductionExtendScalarsIsoApp`)
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
  trace_state
  sorry

end ExtendScalars
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

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
        (integersModPowCoeffTransition ℓ E n)).map (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom ≫
      (derivedRestrictScalarsCompComparisonLowerStarMap (integersModPowCoeffTransition ℓ E n)
        X.left).app ((finiteCoefficientDerivedEquivalence X.left
          (PadicAlgCl.integersModPow ℓ E n)).functor.obj ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K))) =
    (R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))])).map
      ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.map
          ((Mod.derivedExtendMapDerivedCategoryAdjunction (integersModPowTransition X.left ℓ E n)).unit.app
              ((boundedConstructible _).ι.obj
                ((boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj K)) ≫
            (Mod.comap (integersModPowTransition X.left ℓ E n)).mapDerivedCategory.map
              ((boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X.left).hom.app K)) ≫
        (finiteCoefficientDerivedEquivalenceComapIso X.left
          (PadicAlgCl.integersModPowTransition ℓ E n)).hom.app ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K))) := by
  have hstar := unit_app_comp_map_derivedExtendScalarsComparisonLowerStarMap_app X.left
    (integersModPowCoeffTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
    ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.obj
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
  trace_state
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
