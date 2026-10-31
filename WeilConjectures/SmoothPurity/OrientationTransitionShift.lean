/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionShiftApp
public import WeilConjectures.SmoothPurity.OrientationTransitionReading

/-!
# The étale reading of the reductions commutes with the shifts

The isomorphisms `β : Ψ(red_{n+1} K) ≅ red_n K` of the étale readings of the reductions
modulo `ℓⁿ⁺¹` and `ℓⁿ` of a bounded constructible `𝒪_E`-complex `K`
(`ProEtale.CondensedRing.etaleReductionExtendScalarsIsoApp`) commute with the shifts
(`ProEtale.CondensedRing.map_reductionShift_comp_etaleReductionExtendScalarsIsoApp`), for the
commutations of the reductions with the shifts
(`ProEtale.CondensedRing.boundedConstructibleIntegersModPowReductionShiftIso`),
of the étale readings with the shifts and of `Ψ = - ⊗ᴸ_{𝒪_E ⧸ ℓⁿ⁺¹} 𝒪_E ⧸ ℓⁿ` with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

section Reading

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- `finiteEtaleReadingExtendScalarsMap` with the associators made explicit, so that the shift
structures of the composite functors match those of its constituents. -/
noncomputable def finiteEtaleReadingExtendScalarsMap' :
    finiteEtaleReading ℓ E (n + 1) X ⋙ integersModPowDerivedExtendScalars ℓ E n X.left ⟶
      (boundedConstructible _).ι ⋙
        (Mod.extendScalars (integersModPowTransition X.left ℓ E n)).leftDerivedFunctor ⋙
          (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
            R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)]) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (boundedConstructible _).ι (Functor.whiskerLeft
      (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E (n + 1))).functor
      (derivedExtendScalarsComparisonLowerStarMap (integersModPowCoeffTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n) X.left)) ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).inv ≫
    Functor.whiskerLeft (boundedConstructible _).ι
      (Functor.whiskerRight (finiteCoefficientDerivedEquivalenceExtendScalarsIso X.left
        (PadicAlgCl.integersModPowTransition_surjective ℓ E n)
        (ker_integersModPowCoeffTransition ℓ E n)).hom
        R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])) ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).hom

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
lemma finiteEtaleReadingExtendScalarsMap'_eq :
    finiteEtaleReadingExtendScalarsMap' ℓ E n X = finiteEtaleReadingExtendScalarsMap ℓ E n X := by
  ext M
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, finiteEtaleReadingExtendScalarsMap',
    Functor.whiskerLeft_twice, Category.assoc, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Category.comp_id, Category.id_comp, finiteEtaleReadingExtendScalarsMap]
  exact Category.id_comp _

set_option synthInstance.maxHeartbeats 400000 in
-- The `CommShift` instance of a composite of many whiskered natural transformations is found by
-- a long instance search.
instance commShift_finiteEtaleReadingExtendScalarsMap' :
    NatTrans.CommShift (finiteEtaleReadingExtendScalarsMap' ℓ E n X) ℤ := by
  dsimp only [finiteEtaleReadingExtendScalarsMap']
  infer_instance

end Reading

section Condensed

variable (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] (m : ℕ)

/-- The reduction modulo `ℓᵐ` of bounded constructible `𝒪_E`-complexes commutes with the shifts,
as the lift of the derived extension of scalars. -/
noncomputable instance commShift_boundedConstructibleIntegersModPowReduction :
    (boundedConstructibleIntegersModPowReduction X ℓ E m).CommShift ℤ := by
  dsimp only [boundedConstructibleIntegersModPowReduction]
  infer_instance

instance commShift_boundedConstructibleIntegersModPowReductionCompatibility_hom :
    NatTrans.CommShift
      (boundedConstructibleIntegersModPowReductionCompatibility X ℓ E m).hom ℤ := by
  dsimp only [boundedConstructibleIntegersModPowReductionCompatibility,
    commShift_boundedConstructibleIntegersModPowReduction]
  infer_instance

/-- The commutation of the reduction with the shifts given by its shift structure is the explicit
`boundedConstructibleIntegersModPowReductionShiftIso`. -/
lemma boundedConstructibleIntegersModPowReduction_commShiftIso_app
    (K : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧) (q : ℤ) :
    ((boundedConstructibleIntegersModPowReduction X ℓ E m).commShiftIso q).app K =
      boundedConstructibleIntegersModPowReductionShiftIso ℓ E m X K q := by
  apply Iso.ext
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  have h : ((boundedConstructibleIntegersModPowReduction X ℓ E m).commShiftIso q) =
      Functor.CommShift.OfComp.iso
        (boundedConstructibleIntegersModPowReductionCompatibility X ℓ E m) q := rfl
  rw [boundedConstructibleIntegersModPowReductionShiftIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, h, Iso.app_hom, Functor.CommShift.OfComp.map_iso_hom_app]
  simp [Functor.commShiftIso_comp_hom_app]

lemma boundedConstructibleIntegersModPowReduction_commShiftIso_hom_app
    (K : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧) (q : ℤ) :
    ((boundedConstructibleIntegersModPowReduction X ℓ E m).commShiftIso q).hom.app K =
      (boundedConstructibleIntegersModPowReductionShiftIso ℓ E m X K q).hom := by
  rw [← Iso.app_hom, boundedConstructibleIntegersModPowReduction_commShiftIso_app]

/-- The condensed transition `(𝒪_E ⧸ ℓⁿ) ⊗ᴸ red_{n+1} - ≅ red_n -` commutes with the shifts. -/
instance commShift_boundedConstructibleIntegersModPowReductionTransitionIso_hom :
    NatTrans.CommShift
      (boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X).hom ℤ := by
  dsimp only [boundedConstructibleIntegersModPowReductionTransitionIso,
    Mod.derivedExtendScalarsCompIso, Mod.mapDerivedCategoryComapCompIso]
  infer_instance

end Condensed

section Reading

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- `etaleReductionExtendScalarsIso`, as a natural transformation between the composites
`red_{n+1} ⋙ ρ ⋙ Ψ` and `red_n ⋙ ρ`, with the associators made explicit. -/
noncomputable def etaleReductionExtendScalarsMap' :
    boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1) ⋙
        (finiteEtaleReading ℓ E (n + 1) X ⋙ integersModPowDerivedExtendScalars ℓ E n X.left) ⟶
      boundedConstructibleIntegersModPowReduction X.left ℓ E n ⋙ finiteEtaleReading ℓ E n X :=
  Functor.whiskerLeft _ (finiteEtaleReadingExtendScalarsMap' ℓ E n X) ≫
    (Functor.associator _ _ _).inv ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((Functor.associator _ _ _).hom ≫
      (boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X.left).hom)
      ((finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
        R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])) ≫
    (Functor.associator _ _ _).hom

set_option synthInstance.maxHeartbeats 400000 in
-- The `CommShift` instance of a composite of many whiskered natural transformations is found by
-- a long instance search.
instance commShift_etaleReductionExtendScalarsMap' :
    NatTrans.CommShift (etaleReductionExtendScalarsMap' ℓ E n X) ℤ := by
  dsimp only [etaleReductionExtendScalarsMap']
  infer_instance

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
lemma etaleReductionExtendScalarsMap'_app (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (etaleReductionExtendScalarsMap' ℓ E n X).app K =
      (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom := by
  rw [etaleReductionExtendScalarsIsoApp_hom, ← finiteEtaleReadingExtendScalarsMap'_eq]
  simp [etaleReductionExtendScalarsMap']

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- Blueprint `det-sp-purity-coefficient-change` (shifts). **The isomorphisms
`β : Ψ(red_{n+1} K) ≅ red_n K` commute with the shifts**: through the commutations of the
reductions with the shifts (`boundedConstructibleIntegersModPowReductionShiftIso`), of the étale
readings and of `Ψ` with the shifts, `β` at `K⟦q⟧` is `β` at `K` shifted by `q`. -/
theorem map_reductionShift_comp_etaleReductionExtendScalarsIsoApp
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) (q : ℤ) :
    (integersModPowDerivedExtendScalars ℓ E n X.left).map
        ((finiteEtaleReading ℓ E (n + 1) X).map
          (boundedConstructibleIntegersModPowReductionShiftIso ℓ E (n + 1) X.left K q).hom ≫
        ((finiteEtaleReading ℓ E (n + 1) X).commShiftIso q).hom.app
          ((boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj K)) ≫
      ((integersModPowDerivedExtendScalars ℓ E n X.left).commShiftIso q).hom.app
        ((finiteEtaleReading ℓ E (n + 1) X).obj
          ((boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj K)) ≫
      (etaleReductionExtendScalarsIsoApp ℓ E n X K).hom⟦q⟧' =
    (etaleReductionExtendScalarsIsoApp ℓ E n X (K⟦q⟧)).hom ≫
      (finiteEtaleReading ℓ E n X).map
        (boundedConstructibleIntegersModPowReductionShiftIso ℓ E n X.left K q).hom ≫
      ((finiteEtaleReading ℓ E n X).commShiftIso q).hom.app
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj K) := by
  have h := NatTrans.shift_app_comm (etaleReductionExtendScalarsMap' ℓ E n X) q K
  simp only [Functor.commShiftIso_comp_hom_app,
    boundedConstructibleIntegersModPowReduction_commShiftIso_hom_app,
    etaleReductionExtendScalarsMap'_app] at h
  simpa [Functor.map_comp, Category.assoc] using h

end Reading

end AlgebraicGeometry.ProEtale.CondensedRing
