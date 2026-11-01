/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizingUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction

/-!
# The comparisons of `ν^*` and of `Φ` with the derived extension of scalars at the unit

Write `Ψ` for the derived extension of scalars along a surjective ring morphism with principal
kernel, on the étale site, on the pro-étale site and on module objects over the condensed
coefficient rings. This file states (blueprint `det-sp-purity-coefficient-change`) that the
commutations of `Ψ` with the comparison pullback `ν^*`
(`ProEtale.comparisonUpperStarDerivedExtendScalarsIso`) and with the comparison `Φ` of the two
models of finite coefficients (`ProEtale.finiteCoefficientDerivedEquivalenceExtendScalarsIso`)
are compatible with the unit comparisons `η` of the monoidal functors `Ψ`:

* `ProEtale.map_inv_comp_comparisonUpperStarDerivedExtendScalarsIso_hom_app_comp_map_hom`;
* `ProEtale.finiteCoefficientDerivedEquivalenceExtendScalarsIso_hom_app_unit_comp`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Comparison

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [IsNoetherianRing Λ] {φ : Λ →+* Λ'}
  (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u})

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity.

**The commutation of `ν^*` with `Ψ` preserves the units**: `Ψ` of `𝟙 ≅ ν^* 𝟙`, followed by
`Ψ ν^* ≅ ν^* Ψ` (`comparisonUpperStarDerivedExtendScalarsIso`) and `ν^*(Ψ Λ ≅ Λ')`, is the unit
comparison `Ψ Λ ≅ Λ'` on the pro-étale site followed by `𝟙 ≅ ν^* 𝟙`. -/
theorem map_inv_comp_comparisonUpperStarDerivedExtendScalarsIso_hom_app_comp_map_hom :
    haveI := preservesKFlatQuasiIso_extendScalars hφ ha X
    letI := (Sheaf.extendScalars (Scheme.ProEt.topology X) φ).leftDerivedFunctorMonoidal
    (derivedExtendScalars hφ ha X).map
        (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso Λ X).inv ≫
      (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).hom.app (𝟙_ _) ≫
      D(ν^*(X)[ModuleCat.{u + 1} Λ']).map
        (Etale.derivedExtendScalarsConstantComplexIso hφ ha X).hom =
    η (Sheaf.extendScalars (Scheme.ProEt.topology X) φ).leftDerivedFunctor ≫
      (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso Λ' X).inv := by
  sorry

end Comparison

section FiniteCoefficient

variable (X : Scheme.{u}) {T T' : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
  [DiscreteTopology T'] [Finite T'] {ρ : T →+* T'} (hρ : Function.Surjective ρ)
  {a : ULift.{u + 1} T} (ha : RingHom.ker ρ.ulift = Ideal.span {a})

/-- Blueprint `det-sp-purity-coefficient-change`: change of coefficients in purity.

**The commutation of `Φ` with `Ψ` preserves the units**: the compatibility of `Φ` with the
extensions of scalars (`finiteCoefficientDerivedEquivalenceExtendScalarsIso`) at the unit,
followed by `Φ` of the unit comparison of the condensed `Ψ` and `Φ 𝟙 ≅ 𝟙`, is `Ψ` of
`Φ 𝟙 ≅ 𝟙` followed by the unit comparison of the pro-étale `Ψ`. -/
theorem finiteCoefficientDerivedEquivalenceExtendScalarsIso_hom_app_unit_comp :
    letI := Mod.extendScalarsMonoidal (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
      continuous_of_discreteTopology) X)
    letI := (Mod.extendScalars (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
      continuous_of_discreteTopology) X)).leftDerivedFunctorMonoidal
    haveI := preservesKFlatQuasiIso_extendScalars (φ := ρ.ulift)
      (fun y ↦ ⟨⟨(hρ y.down).choose⟩, ULift.ext _ _ (hρ y.down).choose_spec⟩) ha X
    letI := (Sheaf.extendScalars (Scheme.ProEt.topology X) ρ.ulift).leftDerivedFunctorMonoidal
    (finiteCoefficientDerivedEquivalenceExtendScalarsIso X hρ ha).hom.app (𝟙_ _) ≫
      (finiteCoefficientDerivedEquivalence X T').functor.map
        (η (Mod.extendScalars (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) X)).leftDerivedFunctor) ≫
      (finiteCoefficientDerivedEquivalenceUnitIso X T').hom =
    (derivedExtendScalars (φ := ρ.ulift)
        (fun y ↦ ⟨⟨(hρ y.down).choose⟩, ULift.ext _ _ (hρ y.down).choose_spec⟩) ha X).map
        (finiteCoefficientDerivedEquivalenceUnitIso X T).hom ≫
      η (Sheaf.extendScalars (Scheme.ProEt.topology X) ρ.ulift).leftDerivedFunctor := by
  sorry

end FiniteCoefficient

end AlgebraicGeometry.ProEtale
