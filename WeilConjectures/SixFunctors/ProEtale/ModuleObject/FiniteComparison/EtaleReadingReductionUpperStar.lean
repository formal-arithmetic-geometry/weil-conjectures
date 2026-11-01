/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionResMate2

/-!
# The base change map `Res Rν_* ⟶ Rν_* Res` and the pullbacks

Write `Res` for the restriction of scalars along `φ : Λ →+* Λ'` and
`ω : Res Rν_* ⟶ Rν_* Res` for the base change map of `Res` with `Rν_*`
(`ProEtale.derivedRestrictScalarsCompComparisonLowerStarMap`). This file shows:

* `ProEtale.isIso_derivedRestrictScalarsCompComparisonLowerStarMap`: for a surjective `φ` with
  principal kernel, `ω` is an isomorphism, being the conjugate of the commutation
  `ν^* Ψ ≅ Ψ ν^*` of `ν^*` with the derived extensions of scalars;
* `ProEtale.map_app_comp_rightDerivedComparisonBaseChange_app_comp_map_eq`: `ω` is compatible
  with the base change maps `Lg^* Rν_* ⟶ Rν_* Lg^*` (`ProEtale.rightDerivedComparisonBaseChange`)
  and the commutations of `Res` with the derived pullbacks.

Both are used for the reduction square for the pullbacks (blueprint
`det-sp-purity-coefficient-change`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'}

/-- **The base change map `Res Rν_* ⟶ Rν_* Res` is an isomorphism**: it is the conjugate, under
the composite adjunctions `Ψ ⋙ ν^* ⊣ Rν_* ⋙ Res`, of the isomorphism `ν^* ⋙ Ψ ≅ Ψ ⋙ ν^*`
(`comparisonUpperStarDerivedExtendScalarsIso`). -/
lemma isIso_derivedRestrictScalarsCompComparisonLowerStarMap [IsNoetherianRing Λ]
    (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u}) :
    IsIso (derivedRestrictScalarsCompComparisonLowerStarMap φ X) := by
  have hσ : (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom =
      mateEquiv (Etale.derivedExtendScalarsAdjunction hφ ha X)
        (ProEtale.derivedExtendScalarsAdjunction hφ ha X)
        (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).hom := by
    rw [comparisonUpperStarDerivedExtendScalarsIso_hom_eq]
    exact (Equiv.apply_symm_apply _ _).symm
  have h : derivedRestrictScalarsCompComparisonLowerStarMap φ X =
      conjugateEquiv ((Etale.derivedExtendScalarsAdjunction hφ ha X).comp
          (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') X))
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).comp
          (ProEtale.derivedExtendScalarsAdjunction hφ ha X))
        (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).hom := by
    rw [← iterated_mateEquiv_conjugateEquiv, ← hσ]
    rfl
  rw [h]
  infer_instance

variable (φ) {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- **The base change maps of `Rν_*` with the derived pullbacks commute with the restriction of
scalars**: for `B` over `Λ'` on `Y_proét`, the two morphisms
`Lg^*(Res(Rν_* B)) ⟶ Rν_*(Res(Lg^* B))` obtained from the base change maps
`Lg^* Rν_* ⟶ Rν_* Lg^*` (`rightDerivedComparisonBaseChange`), the base change maps
`Res Rν_* ⟶ Rν_* Res` (`derivedRestrictScalarsCompComparisonLowerStarMap`) and the commutations
of `Res` with `Lg^*` on both sites agree. -/
theorem map_app_comp_rightDerivedComparisonBaseChange_app_comp_map_eq
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ'))) :
    L(Etale.upperStar (ModuleCat.{u + 1} Λ) g).map
        ((derivedRestrictScalarsCompComparisonLowerStarMap φ Y).app B) ≫
      (rightDerivedComparisonBaseChange (ModuleCat.{u + 1} Λ) g).app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).obj B) ≫
      R(ν_*(Z)[ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarRestrictScalarsIso φ g).hom.app B) =
    (Etale.leftDerivedUpperStarRestrictScalarsIso φ g).hom.app
        (R(ν_*(Y)[ModuleCat.{u + 1} Λ']).obj B) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((rightDerivedComparisonBaseChange (ModuleCat.{u + 1} Λ') g).app B) ≫
      (derivedRestrictScalarsCompComparisonLowerStarMap φ Z).app
        (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ') g).obj B) := by
  sorry

end AlgebraicGeometry.ProEtale
