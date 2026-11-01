/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.ReductionTateSheafPowOne
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionTranspose
public import WeilConjectures.TateTwist.IntegralReduction

/-!
# The reduction of the integral Tate twist in degree one: the pieces

The degree-one case of the comparison of the reductions of the integral Tate twists with the
canonical reductions of the Tate twists
(`unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom_comp_tateTwistObjectOneChangeMap`)
splits into:

* a categorical rearrangement (`CategoryTheory.comp_map_comp_eq_of_transpose`);
* the compatibility of `Rν_* ν^* S ≅ S` (`ProEtale.rightDerivedComparisonLowerStarSingleFunctorIso`)
  with morphisms of sheaves and with the restriction of scalars;
* the condensed statement: the transition `red_{n+1} 𝒪_{E,X}(1) ⟶ Res(red_n 𝒪_{E,X}(1))` is, on
  `ν^*` of the Tate sheaves, the change of coefficients `Etale.tateSheafPowOneChangeMap` (the
  `ℓ`-th power map `μ_{ℓⁿ⁺¹} ⟶ μ_{ℓⁿ}`).

The rearrangement, applied to `unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom`,
`etaleReductionIntegralTateTwistIso_hom_eq`,
`derivedRestrictScalars_map_rightDerivedComparisonLowerStarSingleFunctorIso_hom`,
`Etale.tateObjectNatIsoSingleFunctor_inv_comp_tateTwistObjectOneChangeMap`,
`rightDerivedComparisonLowerStarSingleFunctorIso_hom_naturality` and
`finiteCoefficientDerivedEquivalence_map_transition_integralTateTwistOne`, proves the degree-one
case; the kernel check of that application currently needs about 4.7 GB, 1.6 GB of which come
from the instance of the general restriction-of-scalars compatibility at `𝒪_E ⧸ ℓⁿ`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-- A categorical rearrangement for the degree-one reduction of the integral Tate twist: the
transpose `w ≫ Res β ≫ ω = Rν₁ τ`, the factorisations `i₀ = Rν₀ Ψ₀ ≫ r₀ ≫ t₀`,
`i₁ = Rν₁ Ψ₁ ≫ r₁ ≫ t₁`, `Res r₀ = ω ≫ Rν₁ z ≫ r' ≫ θ'`, `t₁ ≫ c = k ≫ θ' ≫ Res t₀`,
`r₁ ≫ k = Rν₁ m ≫ r'` and `τ ≫ Resₚ Ψ₀ ≫ z = Ψ₁ ≫ m` give `w ≫ Res (β ≫ i₀) = i₁ ≫ c`. -/
lemma CategoryTheory.comp_map_comp_eq_of_transpose {E₀ E₁ P₀ P₁ : Type*} [Category* E₀]
    [Category* E₁] [Category* P₀] [Category* P₁] (Res : E₀ ⥤ E₁) (Rν₀ : P₀ ⥤ E₀)
    (Rν₁ : P₁ ⥤ E₁) (Resₚ : P₀ ⥤ P₁) (ω : Rν₀ ⋙ Res ⟶ Resₚ ⋙ Rν₁) {B : E₀} {a : P₁}
    {b Q₀ : P₀} {Q₁ Q₁' : P₁} {S₀ T₀ : E₀} {S₁ S' T₁ : E₁}
    (w : Rν₁.obj a ⟶ Res.obj B) (β : B ⟶ Rν₀.obj b) (τ : a ⟶ Resₚ.obj b)
    (i₀ : Rν₀.obj b ⟶ T₀) (Ψ₀ : b ⟶ Q₀) (r₀ : Rν₀.obj Q₀ ⟶ S₀) (t₀ : S₀ ⟶ T₀)
    (i₁ : Rν₁.obj a ⟶ T₁) (Ψ₁ : a ⟶ Q₁') (r₁ : Rν₁.obj Q₁' ⟶ S₁) (t₁ : S₁ ⟶ T₁)
    (c : T₁ ⟶ Res.obj T₀) (z : Resₚ.obj Q₀ ⟶ Q₁) (r' : Rν₁.obj Q₁ ⟶ S') (θ' : S' ⟶ Res.obj S₀)
    (k : S₁ ⟶ S') (m : Q₁' ⟶ Q₁)
    (htr : w ≫ Res.map β ≫ ω.app b = Rν₁.map τ) (hi₀ : i₀ = Rν₀.map Ψ₀ ≫ r₀ ≫ t₀)
    (hi₁ : i₁ = Rν₁.map Ψ₁ ≫ r₁ ≫ t₁) (hr₀ : Res.map r₀ = ω.app Q₀ ≫ Rν₁.map z ≫ r' ≫ θ')
    (hc : t₁ ≫ c = k ≫ θ' ≫ Res.map t₀) (hr₁ : r₁ ≫ k = Rν₁.map m ≫ r')
    (hΨ : τ ≫ Resₚ.map Ψ₀ ≫ z = Ψ₁ ≫ m) :
    w ≫ Res.map (β ≫ i₀) = i₁ ≫ c := by
  have hω := ω.naturality Ψ₀
  simp only [Functor.comp_map] at hω
  subst hi₀ hi₁
  rw [Category.assoc, Category.assoc, hc, reassoc_of% hr₁, Res.map_comp, Res.map_comp,
    Res.map_comp, hr₀]
  simp only [Category.assoc]
  rw [reassoc_of% hω, reassoc_of% htr, ← Rν₁.map_comp_assoc, ← Rν₁.map_comp_assoc,
    ← Rν₁.map_comp_assoc, Category.assoc, hΨ]

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})

/-- The naturality of `Rν_* ν^* S ≅ S` (`rightDerivedComparisonLowerStarSingleFunctorIso`) in the
sheaf `S`. -/
lemma rightDerivedComparisonLowerStarSingleFunctorIso_hom_naturality
    {S T : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : S ⟶ T) :
    (rightDerivedComparisonLowerStarSingleFunctorIso Λ X S).hom ≫
        (DerivedCategory.singleFunctor _ 0).map g =
      (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map
          ((DerivedCategory.singleFunctor _ 0).map (ν^*(X)[ModuleCat.{u + 1} Λ].map g)) ≫
        (rightDerivedComparisonLowerStarSingleFunctorIso Λ X T).hom := by
  sorry

/-- **`Rν_* ν^* S ≅ S` commutes with the restriction of scalars**: for a sheaf `S` of
`Λ'`-modules, the restriction of scalars of `Rν_* ν^* S ≅ S` is the base change map
`Res Rν_* ⟶ Rν_* Res` (`derivedRestrictScalarsCompComparisonLowerStarMap`), followed by the
commutations of `Res` with the inclusion in degree zero and with `ν^*`, and
`Rν_* ν^* Res S ≅ Res S`.
-/
lemma derivedRestrictScalars_map_rightDerivedComparisonLowerStarSingleFunctorIso_hom
    (S : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        (rightDerivedComparisonLowerStarSingleFunctorIso Λ' X S).hom =
      (derivedRestrictScalarsCompComparisonLowerStarMap φ X).app
          ((DerivedCategory.singleFunctor _ 0).obj (ν^*(X)[ModuleCat.{u + 1} Λ'].obj S)) ≫
        (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map
          (((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategorySingleFunctor
              0).hom.app (ν^*(X)[ModuleCat.{u + 1} Λ'].obj S) ≫
            (DerivedCategory.singleFunctor _ 0).map
              ((asIso (restrictScalarsCompComparisonUpperStar φ X)).inv.app S)) ≫
        (rightDerivedComparisonLowerStarSingleFunctorIso Λ X
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj S)).hom ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategorySingleFunctor
          0).inv.app S := by
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [NeZero (ℓ : k)] (E : Type) [Field E]
  [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ) (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The reduction modulo `ℓⁿ` of the integral Tate twist `𝒪_{E,X}(d)`, read as a pro-étale
complex, is `ν^*` of the Tate sheaf `Λ_X(1)^{⊗ d}` placed in degree zero: the first factor of
`etaleReductionIntegralTateTwistIso`. -/
noncomputable def finiteCoefficientDerivedEquivalenceIntegralTateTwistIso (d : ℕ) :
    (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor.obj
        ((boundedConstructible _).ι.obj ((boundedConstructibleIntegersModPowReduction X.left ℓ E
          n).obj (integralTateTwistBoundedConstructible ℓ E X.hom d))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
          (Etale.tateSheafPow (integersModPowCoeff.{u} ℓ E n) X.left d)) :=
  (finiteCoefficientDerivedEquivalence X.left (PadicAlgCl.integersModPow ℓ E n)).functor.mapIso
      ((boundedConstructibleIntegersModPowReductionCompatibility X.left ℓ E n).app
          (integralTateTwistBoundedConstructible ℓ E X.hom d) ≪≫
        Functor.leftDerivedFunctorSingleFunctorIsoOfFlat _
          (isLocallyFree_integralTateTwistNat ℓ E X.hom d).flat) ≪≫
    ((finiteCoefficientModEquivalence X.left _).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (finiteCoefficientModEquivalenceExtendScalarsIntegralTateTwistNatIso ℓ E n X.hom d)


variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E n) X.left]

/-- `etaleReductionIntegralTateTwistIso` through
`finiteCoefficientDerivedEquivalenceIntegralTateTwistIso`. -/
lemma etaleReductionIntegralTateTwistIso_hom_eq (d : ℕ) :
    (etaleReductionIntegralTateTwistIso ℓ E n X d).hom =
      (R(ν_*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])).map
          (finiteCoefficientDerivedEquivalenceIntegralTateTwistIso ℓ E n X d).hom ≫
        (rightDerivedComparisonLowerStarSingleFunctorIso _ _ _).hom ≫
        (Etale.tateObjectNatIsoSingleFunctor _ _ d).inv :=
  rfl

variable [NeZero (ringChar (integersModPowCoeff.{u} ℓ E (n + 1)))]
  [NeZero (ringChar (integersModPowCoeff.{u} ℓ E n))]
  [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E (n + 1)) X.left]

/-- Blueprint `det-sp-purity-coefficient-change`. **The condensed transition on the reduction of
`𝒪_{E,X}(1)` is the `ℓ`-th power map**: through the identifications of the reductions of the
integral Tate twist `𝒪_{E,X}(1)` with `ν^*` of the Tate sheaves placed in degree zero
(`finiteCoefficientDerivedEquivalenceIntegralTateTwistIso`), the transition
`red_{n+1} 𝒪_{E,X}(1) ⟶ Res(red_n 𝒪_{E,X}(1))` read on the pro-étale site (as in
`unit_app_comp_map_etaleReductionExtendScalarsIsoApp_hom`) is `ν^*` of the change of coefficients
of the Tate sheaves `Etale.tateSheafPowOneChangeMap` (the `ℓ`-th power map
`μ_{ℓⁿ⁺¹} ⟶ μ_{ℓⁿ}`), up to the commutations of `Res` with `ν^*` and with the inclusion in degree
zero. -/
lemma finiteCoefficientDerivedEquivalence_map_transition_integralTateTwistOne :
    ((finiteCoefficientDerivedEquivalence X.left
          (PadicAlgCl.integersModPow ℓ E (n + 1))).functor.map
          ((Mod.derivedExtendMapDerivedCategoryAdjunction
              (integersModPowTransition X.left ℓ E n)).unit.app
              ((boundedConstructible _).ι.obj
                ((boundedConstructibleIntegersModPowReduction X.left ℓ E (n + 1)).obj
                  (integralTateTwistBoundedConstructible ℓ E X.hom 1))) ≫
            (Mod.comap (integersModPowTransition X.left ℓ E n)).mapDerivedCategory.map
              ((boundedConstructibleIntegersModPowReductionTransitionIso ℓ E n X.left).hom.app
                (integralTateTwistBoundedConstructible ℓ E X.hom 1))) ≫
        (finiteCoefficientDerivedEquivalenceComapIso X.left
          (PadicAlgCl.integersModPowTransition ℓ E n)).hom.app ((boundedConstructible _).ι.obj
            ((boundedConstructibleIntegersModPowReduction X.left ℓ E n).obj
              (integralTateTwistBoundedConstructible ℓ E X.hom 1)))) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X.left)
          (integersModPowCoeffTransition ℓ E n)).map
        (finiteCoefficientDerivedEquivalenceIntegralTateTwistIso ℓ E n X 1).hom ≫
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X.left)
          (integersModPowCoeffTransition ℓ E n)).mapDerivedCategorySingleFunctor 0).hom.app
        (ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
          (Etale.tateSheafPow (integersModPowCoeff.{u} ℓ E n) X.left 1)) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((asIso (restrictScalarsCompComparisonUpperStar (integersModPowCoeffTransition ℓ E n)
          X.left)).inv.app (Etale.tateSheafPow (integersModPowCoeff.{u} ℓ E n) X.left 1)) =
    (finiteCoefficientDerivedEquivalenceIntegralTateTwistIso ℓ E (n + 1) X 1).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        (ν^*(X.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))].map
          (Etale.tateSheafPowOneChangeMap (integersModPowCoeffTransition ℓ E n) X.left ℓ
            (ringChar_integersModPowCoeff_succ ℓ E n))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
