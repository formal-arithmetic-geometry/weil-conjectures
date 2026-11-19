/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedAdicComplete
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeResidueExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CountableProducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Proper base change for derived complete integral complexes

Let `t : P ⟶ Q` be proper and `g : Q' ⟶ Q` a morphism along which the derived pullbacks
`Lg^*` and `Lg'^*` preserve countable products (for instance closed immersions,
`ProEtale.CondensedRing.preservesLimitsOfShape_leftDerivedUpperStar_of_isCompl`). For a bounded
below complex `R` of `𝒪_{E,P}`-modules which is derived `ℓ`-adically complete
(`CategoryTheory.IsDerivedAdicComplete`) and whose first derived reduction `R ⊗ᴸ 𝔽_E` is of
étale origin, the base change morphism `Lg^* Rt_* R ⟶ Rt'_* Lg'^* R` is an isomorphism
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_of_isDerivedAdicComplete`).

This is blueprint `proposition-proper-base-change-complete-integral` in the case where the completed
inverse images agree with the inverse images. The proof: both sides of the base change morphism are
derived complete (`Rt_*` is a right adjoint, and `Lg^*`, `Lg'^*` preserve the products), hence so is
its cone `C`. The first derived reduction of the base change morphism is the pro-étale base change
morphism with coefficients `𝔽_E` at `R ⊗ᴸ 𝔽_E`
(`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_map_exchangeRight`), invertible by
proper base change for torsion coefficients
(`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`). So `C ⊗ᴸ 𝔽_E = 0`, `ℓ` acts invertibly on
`C` (`ProEtale.isIso_zsmul_id_of_isZero_derivedReduction`) and `C = 0` by derived Nakayama
(`CategoryTheory.IsDerivedAdicComplete.isZero_of_isIso_zsmul_id`).

The same argument only uses that `Lg^* Rt_* R` and `Lg'^* R` are derived complete; this is
`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_of_isDerivedAdicComplete_upperStar`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- A morphism between derived `ℓ`-adically complete `𝒪_E`-complexes is an isomorphism if its
first derived reduction is. -/
theorem isIso_of_isIso_derivedReduction_map_of_isDerivedAdicComplete (Z : Scheme.{u})
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))} (φ : K ⟶ L)
    (hK : IsDerivedAdicComplete (ℓ : ℤ) K) (hL : IsDerivedAdicComplete (ℓ : ℤ) L)
    (h : IsIso ((derivedReduction Z ℓ E).map φ)) : IsIso φ := by
  obtain ⟨C, a, b, hT⟩ := distinguished_cocone_triangle φ
  have hC : IsDerivedAdicComplete (ℓ : ℤ) C := IsDerivedAdicComplete.of_distTriang₁₂ _ hT hK hL
  have h' := isIso_leftDerivedFunctor_map_of_isIso_derivedReduction_map Z ℓ E _ h
  have h₀ : IsZero ((Mod.extendScalars (padicIntegersToResidueField Z ℓ E)).leftDerivedFunctor.obj
      C) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((Mod.extendScalars (padicIntegersToResidueField Z ℓ E)).leftDerivedFunctor.map_distinguished
        _ hT)).2 h'
  have hC₁ : IsZero ((derivedReduction Z ℓ E).obj C) :=
    Functor.map_isZero (residueFieldModuleSheaf Z ℓ E).mapDerivedCategory h₀
  have hCz : IsZero C :=
    hC.isZero_of_isIso_zsmul_id (isIso_zsmul_id_of_isZero_derivedReduction Z ℓ E C hC₁)
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hCz

/-- For a cartesian square `g' ≫ p = p' ≫ g` with `p` proper and a bounded below `𝒪_E`-complex
`R` whose first derived reduction is of étale origin, the first derived reduction of the base
change morphism `Lg^* Rp_* R ⟶ Rp'_* Lg'^* R` is an isomorphism. -/
theorem isIso_derivedReduction_map_baseChangeMap_app_of_isProper [IsProper p]
    (hsq : IsPullback g' p' p g)
    (R : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [R.IsGE n]
    (hR₁ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X
      ((derivedReduction X ℓ E).obj R)) :
    IsIso ((derivedReduction Y' ℓ E).map
      ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) hsq.toCommSq).app R)) := by
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1)))
  unfold baseChangeMap
  have e := (nonempty_arrowIso_derivedReduction_map_exchangeRight ℓ E hsq.toCommSq R n).some
  have h₃ : IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E))
      hsq.toCommSq).app ((derivedReduction X ℓ E).obj R)) :=
    isIso_derivedBaseChangeMap_app_of_isProper _ hsq _ hR₁
  have key := isIso_of_nonempty_arrowIso_map (𝟭 _) h₃ ⟨e.symm⟩
  exact_mod_proofs key

/-- **Completed and ordinary base change, isomorphism criterion.** For a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper and a bounded below `𝒪_E`-complex `R` whose first derived
reduction is of étale origin, if `Lg^* Rp_* R` and `Lg'^* R` are derived `ℓ`-adically complete,
then the base change morphism `Lg^* Rp_* R ⟶ Rp'_* Lg'^* R` is an isomorphism. -/
theorem isIso_baseChangeMap_app_of_isProper_of_isDerivedAdicComplete_upperStar [IsProper p]
    (hsq : IsPullback g' p' p g)
    (R : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [R.IsGE n]
    (hR₁ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X
      ((derivedReduction X ℓ E).obj R))
    (h₁ : IsDerivedAdicComplete (ℓ : ℤ)
      (L((g)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj
        (R((p)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj R)))
    (h₂ : IsDerivedAdicComplete (ℓ : ℤ)
      (L((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj R)) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) hsq.toCommSq).app R) := by
  have h₂' : IsDerivedAdicComplete (ℓ : ℤ)
      (R((p')_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj
        (L((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj R)) := by
    have := (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
      p').rightAdjoint_preservesLimits.{0, 0}
    exact h₂.map' _
  exact isIso_of_isIso_derivedReduction_map_of_isDerivedAdicComplete ℓ E Y' _ h₁ h₂'
    (isIso_derivedReduction_map_baseChangeMap_app_of_isProper ℓ E hsq R n hR₁)

/-- **Proper base change for derived complete integral complexes.** For a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper, along which `Lg^*` and `Lg'^*` preserve countable products,
and a bounded below derived `ℓ`-adically complete `𝒪_E`-complex `R` whose first derived
reduction is of étale origin, the base change morphism `Lg^* Rp_* R ⟶ Rp'_* Lg'^* R` is an
isomorphism. -/
theorem isIso_baseChangeMap_app_of_isProper_of_isDerivedAdicComplete [IsProper p]
    (hsq : IsPullback g' p' p g)
    [PreservesLimitsOfShape (Discrete ℕ) L((g)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)]
    [PreservesLimitsOfShape (Discrete ℕ) L((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)]
    (R : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) [R.IsGE n]
    (hR : IsDerivedAdicComplete (ℓ : ℤ) R)
    (hR₁ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) X
      ((derivedReduction X ℓ E).obj R)) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1) hsq.toCommSq).app R) := by
  have := (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
    p).rightAdjoint_preservesLimits.{0, 0}
  exact isIso_baseChangeMap_app_of_isProper_of_isDerivedAdicComplete_upperStar ℓ E hsq R n hR₁
    ((hR.map' _).map' _) (hR.map' _)

end AlgebraicGeometry.ProEtale.CondensedRing
