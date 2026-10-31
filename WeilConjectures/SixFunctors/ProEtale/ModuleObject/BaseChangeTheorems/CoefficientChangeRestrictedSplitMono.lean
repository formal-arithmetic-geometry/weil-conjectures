/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted

/-!
# Split restricted base change maps under coefficient change

For a commutative square `sq : g' ≫ p' = p ≫ g` and `i : Z ⟶ Y'`, consider the restricted base
change map `Li^* BC_sq(K) : Li^* Lg^* Rp_* K ⟶ Li^* Rp'_* Lg'^* K`. This file shows that its split
injectivity is compatible with the coefficient changes `𝒪_E/ℓⁿ ⟵ 𝒪_E ⟶ E ⟶ ℚ̄_ℓ`, as
`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_integral` does for its
invertibility:

* `ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_padicSubfield_of_padicIntegers` and
  `ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_padicAlgCl_of_padicSubfield`: flat
  extension of scalars along `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` carries split monomorphisms to split monomorphisms
  through the arrow isomorphisms
  `ProEtale.CondensedRing.nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat`;
  `ProEtale.CondensedRing.isSplitMono_map_baseChangeMap_app_of_iso_extendScalars` transports along
  an integral model.

The case of `𝒪_E/ℓⁿ⁺¹`-coefficients is in `CoefficientChangeRestrictedSplitMonoTorsion.lean`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

section Flat

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Flat extension of scalars and split restricted base change maps**: if the restricted base
change map with coefficients `Λ` is a split monomorphism at `K` and the comparisons
`derivedPushHom a` are invertible at `K` and `Lg'^* K`, the one with coefficients `Λ'` is a split
monomorphism at `T K`. -/
theorem isSplitMono_map_baseChangeMap_app_derivedExtendScalars
    (H : DerivedPullIsoCompCoherence a) (sq : CommSq g' p' p g) (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedPushHom a p).app K))
    (h₂ : IsIso ((derivedPushHom a p').app ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K)))
    (hK : IsSplitMono ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ p)
          (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)).app K))) :
    IsSplitMono ((L((i)^*⟦Λ'⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction Λ' p)
          (derivedUpperStarLowerStarAdjunction Λ' p') (pullbackSquareComparison Λ' sq)).app
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K))) :=
  Arrow.isSplitMono_of_iso
    (nonempty_arrowIso_map_leftDerivedUpperStar_map_baseChangeMap_app_of_flat a H sq i K h₁
      h₂).some.symm

end Flat

section Transport

variable {Λ₁ Λ₂ Λ₃ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₁]
  [IsCommMonObj Λ₁] [MonObj Λ₂] [IsCommMonObj Λ₂] [MonObj Λ₃] [IsCommMonObj Λ₃]
  (a : Λ₁ ⟶ Λ₂) [IsMonHom a] (b : Λ₂ ⟶ Λ₃) [IsMonHom b]
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The restricted base change map with coefficients `Λ₃` is a split monomorphism at `K` as soon
as it is one at `T_b (T_a K₀)` for some `K₀` with `T_b (T_a K₀) ≅ K`. -/
lemma isSplitMono_map_baseChangeMap_app_of_iso_extendScalars (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₁ X)))
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₃ X))}
    (e : Nonempty ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K₀) ≅ K))
    (h : IsSplitMono ((L((i)^*⟦Λ₃⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ₃ p) (derivedUpperStarLowerStarAdjunction Λ₃ p')
      (pullbackSquareComparison Λ₃ sq)).app
        ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj
          ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K₀))))) :
    IsSplitMono ((L((i)^*⟦Λ₃⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ₃ p) (derivedUpperStarLowerStarAdjunction Λ₃ p')
      (pullbackSquareComparison Λ₃ sq)).app K)) :=
  Arrow.isSplitMono_of_iso (Arrow.isoMapApp _ _ e.some).symm

end Transport

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' Z : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **From `𝒪_E` to `E` for split restricted base change maps**, for quasi-compact
quasi-separated vertical maps and a bounded below `K₀`. -/
theorem isSplitMono_map_baseChangeMap_app_padicSubfield_of_padicIntegers [QuasiCompact p]
    [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p'] (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K₀ : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))) (n : ℤ) (hn : K₀.IsGE n)
    (h : IsSplitMono ((L((i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map
      ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p)
        (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) p')
        (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) sq)).app K₀))) :
    IsSplitMono ((L((i)^*⟦Profinite.continuousMapRingObj E.1⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p')
      (pullbackSquareComparison (Profinite.continuousMapRingObj E.1) sq)).app
        ((Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E)
          X)).leftDerivedFunctor.obj K₀))) := by
  have := isGE_leftDerivedUpperStar_obj (Profinite.padicIntegersRingObj ℓ E.1) g' K₀ n
  have hE := isSplitMono_map_baseChangeMap_app_derivedExtendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) (derivedPullIsoCompCoherence _) sq i K₀
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p K₀ n)
    (isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p'
      ((g')^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧.leftDerivedFunctor.obj K₀) n)
    (by exact_mod_proofs h)
  exact_mod_proofs hE

/-- **From `E` to `ℚ̄_ℓ` for split restricted base change maps**, for quasi-compact
quasi-separated vertical maps and a bounded below `K`. -/
theorem isSplitMono_map_baseChangeMap_app_padicAlgCl_of_padicSubfield [QuasiCompact p]
    [QuasiSeparated p] [QuasiCompact p'] [QuasiSeparated p'] (sq : CommSq g' p' p g)
    (i : Z ⟶ Y')
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X))) (n : ℤ) (hn : K.IsGE n)
    (h : IsSplitMono ((L((i)^*⟦Profinite.continuousMapRingObj E.1⟧)).map
      ((Adjunction.exchangeRight
        (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p)
        (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) p')
        (pullbackSquareComparison (Profinite.continuousMapRingObj E.1) sq)).app K))) :
    IsSplitMono ((L((i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p)
      (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p')
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq)).app
      ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        X)).leftDerivedFunctor.obj K))) := by
  have := isGE_leftDerivedUpperStar_obj (Profinite.continuousMapRingObj E.1) g' K n
  have hA := isSplitMono_map_baseChangeMap_app_derivedExtendScalars
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) (derivedPullIsoCompCoherence _) sq i K
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p K n)
    (isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p'
      ((g')^*⟦Profinite.continuousMapRingObj E.1⟧.leftDerivedFunctor.obj K) n)
    (by exact_mod_proofs h)
  exact_mod_proofs hA

end Coefficients

end AlgebraicGeometry.ProEtale.CondensedRing
