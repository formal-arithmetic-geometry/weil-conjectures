/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionCanonical
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekReflectInvertible

/-!
# The canonical comparison `Ψ ω_f ⟶ ω'_f` is an isomorphism

Let `f : X ⟶ Y` be smooth separated of relative dimension `d` over a quasi-compact `Y`, separated
and locally of finite type over a field, `Ψ` the reduction of coefficients along `ρ : Λ →+* Λ'`,
and assume that `Ψ` commutes with `Rf_!` and `Rp₁_!` for the first projection
`p₁ : X ×_Y X ⟶ X`. If `Ψ` carries the frame classes of the diagonal `Δ` over `Λ` to those over
`Λ'`, then the canonical comparison `c_f : Ψ Rf^! ⟶ Rf^! Ψ` is an isomorphism at `Λ_Y`
(`AlgebraicGeometry.Etale.isIso_derivedExtendScalarsRightDerivedUpperShriekMap_app`): hence the
canonical comparison `Ψ ω_f ≅ ω'_f` of the dualizing complexes is an isomorphism, and the
canonical orientation is compatible with `Ψ` through it
(`AlgebraicGeometry.Etale.map_dualizingComplexTwistShiftIso_reduction_canonical`).

The proof runs through the diagonal. By the compatibility of the comparisons with the composition
isomorphisms of a section (`hε`), `c_Δ(ω_{p₁}) ≫ RΔ^!(φ₁)` is an isomorphism, where `φ₁` is the
comparison `Ψ ω_{p₁} ⟶ ω'_{p₁}`. The comparison `c_Δ` is an isomorphism at `Λ(d)[2d]` by the
compatibility of the frame classes, hence at `ω_{p₁} ≅ Lp₂^* ω_f ≅ Λ(d)[2d]`. So `RΔ^! φ₁` is an
isomorphism, hence so is `LΔ^* φ₁` (`RΔ^!` reflects isomorphisms between invertible objects,
`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map_of_isInvertible`),
and `LΔ^* φ₁ ≅ LΔ^* Lp₂^* φ ≅ φ` by smooth base change, `φ` the comparison of `f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the definitions of
-- the tensor maps of `R^!` (see
-- `WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation`).
attribute [local instance high] SymmetricCategory.toBraidedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})
  [Finite Λ] [Finite Λ'] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ' X] [HasCompactification f] [QuasiSeparatedSpace Y] [QuasiCompact f]
  [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasKummerClass Λ']
  [HasKummerClass.IsNormalized Λ'] (τ : DerivedExtendScalarsTateShiftData Λ Λ' hρ ha)

/-- **The canonical comparison `c_f : Ψ Rf^! ⟶ Rf^! Ψ` is an isomorphism at `Λ_Y`** for a smooth
separated `f` along which `Ψ` commutes with `R_!`, as soon as `Ψ` carries the frame classes of
the diagonal over `Λ` to those over `Λ'`. -/
theorem isIso_derivedExtendScalarsRightDerivedUpperShriekMap_app (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated f] {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ (pullback f f)] [HasInvertibleExponent Λ' (pullback f f)]
    [CompactSpace Y] [CompactSpace X] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha (pullback.fst f f))]
    (hframe : ∀ F : (pullback.diagonal f).EtaleFrame d, IsOpenImmersion F.e →
      (reductionSupportedCoefficientChange hρ ha τ).mapSupportedClass _
        ((reductionSupportedCoefficientChange hρ ha τ).tateShiftIso F.U d) (frameClass Λ F) =
          frameClass Λ' F) :
    IsIso ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha f).app (constantComplex Λ Y)) := by
  have := SmoothOfRelativeDimension.smooth d f
  have : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
  -- `c_Δ` is an isomorphism at `Λ(d)[2d]`, hence at `ω_{p₁} ≅ Λ(d)[2d]`
  have hcT : IsIso ((derivedExtendScalarsUpperShriekMap hρ ha (pullback.diagonal f)).app
      ((tateObject Λ (pullback f f) d)⟦2 * (d : ℤ)⟧)) :=
    (reductionSupportedCoefficientChange hρ ha τ).isIso_upperShriekMap_app_of_hasThomFrames
      (hasThomFrames_of_section Λ d (pullback.fst f f) (pullback.diagonal f)
        (pullback.diagonal_fst f) (f ≫ aY))
      (hasThomFrames_of_section Λ' d (pullback.fst f f) (pullback.diagonal f)
        (pullback.diagonal_fst f) (f ≫ aY))
      (hasRegularZariskiFrames_of_section d (pullback.fst f f) (pullback.diagonal f)
        (pullback.diagonal_fst f)) (pullback.fst f f ≫ f ≫ aY) hframe
  let ι : dualizingComplex Λ (pullback.fst f f) ≅ (tateObject Λ (pullback f f) d)⟦2 * (d : ℤ)⟧ :=
    dualizingComplexPullbackFstIso Λ f d ≪≫
      (L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ])).mapIso
        (dualizingComplexTwistShiftIso Λ f d aY ≪≫ Etale.twistShiftConstantComplexIso Λ X d) ≪≫
      leftDerivedUpperStarTateShiftIso Λ (pullback.snd f f) d
  have hcω : IsIso ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha
      (pullback.diagonal f)).app (dualizingComplex Λ (pullback.fst f f))) := by
    have hn := (derivedExtendScalarsUpperShriekMap hρ ha (pullback.diagonal f)).naturality ι.hom
    simp only [Functor.comp_obj, Functor.comp_map] at hn
    have : IsIso ((derivedExtendScalarsUpperShriekMap hρ ha (pullback.diagonal f)).app
        (dualizingComplex Λ (pullback.fst f f)) ≫ (R(pullback.diagonal f)^![Λ']).map
          ((derivedExtendScalars hρ ha (pullback f f)).map ι.hom)) := by
      rw [← hn]
      infer_instance
    rw [derivedExtendScalarsRightDerivedUpperShriekMap_eq_derivedExtendScalarsUpperShriekMap]
    exact IsIso.of_isIso_comp_right _
      ((R(pullback.diagonal f)^![Λ']).map ((derivedExtendScalars hρ ha (pullback f f)).map ι.hom))
  -- hence `RΔ^! φ₁` is an isomorphism, `φ₁ : Ψ ω_{p₁} ⟶ ω'_{p₁}` the comparison of `p₁`
  have hε := map_rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_hom_comp hρ ha
    (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)
    (derivedExtendScalarsConstantComplexIso hρ ha X)
  rw [← derivedExtendScalarsDualizingComplexMap_eq] at hε
  have hRφ₁ : IsIso ((R(pullback.diagonal f)^![Λ']).map (derivedExtendScalarsDualizingComplexMap
      hρ ha (pullback.fst f f) (derivedExtendScalarsConstantComplexIso hρ ha X))) := by
    have h₀ : IsIso ((derivedExtendScalars hρ ha X).map
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f f)
          (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫
            (derivedExtendScalarsConstantComplexIso hρ ha X).hom) := inferInstance
    rw [hε] at h₀
    have h₁ : IsIso ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha
        (pullback.diagonal f)).app (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f)^![Λ']).map (derivedExtendScalarsDualizingComplexMap hρ ha
            (pullback.fst f f) (derivedExtendScalarsConstantComplexIso hρ ha X))) :=
      IsIso.of_isIso_comp_right _
      (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ' (pullback.fst f f)
        (pullback.diagonal f) (pullback.diagonal_fst f)).hom
    exact IsIso.of_isIso_comp_left
      ((derivedExtendScalarsRightDerivedUpperShriekMap hρ ha (pullback.diagonal f)).app
        (dualizingComplex Λ (pullback.fst f f))) _
  -- hence `LΔ^* φ₁` is an isomorphism
  have hT' : DerivedCategory.isInvertible Λ' (pullback f f)
      ((tateObject Λ' (pullback f f) d)⟦2 * (d : ℤ)⟧) :=
    (isInvertible_tateObject Λ' (pullback f f) d).shift _
  have hRT' : DerivedCategory.isInvertible Λ' X
      ((R(pullback.diagonal f)^![Λ']).obj ((tateObject Λ' (pullback f f) d)⟦2 * (d : ℤ)⟧)) :=
    DerivedCategory.isInvertible.of_iso
      (rightDerivedUpperShriekTateObjectIsoOfSection Λ' d (pullback.fst f f)
        (pullback.diagonal f) (pullback.diagonal_fst f) (f ≫ aY)).symm
      (DerivedCategory.isInvertible_unit Λ' X)
  have hP : DerivedCategory.isInvertible Λ' (pullback f f)
      ((derivedExtendScalars hρ ha (pullback f f)).obj (dualizingComplex Λ (pullback.fst f f))) :=
    DerivedCategory.isInvertible.of_iso
      ((derivedExtendScalars hρ ha (pullback f f)).mapIso ι ≪≫ τ.iso (pullback f f) d).symm hT'
  have hQ : DerivedCategory.isInvertible Λ' (pullback f f)
      (dualizingComplex Λ' (pullback.fst f f)) :=
    isInvertible_dualizingComplex Λ' (d := d) (pullback.fst f f)
  have hLφ₁ := isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map_of_isInvertible
    (rightDerivedUpperShriekAdjunction Λ' (pullback.diagonal f))
    ((isInvertible_iff_exists_derivedTensor _).2 hT')
    ((isInvertible_iff_exists_derivedTensor _).2 hRT')
    ((isInvertible_iff_exists_derivedTensor _).2 hP)
    ((isInvertible_iff_exists_derivedTensor _).2 hQ) _ hRφ₁
  -- `φ₁` is `Lp₂^* φ` up to isomorphisms, `φ` the comparison of `f`, and `LΔ^* Lp₂^* ≅ 𝟭`
  have hb := map_dualizingComplexBaseChangeMap_comp hρ ha (IsPullback.of_hasPullback f f).flip
    (derivedExtendScalarsConstantComplexIso hρ ha Y)
    (derivedExtendScalarsConstantComplexIso hρ ha X)
    (derivedExtendScalarsConstantComplexIso_hom_pullback_unit hρ ha f)
  rw [← derivedExtendScalarsDualizingComplexMap_eq, ← derivedExtendScalarsDualizingComplexMap_eq]
    at hb
  have hBC : IsIso (dualizingComplexBaseChangeMap Λ (IsPullback.of_hasPullback f f).flip) := by
    rw [← dualizingComplexPullbackFstIso_inv_eq f Λ d]
    infer_instance
  have hBC' : IsIso (dualizingComplexBaseChangeMap Λ' (IsPullback.of_hasPullback f f).flip) := by
    rw [← dualizingComplexPullbackFstIso_inv_eq f Λ' d]
    infer_instance
  have hLp : IsIso ((L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ'])).map
      ((L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ'])).map
        (derivedExtendScalarsDualizingComplexMap hρ ha f
          (derivedExtendScalarsConstantComplexIso hρ ha Y)))) := by
    have e : (L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ'])).map
        (derivedExtendScalarsDualizingComplexMap hρ ha f
          (derivedExtendScalarsConstantComplexIso hρ ha Y)) =
        inv ((derivedExtendScalarsPullbackMap hρ ha (pullback.snd f f)).app
          (dualizingComplex Λ f)) ≫
          (derivedExtendScalars hρ ha (pullback f f)).map
            (dualizingComplexBaseChangeMap Λ (IsPullback.of_hasPullback f f).flip) ≫
          derivedExtendScalarsDualizingComplexMap hρ ha (pullback.fst f f)
            (derivedExtendScalarsConstantComplexIso hρ ha X) ≫
          inv (dualizingComplexBaseChangeMap Λ' (IsPullback.of_hasPullback f f).flip) := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.eq_comp_inv, Category.assoc]
      exact hb.symm
    rw [e]
    simp only [Functor.map_comp]
    infer_instance
  have hφ : IsIso (derivedExtendScalarsDualizingComplexMap hρ ha f
      (derivedExtendScalarsConstantComplexIso hρ ha Y)) := by
    have hn := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ') (pullback.diagonal f)
      (pullback.snd f f) (pullback.diagonal_snd f)).hom.naturality
        (derivedExtendScalarsDualizingComplexMap hρ ha f
          (derivedExtendScalarsConstantComplexIso hρ ha Y))
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hn
    have : IsIso ((L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ'])).map
        ((L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ'])).map
          (derivedExtendScalarsDualizingComplexMap hρ ha f
            (derivedExtendScalarsConstantComplexIso hρ ha Y))) ≫
          (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ') (pullback.diagonal f)
            (pullback.snd f f) (pullback.diagonal_snd f)).hom.app _) := inferInstance
    rw [hn] at this
    exact IsIso.of_isIso_comp_left
      ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ') (pullback.diagonal f)
        (pullback.snd f f) (pullback.diagonal_snd f)).hom.app _) _
  rw [derivedExtendScalarsDualizingComplexMap_eq] at hφ
  exact IsIso.of_isIso_comp_right _
    ((R(f)^![Λ']).map (derivedExtendScalarsConstantComplexIso hρ ha Y).hom)

/-- Blueprint `thm-pur-diagonal-dualizing-object`, `det-sp-purity-coefficient-change`

**The canonical orientation `ω_f ≅ Λ_X(d)[2d]` is compatible with the reduction of coefficients
through the canonical comparison `Ψ ω_f ⟶ ω'_f`.** Let `f : X ⟶ Y` be smooth separated of
relative dimension `d` over a quasi-compact `Y`, separated and locally of finite type over a
field, such that `Ψ` commutes with `Rf_!` and with `Rp₁_!` for the first projection
`p₁ : X ×_Y X ⟶ X`. If `Ψ` carries the frame classes of the diagonal over `Λ` to those over `Λ'`
(`hframe`) and preserves the section invariant construction at the diagonal (`hL`), then the
canonical comparison `vω = c_f ≫ Rf^!(Ψ Λ_Y ≅ Λ'_Y)`
(`AlgebraicGeometry.Etale.derivedExtendScalarsDualizingComplexMap`, an isomorphism by
`AlgebraicGeometry.Etale.isIso_derivedExtendScalarsRightDerivedUpperShriekMap_app`) satisfies
`vω ≫ θ'_f = Ψ θ_f ≫ (Ψ(Λ_X(d)[2d]) ≅ Λ'_X(d)[2d])`. -/
theorem map_dualizingComplexTwistShiftIso_reduction_canonical (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated f] {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ (pullback f f)] [HasInvertibleExponent Λ' (pullback f f)]
    [CompactSpace Y] [CompactSpace X] [IsIso (derivedExtendScalarsLowerShriekMap hρ ha f)]
    [IsIso (derivedExtendScalarsLowerShriekMap hρ ha (pullback.fst f f))]
    (hframe : ∀ F : (pullback.diagonal f).EtaleFrame d, IsOpenImmersion F.e →
      (reductionSupportedCoefficientChange hρ ha τ).mapSupportedClass _
        ((reductionSupportedCoefficientChange hρ ha τ).tateShiftIso F.U d) (frameClass Λ F) =
          frameClass Λ' F)
    (hL : (reductionSupportedCoefficientChange hρ ha τ).PreservesSectionInvariantIso
      (pullback.diagonal f)) :
    (derivedExtendScalars hρ ha X).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        ((reductionSupportedCoefficientChange hρ ha τ).twistShiftConstantComplexIso X d).hom =
      derivedExtendScalarsDualizingComplexMap hρ ha f
          (derivedExtendScalarsConstantComplexIso hρ ha Y) ≫
        (dualizingComplexTwistShiftIso Λ' f d aY).hom := by
  have := isIso_derivedExtendScalarsRightDerivedUpperShriekMap_app hρ ha f τ d aY hframe
  exact map_dualizingComplexTwistShiftIso_reduction_canonical_of_isIso hρ ha f τ d aY hframe hL

end Etale

end AlgebraicGeometry
