/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalBaseChange

/-!
# Base change of the canonical orientation

For a cartesian square `g' ≫ f = f' ≫ g` with `f`, `f'` smooth separated of relative dimension
`d` over bases separated and locally of finite type over fields, the canonical orientations
`θ_f : ω_f ≅ Λ_X(d)[2d]` and `θ_{f'}` (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`)
are compatible with the exceptional base change `Lg'^* ω_f ≅ ω_{f'}` and the pullback of the
twist-and-shift (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange`).

Every step of the diagonal construction of `θ_f` commutes with base change: the smooth base change
identification `𝒞(p₁, Δ) ≅ ω_f` and the composition isomorphism `RΔ^! ω_{p₁} ≅ Λ_X`
(`WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalBaseChange`), the purity of the diagonal
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTateObjectIsoOfSection_baseChange`, from the base
change of the fundamental class) and the section invariant construction
(`AlgebraicGeometry.Etale.sectionInvariantTwistShiftIsoOfSection_baseChange`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme IsoSquare

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (d : ℕ) [SmoothOfRelativeDimension d f]
  [SmoothOfRelativeDimension d f'] [IsSeparated f] [IsSeparated f'] [HasCompactification f]
  [HasCompactification f'] [QuasiCompact f'] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ X'] {k k' : Type u} [Field k] [Field k']

/-- The canonical orientations `θ_f : Rf^! Λ_Y ≅ Λ_X(d)[2d]` and `θ_{f'}`
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`) are compatible with the exceptional base
change `Lg'^* Rf^! ⟶ Rf'^! Lg^*` and the pullback of the Tate twist. -/
theorem dualizingComplexTwistShiftIso_baseChange (sq : IsPullback g' f' f g)
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    (aY' : Y' ⟶ Spec (.of k')) [IsSeparated aY'] [LocallyOfFiniteType aY'] :
    (upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom ≫
          (dualizingComplexTwistShiftIso Λ f' d aY').hom =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (leftDerivedUpperStarTwistShiftIso Λ g' d (constantComplex Λ X)).hom ≫
          (twistShift Λ X' d).map (leftDerivedUpperStarUnitIso _ g').hom := by
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated aY
  have : QuasiSeparatedSpace Y' := quasiSeparatedSpace_of_quasiSeparated aY'
  have : QuasiCompact f := HasCompactification.quasiCompact_of_locallyOfFiniteType f aY
  have : HasInvertibleExponent Λ (pullback f f) := .of_hom (pullback.fst f f)
  have : HasInvertibleExponent Λ (pullback f' f') := .of_hom (pullback.fst f' f')
  have := SmoothOfRelativeDimension.smooth d f
  have := SmoothOfRelativeDimension.smooth d f'
  have hS := sectionInvariantTwistShiftIsoOfSection_baseChange Λ d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) (pullback.fst f' f') (pullback.diagonal f')
    (pullback.diagonal_fst f') (IsoSquare.map sq) (isPullback_diagonal_map sq) (f ≫ aY)
    (f' ≫ aY')
    (dualizingComplexPullbackFstBaseChangeIso Λ sq d (dualizingComplexBaseChangeIso Λ sq d))
    (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_diagonal_baseChange Λ sq d)
  have hC := sectionInvariantDiagonalIso_baseChange Λ sq d (dualizingComplexBaseChangeIso Λ sq d)
  have hC' : (L((g')^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantDiagonalIso Λ f d).inv ≫
      derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ)
          (isPullback_diagonal_map sq).toCommSq _ ≫
        (L((pullback.diagonal f')^*[ModuleCat.{u + 1} Λ])).map
          (dualizingComplexPullbackFstBaseChangeIso Λ sq d
            (dualizingComplexBaseChangeIso Λ sq d)).hom =
      (dualizingComplexBaseChangeIso Λ sq d).hom ≫ (sectionInvariantDiagonalIso Λ f' d).inv := by
    rw [← cancel_epi ((L((g')^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantDiagonalIso Λ f d).hom),
      ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      reassoc_of% hC, Iso.hom_inv_id, Category.comp_id]
  have h : (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTwistShiftIso Λ f d aY).hom ≫
        (twistShiftConstantComplexBaseChangeIso Λ g' d).hom =
      (dualizingComplexBaseChangeIso Λ sq d).hom ≫
        (dualizingComplexTwistShiftIso Λ f' d aY').hom := by
    simp only [dualizingComplexTwistShiftIso, Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
      Category.assoc]
    rw [hS, reassoc_of% hC']
  rw [twistShiftConstantComplexBaseChangeIso_hom] at h
  simp only [dualizingComplexBaseChangeIso, asIso_hom, Category.assoc] at h
  exact h.symm

end AlgebraicGeometry.Etale
