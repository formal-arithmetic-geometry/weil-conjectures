/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenImageDeltaDefs

/-! The negative-degree and degree-zero part of the condensed open-image argument.

Source: latest blueprint, p-dl-a1-exact, Step 2
(blueprint: new-dl-a1-basic).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- For a constant constructible coefficient object, the derived open pushforward has
no negative homology and its canonical degree-zero unit is normalized by the single
complex comparison. -/
theorem condensedOpenImage_basic
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_iota : PadicAlgCl ell →+* ℂ)
    (U₀ C₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType C₀.hom] [QuasiCompact C₀.hom] [IsSeparated C₀.hom]
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left] :
    ∀ M : ConstantModelConstructible (Profinite.padicAlgClRingObj ell)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj U₀).left,
      (∀ r : ℤ, r < 0 → IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ell)
          (dlGeometricOpen D j₀)).obj
          ((DerivedCategory.singleFunctor _ 0).obj M.obj)))) ∧
      ((DerivedCategory.homologyFunctor _ 0).map
          ((lowerStar (Profinite.padicAlgClRingObj ell)
            (dlGeometricOpen D j₀)).singleRightDerivedUnit.app M.obj) ≫
        ((lowerStar (Profinite.padicAlgClRingObj ell)
          (dlGeometricOpen D j₀)).singleRightDerivedH0Iso M.obj).hom =
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
          ((lowerStar (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀)).obj M.obj)) := by
  intro M
  constructor
  · intro r hr
    change IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((lowerStar (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀)).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M.obj)))
    have hge := (lowerStar (Profinite.padicAlgClRingObj ell)
      (dlGeometricOpen D j₀)).isGE_rightDerivedFunctor_obj_singleFunctor M.obj
    exact DerivedCategory.isZero_of_isGE _ 0 r hr
  · simpa only [Functor.singleH0Comparison_def] using
      (Functor.singleRightDerivedUnit_homology_zero
        (lowerStar (Profinite.padicAlgClRingObj ell) (dlGeometricOpen D j₀)) M.obj)

end AlgebraicGeometry.ProEtale.CondensedRing
