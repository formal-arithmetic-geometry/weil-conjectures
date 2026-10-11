/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Derived direct image of a degreewise split sequence of K-injectives

Source: Stacks Project, Tags 0152 and 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle).
-/

universe u wX wY

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}
  [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
  [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]

/-- The identification computed by the identity resolution of a K-injective complex.
It is the inverse right-derived unit, with the quotient/localization identifications.
Source: Stacks, Tag 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle). -/
def derivedModuleDirectImageKInjectiveIso (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [K.IsKInjective] :
    (derivedModuleDirectImage g).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (derivedModuleDirectImage g).mapIso
      ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
    (asIso ((moduleDirectImage g).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K))).symm ≪≫
    DerivedCategory.Qh.mapIso
      (((moduleDirectImage g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- The identification of the localized image of a shifted complex with the shifted
localized image. Both complex shift comparison maps are degreewise identities.
Source: Stacks, Tags 0152 and 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle). -/
def moduleDirectImageLocalizedShiftIso (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) :
    DerivedCategory.Q.obj
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (K⟦(1 : ℤ)⟧)) ≅
      (DerivedCategory.Q.obj
        (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.mapIso
      ((((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso
        (1 : ℤ)).app K) ≪≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).app _

/-- The triangle with the connecting map transported by the identity-resolution comparisons.
Source: Stacks, Tags 0152 and 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle). -/
def derivedModuleDirectImageSplitTriangle (g : X ⟶ Y)
    (S : ShortComplex (CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ))
    (hS : S.ShortExact) [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective] :
    Triangle (DerivedCategory (SheafOfModules.{u} (moduleRings Y))) :=
  Triangle.mk
    ((derivedModuleDirectImage g).map (DerivedCategory.Q.map S.f))
    ((derivedModuleDirectImage g).map (DerivedCategory.Q.map S.g))
    ((derivedModuleDirectImage g).map (DerivedCategory.triangleOfSESδ hS) ≫
      (derivedModuleDirectImage g).map
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app S.X₁) ≫
      (derivedModuleDirectImageKInjectiveIso g (S.X₁⟦(1 : ℤ)⟧)).hom ≫
      (moduleDirectImageLocalizedShiftIso g S.X₁).hom ≫
      (shiftFunctor _ (1 : ℤ)).map (derivedModuleDirectImageKInjectiveIso g S.X₁).inv)

/-- Degreewise split sequences of K-injectives have their canonical triangle carried to
that of the direct-image sequence, including its connecting morphism.
Source: Stacks, Tags 0152 and 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle).

Proof:
1. Apply additive module direct image to the degreewise retraction and section identities.
This preserves split exactness. Additivity also preserves the negative differential in
shift by one. The boundary is the chain map pi d s, with the cone sign convention, by
lem-weil-pbc-degreewise-split-connecting-morphism and
lem-weil-pbc-degreewise-split-derived-triangle. Its direct image is g-star(pi d s).
2. Shifts of K-injectives are K-injective, since shifting preserves acyclicity and the
Hom groups from acyclic objects vanish. The inverse right-derived unit on K-injectives
is natural, by def-pc-ringed-spaces-derived-direct-image. Apply this to the first two
maps and to pi d s. After localization this gives all three comparison identities.
3. The image sequence has a distinguished triangle by lem-weil-pbc-complex-ses-triangle.
The three comparison isomorphisms form an isomorphism from the displayed transported
triangle to that triangle, including the third map by step 2. Closure under isomorphism
in def-weil-triangulated-category proves distinguishedness.

The node's clauses that I₁[1] is K-injective and that g-star(I₁[1]) = (g-star I₁)[1]
are not separate conjuncts: the first is Mathlib's shift instance for
`CochainComplex.IsKInjective` (used to form the comparison of `S.X₁⟦1⟧`), the second holds
by `rfl` for termwise direct image, and its canonical `commShiftIso` (identity components,
`Functor.mapHomologicalComplex_commShiftIso_hom_app_f`) is the identification used in
`moduleDirectImageLocalizedShiftIso`. -/
theorem derivedModuleDirectImage_termwise_split_ses_triangle (g : X ⟶ Y)
    (S : ShortComplex (CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ))
    (hS : S.ShortExact)
    (_hSplit : ∀ n : ℤ, Nonempty ((S.map
      (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings X))
        (ComplexShape.up ℤ) n)).Splitting))
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective] :
    ∃ hImage : (S.map
      ((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact,
      (∀ n : ℤ, Nonempty (((S.map
        ((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ))).map
        (HomologicalComplex.eval (SheafOfModules.{u} (moduleRings Y))
          (ComplexShape.up ℤ) n)).Splitting)) ∧
      ((derivedModuleDirectImage g).map (DerivedCategory.Q.map S.f) ≫
          (derivedModuleDirectImageKInjectiveIso g S.X₂).hom =
        (derivedModuleDirectImageKInjectiveIso g S.X₁).hom ≫
          DerivedCategory.Q.map
            (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map S.f)) ∧
      ((derivedModuleDirectImage g).map (DerivedCategory.Q.map S.g) ≫
          (derivedModuleDirectImageKInjectiveIso g S.X₃).hom =
        (derivedModuleDirectImageKInjectiveIso g S.X₂).hom ≫
          DerivedCategory.Q.map
            (((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ)).map S.g)) ∧
      ((derivedModuleDirectImage g).map (DerivedCategory.triangleOfSESδ hS) ≫
          (derivedModuleDirectImage g).map
            ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app S.X₁) ≫
          (derivedModuleDirectImageKInjectiveIso g (S.X₁⟦(1 : ℤ)⟧)).hom ≫
          (moduleDirectImageLocalizedShiftIso g S.X₁).hom =
        (derivedModuleDirectImageKInjectiveIso g S.X₃).hom ≫
          DerivedCategory.triangleOfSESδ hImage) ∧
      (∃ e : derivedModuleDirectImageSplitTriangle g S hS ≅
          DerivedCategory.triangleOfSES hImage,
        e.hom.hom₁ = (derivedModuleDirectImageKInjectiveIso g S.X₁).hom ∧
        e.hom.hom₂ = (derivedModuleDirectImageKInjectiveIso g S.X₂).hom ∧
        e.hom.hom₃ = (derivedModuleDirectImageKInjectiveIso g S.X₃).hom) ∧
      derivedModuleDirectImageSplitTriangle g S hS ∈
        distTriang (DerivedCategory (SheafOfModules.{u} (moduleRings Y))) := by
  sorry

end AlgebraicGeometry.RingedSpace
