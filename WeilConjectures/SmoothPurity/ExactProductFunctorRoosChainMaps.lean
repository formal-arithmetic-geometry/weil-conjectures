/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Strict chain-level Roos comparison for an exact product-preserving functor

Source: Stacks Project, Tags 0940 and 0941, and the final paragraph of
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe uC vC r uD vD s wA wB
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

section ConeComparison
open HomologicalComplex
universe u v u' v'
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Abelian A] [Abelian B]
variable (F : A ⥤ B) [F.Additive]
variable {P : CochainComplex A ℤ} {Q : CochainComplex B ℤ}
  (φ : P ⟶ P) (ψ : Q ⟶ Q)
  (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅ Q)
  (h : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫ e.hom = e.hom ≫ ψ)

private def cc : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (CochainComplex.mappingCone φ) ≅ CochainComplex.mappingCone ψ :=
  CochainComplex.mappingCone.mapHomologicalComplexIso φ F ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by dsimp; omega⟩)
      (Arrow.isoMk e e (by simpa using h.symm))

private def cs : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((CochainComplex.mappingCone φ)⟦(-1 : ℤ)⟧) ≅
      (CochainComplex.mappingCone ψ)⟦(-1 : ℤ)⟧ :=
  ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso (-1)).app _ ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso (cc F φ ψ e h)

end ConeComparison

set_option maxHeartbeats 800000 in
-- The statement contains simultaneous universe-polymorphic cone comparisons.
end CategoryTheory
