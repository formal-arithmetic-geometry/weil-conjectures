/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsHeartBound
import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsSectionsBound
import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
import WeilConjectures.CategoryTheory.Integral.IntegralStratumHomFormula
import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation

/-!
# Hom bound for a bounded classical torsion complex on an integral stratum

Source: blueprint latest, `sk-prop-int-compactness/sk-lem-int-ext-bound.proof.md`,
the dual-tensor and bounded-heart steps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace CategoryTheory

section

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

private theorem subsingleton_hom_of_internal_sections
    {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasDerivedCategory.{u + 1} A]
    [MonoidalCategory (DerivedCategory A)]
    (R : A) (eunit : (DerivedCategory.singleFunctor A 0).obj R ≅
      𝟙_ (DerivedCategory A))
    (P K : DerivedCategory A) (H : DerivedCategory A ⥤ DerivedCategory A)
    (adj : tensorLeft P ⊣ H)
    (hz : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} 0).obj
      ((preadditiveCoyoneda.obj (op R)).rightDerivedFunctor.obj (H.obj K)))) :
    Subsingleton (P ⟶ K) := by
  obtain ⟨e⟩ := derived_coyoneda_evaluation R 0
  have hz' := hz.of_iso (e.app (H.obj K))
  have hzero : Subsingleton (((DerivedCategory.singleFunctor A 0).obj R) ⟶
      (H.obj K) ⟦(0 : ℤ)⟧) := AddCommGrpCat.subsingleton_of_isZero hz'
  let E' := (Iso.homCongr (ρ_ P) (Iso.refl K)).symm |>.trans
    ((adj.homEquiv _ _).trans
      (Iso.homCongr eunit.symm ((shiftFunctorZero (DerivedCategory A) ℤ).symm.app
        (H.obj K))))
  exact E'.injective.subsingleton

end

end CategoryTheory
