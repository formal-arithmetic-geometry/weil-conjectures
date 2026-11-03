/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

/-! # Scalar extension of the recorded nonnegative signed Tate line

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-rational,
sk-prop-sp-rational.proof.md, first paragraph and final endpoint of its Hom chain.
(blueprint: lem-sp-rational-signed-tate-line-scalar-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.SmoothPurityRational

private def nonnegativePower {C : Type*} [Category C] [MonoidalCategory C]
    (L : C) : ℕ → C
  | 0 => 𝟙_ C
  | n + 1 => Nat.rec L (fun _ P ↦ P ⊗ L) n

private theorem nonnegativePower_scalar
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (L : C) (n : ℕ) :
    Nonempty (F.obj (nonnegativePower L n) ≅ nonnegativePower (F.obj L) n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨(Functor.Monoidal.εIso F).symm⟩
  | one => exact ⟨Iso.refl _⟩
  | more n _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨(Functor.Monoidal.μIso F _ _).symm ≪≫ tensorIso e (Iso.refl _)⟩

set_option maxHeartbeats 1000000 in
-- Elaborating the section equivalence and derived tensor constraints needs this budget.
private theorem internalSigned_nonnegative
    (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) (n : ℕ) :
    Nonempty (spInternalSignedTwist T R L (n : ℤ) ≅ nonnegativePower L n) := by
  classical
  let J := Scheme.ProEt.topology T
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  let A := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R
  induction n using Nat.twoStepInduction with
  | zero =>
    exact ⟨e.inverse.mapIso
      (InternalAbelianSheafModule.comparison_unitIso.{u + 1, u + 1, u} J R).symm ≪≫
        e.unitIso.symm.app _⟩
  | one => exact ⟨e.unitIso.symm.app L⟩
  | more n _ ih =>
    obtain ⟨i⟩ := ih
    let P := spInternalSignedTwist T R L ((n + 1 : ℕ) : ℤ)
    let t := InternalAbelianSheafModule.comparison_tensorIso.{u + 1, u + 1, u} J R P L ≪≫
      SheafOfModules.tensorIsoSite.{u + 1, u, u + 1} A (e.functor.obj P) (e.functor.obj L) ≪≫
        (SheafOfModules.siteSheafTensorRight (e.functor.obj L)).mapIso
          (e.counitIso.app (spSignedTwist T R L ((n + 1 : ℕ) : ℤ)))
    exact ⟨e.inverse.mapIso t.symm ≪≫ e.unitIso.symm.app _ ≪≫
      tensorIso i (Iso.refl L)⟩

set_option maxHeartbeats 1000000 in
-- Elaborating the section equivalence and derived tensor constraints needs this budget.
/-- The scalar comparison for the specified signed Tate line, placed in degree zero.
Only nonnegative degrees are needed in smooth purity. No geometric adjunction or
constructibility assertion is included.

Source: latest blueprint sk-prop-sp-rational.proof.md, scalar extension of the Tate
line in the first paragraph and the right endpoint of the displayed Hom chain
(blueprint: lem-sp-rational-signed-tate-line-scalar-comparison).

Proof: scalar extension along O_E -> E is exact. Its left derived functor on a
single module therefore agrees with the single of the ordinary extension. The
rational first Tate line is, by definition, the ordinary extension of the integral
first Tate line. Use the exact section/internal module equivalence to compare the
recorded signed powers with the ordinary internal tensor powers. In degree zero
the comparison is the scalar-extension unit constraint. In degree one use the
section-equivalence unit and counit. In degree n+2 use the tensor comparison for
that equivalence, the induction hypothesis in degree n+1, and the strong monoidal
constraint of scalar extension. The sectionwise balanced tensor universal property
identifies these maps with the tensor powers used in spSignedTwist. Induction
provides mutually inverse module maps in every nonnegative degree. Applying the
single functor and the exact derived-scalar comparison gives the claimed isomorphism.
The construction includes degree zero, zero coefficients on an empty site, arbitrary
schemes, and ramified finite E; it needs no choice of local Tate basis. -/
theorem signedTateLineScalarComparison
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (T : Scheme.{u}) (d : ℕ) :
    Nonempty ((Mod.extendScalars (padicIntegersToPadicSubfield T l E)).leftDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (spInternalSignedTwist T _ (spIntegralTwist T l E) (d : ℤ))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (spInternalSignedTwist T _ (spRationalTwist T l E) (d : ℤ))) := by
  classical
  let F := Mod.extendScalars (padicIntegersToPadicSubfield T l E)
  have : F.Monoidal := Mod.extendScalarsMonoidal _
  obtain ⟨e0⟩ := internalSigned_nonnegative T _ (spIntegralTwist T l E) d
  obtain ⟨e1⟩ := nonnegativePower_scalar F (spIntegralTwist T l E) d
  obtain ⟨e2⟩ := internalSigned_nonnegative T _ (spRationalTwist T l E) d
  let e : F.obj (spInternalSignedTwist T _ (spIntegralTwist T l E) (d : ℤ)) ≅
      spInternalSignedTwist T _ (spRationalTwist T l E) (d : ℤ) :=
    F.mapIso e0 ≪≫ e1 ≪≫ e2.symm
  exact ⟨F.leftDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e⟩

end AlgebraicGeometry.ProEtale.SmoothPurityRational
