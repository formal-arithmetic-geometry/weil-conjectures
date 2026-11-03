/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # Integral constructible internal Hom for arbitrary admissible integral rings

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
cor-coef-integral-internal-hom.md and its proof, order 2992
(blueprint: def-coef-admissible-integral-hom-data).

All categories are ordinary derived categories of modules over pulled-back condensed
rings. The scalar maps below are the actual quotient maps, at exponent n itself.
No extension field or coefficient presentation is chosen in their construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralCoefficientHom

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The specified comparison transposes the actual reduced evaluation.
Source: latest blueprint `lem-coef-integral-hom-reduction.proof.md`, evaluation
compatibility in paragraph 2 (blueprint: def-coef-admissible-integral-hom-data).
The equality is the inverse law of the tensor--Hom adjunction. -/
theorem comparison_evaluation (X : Scheme.{u}) (π : R) (n : ℕ)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))) :
    ((reduction R X π n).obj K ◁ comparison R X π n K L) ≫
        (CondensedRing.derivedTensorHomAdjunction
          (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R)))
          ((reduction R X π n).obj K)).counit.app ((reduction R X π n).obj L) =
      (reductionTensorIso R X π n K
        (((CondensedRing.derivedHom (Profinite.continuousCoefficientRingObj R) X).obj
          (op K)).obj L)).inv ≫
        (reduction R X π n).map
          ((CondensedRing.derivedTensorHomAdjunction
            (Profinite.continuousCoefficientRingObj R) K).counit.app L) := by
  let adj := CondensedRing.derivedTensorHomAdjunction
    (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R)))
    ((reduction R X π n).obj K)
  change (adj.homEquiv _ _).symm ((adj.homEquiv _ _) _) = _
  exact (adj.homEquiv _ _).symm_apply_apply _

private theorem reductionTensorIso_inv_eq_μ (X : Scheme.{u}) (π : R) (n : ℕ)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))) :
    letI := Mod.extendScalarsMonoidal (coefficientMap (quotientMap R π n) X)
    letI := Mod.extendScalars_preservesFlat (coefficientMap (quotientMap R π n) X)
    letI := (Mod.extendScalars (coefficientMap (quotientMap R π n) X)).leftDerivedFunctorMonoidal
    (reductionTensorIso R X π n K L).inv =
      Functor.LaxMonoidal.μ (reduction R X π n) K L := by
  let := Mod.extendScalarsMonoidal (coefficientMap (quotientMap R π n) X)
  let := Mod.extendScalars_preservesFlat (coefficientMap (quotientMap R π n) X)
  let := (Mod.extendScalars (coefficientMap (quotientMap R π n) X)).leftDerivedFunctorMonoidal
  apply (cancel_mono (reductionTensorIso R X π n K L).hom).1
  rw [Iso.inv_hom_id]
  exact (Functor.Monoidal.μ_δ (reduction R X π n) K L).symm

/-- The evaluation-defined arrow is the native monoidal internal-Hom comparison.
Source: latest blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1
(blueprint: def-coef-admissible-integral-hom-data).
The derived tensorator is inverse to the recorded scalar tensor comparison, so
both arrows are the transpose of the same evaluation. -/
theorem comparison_eq_ihomComparison (X : Scheme.{u}) (π : R) (n : ℕ)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))) :
    letI := Mod.extendScalarsMonoidal (coefficientMap (quotientMap R π n) X)
    letI := Mod.extendScalars_preservesFlat (coefficientMap (quotientMap R π n) X)
    letI := (Mod.extendScalars (coefficientMap (quotientMap R π n) X)).leftDerivedFunctorMonoidal
    comparison R X π n K L =
      (Functor.LaxMonoidal.ihomComparison (reduction R X π n) K).natTrans.app L := by
  let := Mod.extendScalarsMonoidal (coefficientMap (quotientMap R π n) X)
  let := Mod.extendScalars_preservesFlat (coefficientMap (quotientMap R π n) X)
  let := (Mod.extendScalars (coefficientMap (quotientMap R π n) X)).leftDerivedFunctorMonoidal
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry]
  change MonoidalClosed.curry
    ((reductionTensorIso R X π n K ((ihom K).obj L)).inv ≫ _) = _
  rw [reductionTensorIso_inv_eq_μ]
  rfl


end AlgebraicGeometry.ProEtale.IntegralCoefficientHom
