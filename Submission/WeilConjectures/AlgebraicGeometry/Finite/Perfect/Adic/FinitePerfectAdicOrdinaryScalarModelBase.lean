/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import Submission.WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Submission.WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Ordinary scalar comparison definitions and exactness -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] completedAdicChangeData completedAdicRing

/-- Ordinary completed realization, written without the later tensor-cone modules.
Source: Stacks Tags 093J and 093M. -/
abbrev finitePerfectAdicScalarModelOrdinary (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) : ModuleCat.{t} A ⥤ CompletedAdicModules X d :=
  finitePerfectAdicConstant X A ⋙ completedAdicScalarExtension X d

instance finitePerfectAdicScalarModelOrdinary_additive
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) :
    (finitePerfectAdicScalarModelOrdinary X d).Additive := by
  have := (finitePerfectAdicConstant_exact X A).1
  unfold finitePerfectAdicScalarModelOrdinary
  infer_instance

/-- The ordinary coefficient-universe transport. Source: Stacks Tag 05RU. -/
abbrev finitePerfectAdicScalarModelLift (B : Type t) [CommRing B] :
    ModuleCat.{t} B ⥤ ModuleCat.{t + 1} (ULift.{t + 1} B) :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom

/-- Universe transport commutes with scalar restriction, on the identical lifted action.
Source: Stacks Tag 05RU. -/
def finitePerfectAdicScalarModelLiftRestrict {B D : Type t} [CommRing B] [CommRing D]
    (q : B →+* D) :
    ModuleCat.restrictScalars q ⋙ finitePerfectAdicScalarModelLift B ≅
      finitePerfectAdicScalarModelLift D ⋙ ModuleCat.restrictScalars (RingHom.ulift q) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

end AlgebraicGeometry.Scheme
