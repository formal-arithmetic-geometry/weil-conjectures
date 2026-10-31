/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDerivedCoefficientData
public import WeilConjectures.AlgebraicGeometry.ModuleObjects
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

import all WeilConjectures.AlgebraicGeometry.QcqsIntegralFiniteModelCompleteness
import all WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealizationSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence

/-! # Reconstruction of a constructible integral sheaf from its derived reductions -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option synthInstance.maxSize 4096 in
/-- A constructible integral sheaf is the Roos limit of its positive derived reductions.
The levels are the actual quotient tensor functors, including their degree minus one
cohomology when the sheaf has torsion.

Source: blueprint sk-lem-int-ext.proof.md, paragraph (2), first sentence; Bhatt--Scholze,
Definition 6.5.1 and Lemmas 6.5.3--6.5.4; Stacks Tag 099M.
(blueprint: lem-sf-integral-constructible-reduction-limit).

Proof: realize the constructible sheaf in degree zero. The integral-model criterion
identifies it as derived complete. The length-one free resolution of each uniformizer
power quotient identifies the recorded tensor reduction with the corresponding derived
quotient. The quotient projections provide compatible transition maps between these
actual reductions. Derived completeness identifies the original object with their
homotopy inverse limit. Countable products exist in the Grothendieck module category
and its derived category; the standard Roos triangle for this tower then gives the
asserted derived-limit triangle. Indexing by n+1 is cofinal among positive powers.
This includes the zero sheaf and the empty scheme, and makes no torsion-freeness claim. -/
theorem integral_constructible_reduction_limit
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (N : pulledBackModuleObjects (integralCoefficientRing l E) X)
    (hN : IsConstantModelConstructible (integralCoefficientRing l E) X N) :
    ∃ hp : HasProduct (fun n : ℕ ↦ (integralReductionFunctor l E X (n + 1)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N)),
      let := hp
      ∃ step : ∀ n : ℕ,
        (integralReductionFunctor l E X (n + 2)).obj
            ((DerivedCategory.singleFunctor _ 0).obj N) ⟶
          (integralReductionFunctor l E X (n + 1)).obj
            ((DerivedCategory.singleFunctor _ 0).obj N),
        IsDerivedLimit (K := fun n : ℕ ↦
          (integralReductionFunctor l E X (n + 1)).obj
            ((DerivedCategory.singleFunctor _ 0).obj N)) step
          ((DerivedCategory.singleFunctor _ 0).obj N) := by
  classical
  have _ := hl
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of D.k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of D.k))
  let K := (DerivedCategory.singleFunctor _ 0).obj N
  have hK : IsDerivedComplete l E X K := complete_sheaf l E X N hN
  obtain ⟨P, hP, ⟨eP⟩, hη⟩ := hK
  let := AdicCompletion.modules_countableAB4Star l E X
  let := derivedCategory_hasCountableProducts (AdicCompletion.Modules l E X)
  obtain ⟨a, ha, _⟩ := PrincipalNormalization.principal_tensor_scalar_extension l E X
  let V : ℕ → integralDerived l E X := fun n ↦
    (integralReductionFunctor l E X (n + 1)).obj K
  let W := AdicCompletion.integralLevel l E X K
  let t : ∀ n, V (n + 1) ⟶ V n := fun n ↦
    (DerivedNakayama.reductionMap l E X (AdicCompletion.quotientStep l E n)).app K
  let s := AdicCompletion.integralStep l E X K
  let aK (n : ℕ) : V n ≅ W n := (a n).app K
  let B : ∏ᶜ V ≅ ∏ᶜ W :=
    { hom := Limits.Pi.map (fun n ↦ (aK n).hom)
      inv := Limits.Pi.map (fun n ↦ (aK n).inv)
      hom_inv_id := by apply Pi.hom_ext; intro n; simp [Category.assoc]
      inv_hom_id := by apply Pi.hom_ext; intro n; simp [Category.assoc] }
  have hB : towerTransitionEndomorphism t ≫ B.hom =
      B.hom ≫ towerTransitionEndomorphism s := by
    exact (towerTransitionEndomorphism_natural_backward t s
      (fun n ↦ (aK n).hom) (fun n ↦ (ha n K).symm)).symm
  obtain ⟨p, δ, htri, _⟩ := AdicCompletion.roos_isDerivedLimit l E X K P hP eP
  have : IsIso (AdicCompletion.completionMap l E X K P eP) := by
    dsimp only [AdicCompletion.completionMap]
    infer_instance
  let e := asIso (AdicCompletion.completionMap l E X K P eP)
  refine ⟨inferInstance, t, e.hom ≫ p ≫ B.inv,
    B.hom ≫ δ ≫ (shiftFunctor _ (1 : ℤ)).map e.inv, ?_⟩
  apply (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk _ _ e B B ?_ hB ?_)).mpr htri
  · simp [Category.assoc]
  · simp [Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
