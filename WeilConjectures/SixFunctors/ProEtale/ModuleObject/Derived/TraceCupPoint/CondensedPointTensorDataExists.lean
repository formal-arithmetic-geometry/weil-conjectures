/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensorOrdinaryExists
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedWeaklyContractible
import Mathlib.CategoryTheory.Sites.LocalSite
import WeilConjectures.SixFunctors.RingedSitePoint
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import WeilConjectures.SmoothPurity.RingedSitePointTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ExactDerivedMonoidalConstruction
import WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived

/-! Existence of the normalized point tensor data.
Source: Stacks 07A4 and 03EL, and the normalized section tensor construction
(blueprint: lem-pod-condensed-point-tensor-data-exists).
Proof plan: construct the ordinary tensorator on pure sections, extend it to the
signed total complex, and localize the K-flat comparison. The exact point-sections
functor preserves the required finite limits and colimits, so the construction
satisfies all fields of `ExactSectionsDerivedCup` and its pure-tensor formula.
This is a genuine construction statement and has no contradiction hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
  [PreservesFiniteLimits (condensedRingCoefficientSections Λ (Spec (.of k)))]
  [PreservesFiniteColimits (condensedRingCoefficientSections Λ (Spec (.of k)))]

set_option maxHeartbeats 800000 in
-- The record assembles eight universe-polymorphic derived tensor fields.
theorem tensorData_exists :
    ∃ d : ExactSectionsDerivedCup (condensedRingCoefficientSections Λ (Spec (.of k))),
      ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k))))
        (x : (condensedRingCoefficientSections Λ (Spec (.of k))).obj M)
        (y : (condensedRingCoefficientSections Λ (Spec (.of k))).obj N),
        (d.ordinary.μ M N).hom (x ⊗ₜ[Γ Λ] y) = (λ_ _).inv ≫ (x ⊗ₘ y) := by
  obtain ⟨m, hm⟩ := ordinaryTensorator_exists Λ k
  obtain ⟨t, _ht⟩ := tensorTail_exists Λ k m hm
  let d : ExactSectionsDerivedCup (condensedRingCoefficientSections Λ (Spec (.of k))) :=
    { ordinary := m
      derived := t.derived
      chain := t.chain
      chain_summand := t.chain_summand
      chainUnit := t.chainUnit
      chainUnit_zero := t.chainUnit_zero
      tensor_normalization := t.tensor_normalization
      unit_normalization := t.unit_normalization }
  refine ⟨d, ?_⟩
  simpa [d] using hm

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
