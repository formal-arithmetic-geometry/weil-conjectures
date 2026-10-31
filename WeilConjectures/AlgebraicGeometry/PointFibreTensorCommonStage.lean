/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ExactScalarPointCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

/-!
# Canonical condensed point tensor and coefficient unit

Source: current blueprint, `sec-six-functors/sk-thm-sf-kunneth-relative`, Step 5,
with point coefficients from `def-weil-finite-coefficient-point`
in `sec-six-functors-basics/sk-thm-sfb-proper-base-change`.
The normalization is the derived sections cup of Stacks Tags 0B6C and 0FPK.
(blueprint: def-sf-point-fibre-tensor-common-stage)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A supplied point tensor and unit family is normalized by the actual derived
sections cup and coefficient evaluation. This is a predicate on supplied maps;
it does not assert their existence or coherence.
Source: current blueprint, `sec-six-functors/sk-thm-sf-kunneth-relative`, Step 5;
Stacks Tags 0B6C and 0FPK.
(blueprint: def-sf-point-fibre-tensor-common-stage) -/
def condensedPointTensorCanonicality
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E)
    (_hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E))
    (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : Mon.mk Λ = Mon.mk (CondensedGeometricPoint.residueRingObj.{u} ℓ E π n) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E) ∨
      Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj.{u} E) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ))
    (c : ∀ (M N : AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor
        Λ (Spec (.of D.k))),
      ((CohomologyTransport.sections Λ (Spec (.of D.k))).mapDerivedCategory.obj
        (((derivedTensor Λ (Spec (.of D.k))).obj M.obj).obj N.obj)) ≅
      (((curriedTensor _).obj
        ((CohomologyTransport.sections Λ (Spec (.of D.k))).mapDerivedCategory.obj M.obj)).obj
        ((CohomologyTransport.sections Λ (Spec (.of D.k))).mapDerivedCategory.obj N.obj)))
    (u : (CohomologyTransport.sections Λ (Spec (.of D.k))).mapDerivedCategory.obj
      (𝟙_ _) ≅ 𝟙_ _) : Prop :=
  (∀ (M N : AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor
        Λ (Spec (.of D.k))),
      (c M N).inv =
        (pairingExactScalarPointCup Λ D.k).derived.μ M.obj N.obj) ∧
    u = (pairingExactScalarPointCup_unitIso Λ D.k).symm

end AlgebraicGeometry.ProEtale.CondensedRing
