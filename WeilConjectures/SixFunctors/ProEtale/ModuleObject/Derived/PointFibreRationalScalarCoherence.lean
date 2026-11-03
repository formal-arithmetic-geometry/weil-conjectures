/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTensorReduction.CondensedPointTensorReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
import WeilConjectures.AlgebraicGeometry.FinitePointComparison.CondensedPointDerivedScalarComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfectGeneral
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

/-! # Native rational point-fibre scalar coherence

Source: the finite-reduction and scalar-extension compatibility clause of
`sk-thm-sf-kunneth-relative` (blueprint: lem-sf-point-fibre-rational-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

-- Use the published small-site specialization of the exact scalar cup.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 20000]
  CategoryTheory.InternalAbelianSheafModule.comparison_essentiallySmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction
open scoped CategoryTheory.Obj TensorProduct
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Pin point tensor and unit maps to the uniquely sectionwise-normalized cup. Its
`chain_summand` and `tensor_normalization` fields are the balanced K-flat form of
the ambient comparison at (M,C(Gamma N)); there is no newly chosen cup witness.
Source: native section cup, proof step 1; Stacks 0FPJ and 0FPK
(blueprint: lem-sf-point-fibre-rational-scalar-coherence). -/
def NativePointTensor (A : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    (P : PointData A k) : Prop :=
  (∀ (M N : CohomologyTransport.D A.X (Spec (.of k)))
    (hM : condensedConstructibleFiniteTor A.X (Spec (.of k)) M)
    (hN : condensedConstructibleFiniteTor A.X (Spec (.of k)) N),
    (P.tensorIso M N hM hN).inv =
      (ExactSectionsDerivedCup.derived.{u + 2, u + 1, u + 1, u + 1, u + 1}
      (pairingExactScalarPointCup.{u} A.X k)).μ M N) ∧
  P.unitIso.inv = (ExactSectionsDerivedCup.derived.{u + 2, u + 1, u + 1, u + 1, u + 1}
    (pairingExactScalarPointCup.{u} A.X k)).ε

end AlgebraicGeometry.ProEtale.CondensedRing
