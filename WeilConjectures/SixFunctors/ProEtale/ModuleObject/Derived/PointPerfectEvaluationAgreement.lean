/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfectGeneral
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointFibreTensorModels
public import WeilConjectures.AlgebraicGeometry.FlatCohomologyDerivedTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat

/-! # Compatibility of fixed point evaluation and perfect realization

Source: Steps 1 and 3 of the Frobenius pairing proof.
(blueprint: lem-pod-point-perfect-evaluation-agreement)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj TensorProduct
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The fixed regular-section/terminal-section comparison agrees with the canonical
perfect evaluation, including the specified cup and unit squares.
Source: Step 7 of the point-sections transport plan and the first paragraph of
`sk-lem-finite.proof.md`.
Proof: use the geometric-point perfect-realization theorem to obtain the closure
witnesses, perfect values, and the exact braided equivalence. At the heart level,
the point equivalence counit, regular-section evaluation at one, and scalar-ring
identification send the ordinary section pairing to the pure-tensor pairing.
Thus `pointSectionsHeartIso` is monoidal for the ordinary scalar restriction
normalization. The signed total-complex construction preserves that square on
every total summand. Its K-flat localization square identifies it with the
normalized `TraceCupPoint.tensor`; the degree-zero unit square similarly
identifies `pointCoefficientUnit`. Deriving the heart comparison gives exactly
`pointEvaluationCTFComparison`. Restrict to constructible finite-Tor objects and
retain the one braided structure for equivalence, closed comparison and both
squares. The closed evaluation and duality identities are the canonical ones
already supplied by the perfect-realization theorem.
(blueprint: lem-pod-point-perfect-evaluation-agreement). -/
theorem point_perfect_evaluation_agreement
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsAdmissibleCoefficient Λ) :
    Nonempty (PointEvaluationAgreement D Λ) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
