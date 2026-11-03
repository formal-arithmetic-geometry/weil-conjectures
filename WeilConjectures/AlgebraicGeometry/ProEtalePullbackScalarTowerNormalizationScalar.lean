/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
import WeilConjectures.SmoothPurity.CompletedScalarAssociator.PrescribedScalarAssociator

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- Presentation-level scalar tower normalization for one scheme.
Source: Stacks 03EK, 06YY.

Proof: identify the presentation tensor with sheafified change of rings. On pure tensors,
the canonical ordinary associator multiplies the two coefficient factors; its inverse
inserts the unit. Balancing and sheafification extend the formulas to all sections.
Transport this comparison through the universal derived counits to obtain the equation
on flat-term K-flat representatives. Universal localization identifies the resulting
derived isomorphism with the prescribed associator. The same universal property and
the pure tensor formulas prove uniqueness.
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization-scalar-package). -/
theorem scalarTowerNormalization_package
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (T : Scheme.{u}) :
    PrescribedScalarTowerNormalization φ ψ T := by
  sorry

end AlgebraicGeometry.ProEtale
