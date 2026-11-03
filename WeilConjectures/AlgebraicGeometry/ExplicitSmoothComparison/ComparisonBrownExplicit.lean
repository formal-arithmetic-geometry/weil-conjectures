/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ExplicitSmoothAdjunctionData
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteEncodingUnit
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothNormalizedExistence
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.ConstantInternalModuleSheafEncoding.ConstantInternalModuleSheafEquivalenceSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.SixFunctors.ProEtale.Adic.FreeWeilCoefficientsProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement

/-! # The explicit smooth adjunction

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/
sk-thm-purity-transport/sk-prop-sp-comparison-brown-explicit.md and its proof.
(blueprint: det-sp-comparison-brown-explicit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace AlgebraicGeometry.ProEtale.ExplicitSmoothComparison

private theorem assemble_finiteNormalized {ell : ℕ} [Fact ell.Prime]
    {k : Type u} [Field k] (a : FiniteFamily ell k) (r : NonfiniteFamily ell k)
    (h : a.normalized ell k) : FiniteNormalized ell k (assemble a r) := by
  exact h

private theorem assemble_affineNormalized {ell : ℕ} [Fact ell.Prime]
    {k : Type u} [Field k] (a : FiniteFamily ell k) (r : NonfiniteFamily ell k)
    (h : a.affineNormalized ell k) : AffineNormalized ell k (assemble a r) := by
  exact h

private theorem assemble_scalarCompatible {ell : ℕ} [Fact ell.Prime]
    {k : Type u} [Field k] (a : FiniteFamily ell k) (r : NonfiniteFamily ell k)
    (hfin : a.scalarCompatible ell k)
    (hmix : MixedScalarCompatible ell k (assemble a r)) :
    ScalarCompatible ell k (assemble a r) := by
  intro c c' φ hφ
  by_cases hc : IsFiniteCoefficient c
  · cases c <;> simp only [IsFiniteCoefficient] at hc
    case finite A fin n hA =>
      by_cases hc' : IsFiniteCoefficient c'
      · cases c' <;> simp only [IsFiniteCoefficient] at hc'
        case finite A' fin' n' hA' =>
          exact hfin A fin n hA A' fin' n' hA' φ hφ
      · exact hmix _ _ φ hφ (Or.inr hc')
  · exact hmix _ _ φ hφ (Or.inl hc)

/-- The twisted shifted inverse image is right adjoint to the specified
compact-support functor for every admissible coefficient, with unit and counit
normalized by finite affine-line integration and its coefficient transports.

Source: sk-prop-sp-comparison-brown-explicit, all coefficient cases and normalization
(blueprint: det-sp-comparison-brown-explicit).

Proof: for finite coefficients, transport the exceptional adjunction through the
canonical purity comparison. Its orientation restricts on every etale coordinate
chart to the ordered affine-line integration orientation; the projection-formula
transpose computes the counit. For integral coefficients use the natural Hom
bijections and the compatible reductions. For finite extensions of Q_ell use
the model-independent Hom bijections obtained by scalar extension, and for the
algebraic closure use their filtered colimit. The coefficient comparison counit
identities transport the finite affine normalization through all these cases.
For a general positive-characteristic field, the geometric orientation argument
may be checked after the conservative algebraic-closure base change; smooth
base change for the dualizing complexes and Tate lines descends the comparison.
The unit is the transpose of the identity under these same Hom bijections, so
the triangles and both normalization equations belong to the same adjunction. -/
theorem comparisonBrownExplicit (k : Type u) [Field k]
    (ell : ℕ) [Fact ell.Prime] (hchar : (ringChar k).Prime)
    (hne : ell ≠ ringChar k) :
    ∃ b : Family ell k,
      FiniteNormalized ell k b ∧ AffineNormalized ell k b ∧ ScalarCompatible ell k b := by
  sorry

end AlgebraicGeometry.ProEtale.ExplicitSmoothComparison
