/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompatibility
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarCompatibility
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAffineGeometry
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction

/-! # Smooth purity for every admissible condensed coefficient

Source: current blueprint, sk-thm-purity-transport, all clauses, including the
2026-10-25 correction of the etale specialization.
(blueprint: sk-thm-purity-transport).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- The same family of explicit right adjunctions has the prescribed integration
counits, coefficient equations and geometric equations, and gives the unique
counit-compatible natural purity isomorphism to each specified Brown adjoint.
Source: current blueprint sk-thm-purity-transport
(blueprint: sk-thm-purity-transport).
Proof in words. For every finite ring, including nonregular and zero rings, use
the finite normalized counit system and its section-action realization. Reconstruct
the integral adjunction from the normalized positive tower and its transition
counits. Localize the Hom bijections and counits to obtain rational coefficients.
Descend objects and arrows for the algebraic closure to a common finite stage.
The resulting adjunctions have the displayed coefficient, base-change and
composition equations and the affine integration normalization. Restrict the
specified Brown adjunction to finite Tor objects. Uniqueness of right adjoints
with a fixed counit gives the natural gamma, uniquely satisfying its counit
identity. The transported finite and reconstructed comparisons satisfy that
identity and therefore are this same gamma. -/
theorem smooth_purity_transport (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) :
    ∃ a : AdjunctionFamily ell D,
      BrownComparison ell D a ∧
      ScalarCompatible ell D a ∧
      BaseChangeCompatible ell D a ∧
      CompositionCompatible ell D hEll a ∧
      AffineNormalized ell D a := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
