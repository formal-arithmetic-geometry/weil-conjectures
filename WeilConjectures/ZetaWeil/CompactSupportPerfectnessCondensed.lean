/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DerivedStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Compact-support perfectness in the condensed model

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-lem-finite/sk-prop-sf-trace-perfectness/
prop-trf-compact-support-perfectness.md and prop-trf-compact-support-perfectness.proof.md
(blueprint: prop-trf-compact-support-perfectness).

This statement binds the finite-field datum, coefficient stage, geometric scheme, and
condensed coefficient ring inline, as in the landed finite compact-support and geometric
stalk perfectness declaration. No parallel convention structure is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Compact-support cohomology and every geometric stalk are perfect ordinary coefficient
complexes for the current condensed finite-Tor model.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-lem-finite/sk-prop-sf-trace-perfectness/prop-trf-compact-support-perfectness.md,
with proof route in prop-trf-compact-support-perfectness.proof.md
(blueprint: prop-trf-compact-support-perfectness).

The postponed proof follows six steps. (1) Form compact support with the recorded
`rightDerivedLowerShriekOfCompactification` and use finite compact-support constructibility
to obtain bounded finite cohomology at the point. (2) Reduce from `A = O_E / pi_E^n` to
its residue ring and use the canonical derived change-of-rings and scalar-pullback
normalization. (3) The residue input is bounded constructible by the recorded finite-Tor
predicate and derived tensor constructibility, and compact support at residue level is
bounded constructible. (4) Apply the residue Tor criterion on the actual coefficient site
to obtain finite Tor amplitude for compact support. (5) Apply the finite-free point criterion,
using `intrinsic_coefficient_point`, to obtain perfectness over the ordinary coefficient
ring. (6) Apply exact inverse image, the finite-stalk criterion, and the recorded
`derivedGeometricStalk` comparison at every algebraically closed geometric point; no
finite-type hypothesis on the point field is used.
-/
theorem compactSupport_perfect
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom) :
    let A := Padic.coefficientExtensionRing ell E n
    letI : Finite A := Padic.finite_coefficientExtensionRing ell E n hn
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
    let Λ := Profinite.continuousMapRingObj.{u} A
    ∀ K : (ProEtale.CondensedRing.condensedConstructibleFiniteTor Λ X.left).FullSubcategory,
      DerivedCategory.IsPerfectRingComplex
        ((ProEtale.CondensedGeometricPoint.fiber Λ D.k).obj
          ((ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K.obj)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (xbar : Spec (.of Ω) ⟶ X.left),
        DerivedCategory.IsPerfectRingComplex
          ((ProEtale.derivedGeometricStalk
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) xbar).obj
            ((ProEtale.finiteCoefficientDerivedEquivalence X.left A).functor.obj K.obj)) := by
  sorry

end WeilConjectures
