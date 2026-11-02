/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DerivedStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.ZetaWeil.CompactSupportPerfectnessCondensed

/-! # Perfectness of finite-coefficient compact cohomology and geometric stalks

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-lem-finite/
sk-prop-sf-trace-perfectness/_section.md and sk-prop-sf-trace-perfectness.proof.md
(blueprint: sk-prop-sf-trace-perfectness).

The input uses intrinsic bounded constructibility and relative finite Tor amplitude.
Compact cohomology is the ordinary point fibre of the specified compact-support image.
The stalk is the recorded derived geometric stalk after the canonical finite-coefficient
comparison. Its field is arbitrary algebraically closed, without a finite-type assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Compact cohomology and every geometric stalk are perfect ordinary coefficient complexes.
The scalar ring of `CondensedGeometricPoint.fiber` is the ring of sections on the singleton,
canonically the ordinary coefficient ring; the fixed-scalar stalk uses its universe lift.

Source: latest blueprint, part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-lem-finite/
sk-prop-sf-trace-perfectness, proposition and its proof paragraph
(blueprint: sk-prop-sf-trace-perfectness).

Proof: specialize prop-trf-compact-support-perfectness to A = O_E / pi_E^n.
Boundedness and constructibility give bounded compact cohomology and bounded stalks.
Finiteness gives finite cohomology modules. The finite-Tor input and the compact-support
and stalk Tor bounds give finite Tor amplitude for these ordinary complexes. Over the
Artinian local coefficient ring, the bounded finite-cohomology finite-Tor criterion gives
bounded models of finite projective modules, hence the two asserted perfectness clauses.
The point interpretation identifies R Gamma_c with the fibre of Ra_X!; the canonical
finite-coefficient comparison reads the same derived stalk as ordinary module sheaves.
-/
theorem finite_compactCohomology_and_geometricStalk_perfect
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
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (xbar : Spec (.of Ω) ⟶ X.left),
        DerivedCategory.IsPerfectRingComplex
          ((ProEtale.derivedGeometricStalk (ModuleCat.{u + 1} (ULift.{u + 1} A)) xbar).obj
            ((ProEtale.finiteCoefficientDerivedEquivalence X.left A).functor.obj K.obj)) := by
  exact compactSupport_perfect D ell _hell E n hn X c

end WeilConjectures
