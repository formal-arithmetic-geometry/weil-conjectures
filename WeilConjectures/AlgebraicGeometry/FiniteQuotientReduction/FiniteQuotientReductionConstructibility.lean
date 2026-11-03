/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientIntrinsicTensor
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCoefficientComputation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat

/-! # Finite quotient reduction with its canonical constructible origin

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction.proof.md, first paragraph and final associativity sentence;
lem-sf-reduction-flat-model and its proof.
(blueprint: lem-pur-finite-reduction-constructibility).

All scalar functors are actual derived extensions. The comparison is fixed by the
local tensor formula and the derived counits, rather than supplied as an extra hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.FiniteQuotientReduction

/-- The finite ring Z/ell^r in the scheme universe.
Source: the node's coefficient convention (blueprint: lem-pur-finite-reduction-constructibility).
-/
abbrev Ring (ell r : ℕ) := ULift.{u} (ZMod (ell ^ r))

variable {ell : ℕ} [Fact ell.Prime]

end AlgebraicGeometry.FiniteQuotientReduction
