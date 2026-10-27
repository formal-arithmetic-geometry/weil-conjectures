/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseScalarCoherence

/-! # Coherent operations on classical raw lisse realizations

Source: BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-raw-lisse-common-system).
## Main definitions

* `CommonSystem`: the actual classical stages, transitions and associator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace WeilConjectures.ClassicalRawLisse
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : PerAdic.Base D.k)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Classical pairs with directed-colimit Homs, mapped by the finite realization.
The stage morphism's coherence and representative formula fix the map on colimits.
Source: Weil II (1.1.1)d, BS 6.8.4(4)
(blueprint: def-zl-classical-raw-lisse-common-system). -/
structure CommonSystem (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) (c : ScalarCoherence D l hl a b s o) where
  system : StageSystem (fun i : AlgebraicallyClosedCoefficients.Index l Ω ↦
    Rational D l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W)
  transitions {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    system.T h = (o.scalar (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) W
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)).raw
  associator {i j k : AlgebraicallyClosedCoefficients.Index l Ω}
      (h : i ≤ j) (h' : j ≤ k) :
    HEq (system.assoc h h').hom
      ((c.scalarComp (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω k) W
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω j k h')).hom)


end WeilConjectures.ClassicalRawLisse
