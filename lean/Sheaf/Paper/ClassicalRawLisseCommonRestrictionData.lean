/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseCommonFibres
public import Sheaf.Paper.ClassicalRawLisseCoherence

/-! # Coherent operations on classical raw lisse realizations

Source: BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-raw-lisse-common-restriction-data).
## Main definitions

* `CommonRestrictionData`: descended restriction with prescribed finite stages and beta.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace WeilConjectures.ClassicalRawLisse
attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : PerAdic.Base D.k)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Common-stage restriction is descended from the finite classical restrictions;
its comparison uses the existing completed common-stage pullback on representatives.
Source: BS 6.8.15 and Weil II (1.1.1)d
(blueprint: def-zl-classical-raw-lisse-common-restriction-data). -/
structure CommonRestrictionData (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (o : Operations D l hl a b s) (c : ScalarCoherence D l hl a b s o)
    (V : PerAdic.Base D.k)
    (f : V.scheme ⟶ W.scheme) [IsImmersion f]
    (cW : Common D l hl W Ω a b s o c) (cV : Common D l hl V Ω a b s o c) where
  restriction : cW.system.Morphism cV.system
  stages (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    restriction.Φ i = (o.restriction
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W V f).raw
  mixed {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    Mixed D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω i) W
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω j) a b s o
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) V f
  scalar_comparison {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j) :
    HEq (restriction.β h) (mixed h).comparison.symm

end WeilConjectures.ClassicalRawLisse
