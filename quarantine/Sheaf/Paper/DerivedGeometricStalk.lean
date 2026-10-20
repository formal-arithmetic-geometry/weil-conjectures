/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.PurityConventions
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Derived geometric stalk

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-trace-perfectness,
`pur9-def-derived-stalk.md` (blueprint: pur9-def-derived-stalk).

The positive coefficient level is written `n + 1`, as in `finiteDerivedPullback`.
After that intrinsic pullback, the canonical coefficient realization inverse converts
module sheaves to fixed-scalar sheaves before applying the published derived sections.
The resulting complex retains its coefficient action, with the standard universe lift.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The derived geometric stalk is derived sections on `Spec Ω` of the finite-coefficient
intrinsic derived pullback. The inverse of the canonical coefficient realization only
changes the presentation of the module sheaf; it does not forget scalars. Here `n + 1`
ranges over all positive levels, and `Ω` is separably closed. No finite-type condition
on the point, or on its source scheme, is imposed.
Source: blueprint main-20261015, `pur9-def-derived-stalk.md`, displayed definition
(blueprint: pur9-def-derived-stalk). -/
def finiteDerivedGeometricStalk (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (X : Scheme.{u}) (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (xbar : Spec (.of Ω) ⟶ X)
    (K : proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1))) :
    DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))) :=
  letI : Finite (finiteCoefficientRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
  (ProEtale.rightDerivedGlobalSections
    (ModuleCat.{u + 1} (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
    (Spec (.of Ω))).obj
      ((sfIntrinsicModuleEquivalence (Spec (.of Ω))
        (finiteCoefficientRing l E (n + 1))).inverse.mapDerivedCategory.obj
          ((finiteDerivedPullback l E n xbar).obj K))

end WeilConjectures
