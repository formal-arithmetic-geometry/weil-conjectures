/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Tate twists in the intrinsic common-stage category

Source: blueprint main-20261015, coefficient twists, order 1864
(blueprint: def-coefficient-twists-detailed).

The completed root line and its signed tensor powers are the published constructions.
Only their membership in the intrinsic integral category needs a new interface.
The common-stage twist is the published derived tensor with this coefficient object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe d u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

end WeilConjectures
