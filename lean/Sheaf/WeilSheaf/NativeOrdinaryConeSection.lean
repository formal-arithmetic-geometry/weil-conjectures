/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U8
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetfulData

/-! # Section half of the native ordinary cone criterion -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/--
Constructible finite stalks turn the split injection from the cone into a
section of the underlying ordinary map when the common-stage objects are
isomorphic.

Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`,
final exceptional-adjunction sentence. Transport the common-stage isomorphism
through realization and compare every cohomological geometric stalk; finite
dimensional vector spaces with equal dimension make the split injection
surjective. Conservativity of constructible stalks and derived cohomology
produces the section. This is the section half only.
(blueprint: lem-sf-native-ordinary-cone-section).
-/
theorem native_ordinary_cone_section (R : Family l D) (T : Space D)
    (V : ForgetModel D l R T) (H M : W D l T) (q : H ⟶ M)
    (e : Nonempty (V.functor.obj H ≅ V.functor.obj M))
    (hq : ∀ (K : W D l T) (v : K ⟶ H),
      WeilComplex.forget.map (v ≫ q) = 0 → V.functor.map v = 0) :
    Nonempty (SplitEpi (WeilComplex.forget.map q)) := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
