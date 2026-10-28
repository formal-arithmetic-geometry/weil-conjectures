/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U8
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetfulData

/-! # Retraction half of the native ordinary cone criterion -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/--
The rotated native cone gives a retraction of the underlying ordinary map.

Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`,
final exceptional-adjunction sentence. Complete the cone of `q`, rotate it,
and apply the detection hypothesis to its first arrow. Realization and the
faithful section/closure equivalences identify the resulting zero map in the
ordinary category, where the distinguished triangle splits. This is the
retraction half only; the finite-stalk argument is recorded separately.
(blueprint: lem-sf-native-ordinary-cone-retraction).
-/
theorem native_ordinary_cone_retraction (R : Family l D) (T : Space D)
    (V : ForgetModel D l R T) (H M : W D l T) (q : H ⟶ M)
    (e : Nonempty (V.functor.obj H ≅ V.functor.obj M))
    (hq : ∀ (K : W D l T) (v : K ⟶ H),
      WeilComplex.forget.map (v ≫ q) = 0 → V.functor.map v = 0) :
    Nonempty (SplitMono (WeilComplex.forget.map q)) := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
