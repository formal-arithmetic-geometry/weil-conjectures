/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.ConstantStalkLocalUnitPoint.ConstantStalkLocalUnitPoint
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius

/-! # The embedded-point return in the native positive-power convention

Source: latest blueprint, sec-zeta-weil/sk-thm-weil-final/prop-every-iterate-trace.md,
constant-sheaf clause; def-weil-local-frobenius-trace return convention
(blueprint: lem-zl-constant-stalk-local-unit-point).

This adds the native normalization and preserves the published point construction,
legacy return theorem and every existing consumer.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.ConstantStalkLocalUnitPoint

/-- Semilinear return of the same embedded point, using native positive powers.
Source: def-weil-local-frobenius-trace, semilinear return convention
(blueprint: lem-zl-constant-stalk-local-unit-point).
Proof: the legacy and native positive-power recursors have the same initial map
and recurrence, so induction on the exponent identifies their values for every
scheme endomorphism. The two point-Frobenius isomorphisms have the same Spec map.
Transport the existing embeddingPoint_return along these equalities. Equivalently,
the q^n-th power fixes the image of the finite subfield and comparison of the
arithmetic and closure projections of the pullback lift proves the return equation.
At n = 1 the exponent n - 1 is zero in the positive-power convention, hence gives
one Frobenius, as required. -/
theorem embeddingPoint_native_return (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (iota : D.extensionSubfield n hn →+* D.k)
    (hι : iota.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    embeddingPoint D Y₀ n hn x iota hι ≫
        NativeCondensedModule.localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom (n - 1) ≫
          embeddingPoint D Y₀ n hn x iota hι := by
  have hp {X : Scheme.{u}} (g : X ⟶ X) (m : ℕ) :
      NativeCondensedModule.localPositivePower g m = localPositivePower g m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [NativeCondensedModule.localPositivePower, localPositivePower, ih]
  simp only [hp]
  exact embeddingPoint_return D Y₀ n hn x iota hι

end WeilConjectures.ConstantStalkLocalUnitPoint
