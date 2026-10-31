/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeOrdinaryConeRetraction
import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeOrdinaryConeSection

/-! # Detecting invertibility by native cone maps

Source: the cone and constructible-finiteness argument in the ordinary exceptional
counit identification (blueprint: lem-sf-native-ordinary-cone-detection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- A native map detecting its ordinary kernel and joining isomorphic ordinary
objects is an ordinary isomorphism.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, final
exceptional-adjunction sentence; the distinguished-triangle splitting criterion
and finiteness of constructible cohomology stalks.

Proof: complete q to a distinguished triangle H -> M -> C -> H[1] of native Weil
complexes, and rotate it to C[-1] -> H -> M. The composite of its first map v with
q is zero. The kernel-detection hypothesis makes V(v) zero; the realization and the
faithful section and closure equivalences make the ordinary map underlying v zero.
Forgetting is triangulated, so the ordinary triangle splits:
the ordinary map underlying q has a left inverse. The isomorphism in the common
stage gives an ordinary isomorphism of H and M: apply rho, the ForgetModel
realization, and the inverse equivalences for sections and closure transport.
For every cohomological degree and every geometric point, the map induced by q is
now a split injection between finite-dimensional vector spaces of equal dimension.
It is thus bijective. Constructible geometric stalks detect sheaf isomorphisms,
and cohomology detects derived isomorphisms, so the underlying map is invertible.
This does not infer that a native morphism is zero from its underlying map being
zero. It also does not assume that the ordinary category is Hom-finite. The zero
object and an empty scheme satisfy the same argument.
(blueprint: lem-sf-native-ordinary-cone-detection). -/
theorem native_ordinary_cone_detection (R : Family l D) (T : Space D)
    (V : ForgetModel D l R T) (H M : W D l T) (q : H ⟶ M)
    (e : Nonempty (V.functor.obj H ≅ V.functor.obj M))
    (hq : ∀ (K : W D l T) (v : K ⟶ H),
      WeilComplex.forget.map (v ≫ q) = 0 → V.functor.map v = 0) :
    IsIso (WeilComplex.forget.map q) := by
  obtain ⟨sm⟩ := native_ordinary_cone_retraction D l R T V H M q e hq
  obtain ⟨se⟩ := native_ordinary_cone_section D l R T V H M q e hq
  let _ : IsSplitMono (WeilComplex.forget.map q) := IsSplitMono.mk' sm
  let _ : IsSplitEpi (WeilComplex.forget.map q) := IsSplitEpi.mk' se
  exact isIso_of_mono_of_isSplitEpi _

end WeilConjectures.NativeExceptionalForgetful
