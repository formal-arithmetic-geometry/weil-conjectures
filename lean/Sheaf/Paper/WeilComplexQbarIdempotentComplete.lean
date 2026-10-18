/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.SfWeilSheafComplex
import Sheaf.Paper.QbarIdempotentComplete
public import Mathlib.CategoryTheory.Idempotents.Karoubi
import Sheaf.Paper.DerivedPullbackTensorHom

/-! # Idempotent completeness of the common-stage Weil category

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-purity-conv`,
node `lem-weil-weil-complex-qbar-idempotent-complete`
(blueprint: lem-weil-weil-complex-qbar-idempotent-complete).

The common-stage Weil category is the fixed-pair category
`sfCommonStageWeilComplex`; the theorem records its idempotent completeness and
the equivalence with its Karoubi envelope.
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Idempotents AlgebraicGeometry

namespace WeilConjectures

/-- The common-stage `Qbar` Weil category is idempotent complete, and its
canonical inclusion into the Karoubi envelope is an equivalence.

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-purity-conv`,
node `lem-weil-weil-complex-qbar-idempotent-complete`
(blueprint: lem-weil-weil-complex-qbar-idempotent-complete).

Proof: (1) Put C = D^b_c(Y,Qbar) and T = Lg_Y*. Base change preserves finite
type: a finite affine cover by finitely generated k₀-algebras base changes to
one by finitely generated k-algebras. Thus `qbar_idempotent_complete` applies
to Y = D.geometricFiber Y₀ and makes C idempotent complete.
(2) T is additive by the rational and common-stage morphism formulas in
`def-weil-derived-pullback-tensor-hom`. Commuting arrows form subgroups of
the underlying Hom groups. The zero object and biproducts inherit their
Frobenius structures, making the fixed-pair category additive.
(3) For an idempotent e on (K,theta), choose i : L → K and r : K → L with
r i = 1 and i r = e. The commuting equation is e theta = theta T(e).
Give L the structure theta_L = r theta T(i), with inverse
T(r) theta⁻¹ i. Their composites reduce to r e i = 1 and T(r e i) = 1.
Moreover i theta_L = theta T(i) and theta_L T(r) = r theta, so i and r
are fixed-pair morphisms splitting e.
(4) By `def-weil-karoubi-envelope`, these maps identify (L,1) with (K,e)
in the envelope: their composites are its identities 1 and e. Thus the
canonical inclusion is essentially surjective; it is fully faithful by
`lem-weil-karoubi-envelope-fully-faithful` (Mathlib's `fullyFaithfulToKaroubi`).
It is consequently an equivalence.
-/
theorem weil_complex_qbar_idempotent_complete
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
    [IsAlgClosure (Padic l) Qbar]
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    IsIdempotentComplete (sfCommonStageWeilComplex D l hl Y₀ Qbar) ∧
      (toKaroubi (sfCommonStageWeilComplex D l hl Y₀ Qbar)).IsEquivalence := by
  sorry

end WeilConjectures
