/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.ClassicalRawLisseCommonRestriction

/-! # Descent of finite classical realizations to common coefficient stages -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ClassicalRawLisse
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- Descend the finite classical realization and its normalized restriction comparisons.
Source: Bhatt--Scholze, Proposition 6.8.4(3),(4), 6.8.14(1), Remark 6.8.15;
Weil II (1.1.1)d
(blueprint: lem-zl-classical-raw-lisse-common-descent).

Proof: Take Rational at each finite coefficient field as the classical stage category,
and the actual scalar raw functor for each transition. Use the scalar identity and
composition isomorphisms of h as unit and associator. Their coherence is checked after
postcomposition with the fully faithful finite raw realization, where the normalization
fields give the prescribed sf unit and balanced tensor associator. Those satisfy the
unit and pentagon equations. The finite raw realization functors and their normalized
scalar comparisons therefore define a morphism of stage systems. Its descended functor
has precisely these objects and common-stage maps. Every represented object is in
the common heart because its finite representative lies in the finite heart.
For fullness, represent a target arrow over one common larger finite field and use
fullness of the finite raw realization there. For faithfulness, move equality to a
common stage and use faithfulness there. This proves the Hom-colimit bijection.
Take the intrinsic common fibre specified by sfAdicCommonFiber_exists and its finite
comparisons. Composing each finite comparison with the scalar extension of the finite
classical fibre isomorphism defines classical_fibre and proves classical_normalization.
For a locally closed restriction, take the actual finite restriction functors as stage
components. Choose the supplied normalized mixed comparisons for its transition maps,
with the inverse orientation required by the stage morphism. The same faithful
normalization proves compatibility with the unit and associator. Descend the finite
raw restriction comparisons to the pair categories. On a representative the descended
map is exactly the finite map followed by inclusion, proving finite_comparison. All
checks take place at one common finite stage, including ranks zero and empty schemes. -/
theorem classical_raw_lisse_common_descent
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (s : Family D l hl a b) (o : Operations D l hl a b s)
    (h : Coherence D l hl a b s o)
    (hm : ∀ (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
      (W V : PerAdic.Base D.k) (i : E →ₐ[ℚ_[l]] F)
      (f : V.scheme ⟶ W.scheme) [IsImmersion f],
      Nonempty (Mixed D l hl E W F a b s o i V f)) :
    ∃ c : ∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
      (W : PerAdic.Base D.k), Common D l hl W Ω a b s o h.toScalarCoherence,
      ∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (W V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f],
        Nonempty (CommonRestriction D l hl W Ω a b s o h.toScalarCoherence V f
          (c Ω W) (c Ω V)) := by
  sorry

end WeilConjectures.ClassicalRawLisse
