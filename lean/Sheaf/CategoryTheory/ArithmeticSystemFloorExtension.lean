/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.CategoryTheory.ArithmeticSystemRightAdjointData

/-! # Ordinary arithmetic floor extension

Source: the arithmetic-restriction argument in the integral-adjunction normalization;
Bhatt--Scholze, Lemma 3.5.7 (blueprint: lem-sp-arithmetic-system-floor-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

/-- Construct the additive exact right adjoint on strict systems, before localization.
The index embedding and the floor inequality have already been established.

Source: the arithmetic restriction paragraph of the integral-adjunction normalization;
Bhatt--Scholze, Definitions 3.5.2--3.5.3 and Lemma 3.5.7
(blueprint: lem-sp-arithmetic-system-floor-extension).

Proof: at k with e ≤ k+1 put q=(k+1)/e-1 and use restriction of N_q
along B_k → B_(r q); put zero at the remaining prefix. Use the original
transition of N between floor indices, viewed through the composite ring maps,
and zero into the prefix. Its identity and composition laws follow on sections
from those of N. Apply component maps of a morphism at the same floor indices;
the original transition squares give a functor, and addition is componentwise.
Restriction of scalars is exact, so evaluation of this functor is either an exact
restriction of scalars or zero. The componentwise abelian structure of strict
systems therefore proves preservation of finite limits and finite colimits.
Select a map at r n to define the forward Hom map. Extend a map g by
D.transition (hf k h) followed by restriction of g_q above the prefix and by
zero below it. Transition composition and the squares for g prove compatibility.
At selected levels q=n, giving one inverse identity. The square of any map into
the floor extension, taken from k to r q, forces its k component to be exactly
this extension of its selected component; maps to the zero prefix are unique.
This proves the other inverse identity and naturality. The identity map selects
to the identity, hence the counit formula; extending the identity gives the unit
with identity selected components. These are exactly the stated ordinary fields.
For e=1 the prefix is empty and all levels are selected; for e>1 the prefix
contains only zero target components, so it creates no extra compatibility condition.
-/
theorem arithmeticSystemFloorExtension (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (e : ℕ) (he : 1 ≤ e) (r : ℕ ↪o ℕ)
    (hr : ∀ n : ℕ, r n = e * (n + 1) - 1)
    (hf : ∀ k : ℕ, e ≤ k + 1 → r ((k + 1) / e - 1) ≤ k) :
    ∃ (R : StrictRingSystem (selectedSystemRings B r) ⥤ StrictRingSystem B)
      (_hadd : R.Additive) (_hlim : PreservesFiniteLimits R)
      (_hcolim : PreservesFiniteColimits R),
      Nonempty (ArithmeticSystemOrdinaryFloorData B e r hf R) := by sorry

end SheafOfModules
