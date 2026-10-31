/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData

/-! # Finite exceptional coefficient comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

/-- Invertibility of the specified exceptional quotient mate.
Source: current blueprint proof paragraph 2, duality comparison and transposition
(blueprint: lem-sf-finite-exceptional-quotient-is-iso).
Proof: use the finite Verdier coefficient comparison on Y and X. Commuting reduction
past ordinary pullback gives t from Q_X(f*D_Y L) to f*D_Y(Q_Y L). Apply D_X to its
inverse and compose with the X duality comparison to get an isomorphism Q_X H_m L
to H_n Q_Y L. Conjugate by the uniquely normalized dualFormulaIso at both levels.
Evaluation preservation of finite Hom coefficient change and trace preservation of
dualizing coefficient change identify its counit transpose with inverse q followed
by reduction of the old counit. Hom injectivity therefore identifies this natural
isomorphism with the already specified b. The full inclusion reflects invertibility.
No quotient is assumed flat; all inputs are constructible and of finite Tor amplitude,
and equal indices are included. -/
theorem exceptional_quotient_isIso {m n : ℕ} (h : n ≤ m) :
    IsIso (b l E D hl f c h) := by
  sorry

end WeilConjectures.FiniteExceptional
