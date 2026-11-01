/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalDualComparison

/-! # Quotient compatibility of the structural finite relative trace -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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

/-- Quotient tensor preserves the relative trace defined from the absolute structural counit.

Source: current blueprint lem-coef-finite-exceptional, proof paragraph 2, compatibility of
absolute dualizing and compact-support coefficient change; lem-coef-finite-dualizing.
(blueprint: lem-sf-finite-exceptional-trace-quotient).

Proof: first work on the ordinary etale site. Transpose the proposed equality through the
absolute exceptional adjunction on Y. The counit normalization of dualizing coefficient
change turns its left side into the scalar image of the absolute counit on X followed by
the quotient unit. On the right, move the scalar support comparison through the fixed
compact-support compositor. Proper mate pasting and the extension-by-zero unit give the
same scalar image of that absolute counit. Injectivity of the absolute adjunction gives
the etale trace square. Transport through the specified etale/pro-etale realization and
finiteDualizingOrigin. The restriction comparison is normalized on the underlying sheaf;
quotientAdjunction is its transported scalar adjunction. Adjoint uniqueness therefore
identifies the transported dualizing map with dualizingQuotientMap. Naturality of the
support origins identifies the transported support comparison with supportMap. Cancel the
origin isomorphisms to obtain the displayed intrinsic equation. For equal indices these
are the scalar unit equations. The construction also applies to the zero object and the
empty scheme, and does not require the quotient to be flat. -/
theorem finiteTrace_quotient {m n : ℕ} (h : n ≤ m) :
    (reduction l E Y h).map (CoefDualFormulaScalarTranspose.finiteTrace D l E f c m) ≫
        dualizingQuotientMap l E D hl Y h =
      (supportMap l E f c h).app (integralDualizingFiniteTerm l E D X m) ≫
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
          (dualizingQuotientMap l E D hl X h) ≫
        CoefDualFormulaScalarTranspose.finiteTrace D l E f c n := by
  sorry

end WeilConjectures.FiniteExceptional
