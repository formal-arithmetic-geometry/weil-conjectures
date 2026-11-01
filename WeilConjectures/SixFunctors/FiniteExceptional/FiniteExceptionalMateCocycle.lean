/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData

/-! Mate transfer of the finite exceptional quotient cocycle.

Source: `lem-coef-dualizing-quotient-mates`, specialized to the finite exceptional
adjunctions (blueprint: lem-sf-finite-exceptional-quotient-coherence).
Proof: apply the mate bijection to the q cocycle, move each q component across
its counit by naturality, replace its mate by b, and cancel the middle
unit-counit pair by the triangle identity. The remaining endpoint reassociation
is the displayed `reassoc` component. The dependent endpoint transport and
triangle cancellations are the substantial categorical calculation represented
by this split theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
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

theorem mate_cocycle
    (hc : ∀ {m n t : ℕ} (h : n ≤ m) (k : t ≤ n)
      (K : (domain l E X m).FullSubcategory),
      (Q l E Y k).map ((q l E D hl f c h).hom.app K) ≫
          (q l E D hl f c k).hom.app ((Q l E X h).obj K) ≫
          (F l E D hl f c t).map ((reassoc l E X h k).hom.app K) =
        (reassoc l E Y h k).hom.app ((F l E D hl f c m).obj K) ≫
          (q l E D hl f c (k.trans h)).hom.app K) :
    ∀ {m n t : ℕ} (h : n ≤ m) (k : t ≤ n)
      (L : (domain l E Y m).FullSubcategory),
      (Q l E X k).map ((b l E D hl f c h).app L) ≫
          (b l E D hl f c k).app ((Q l E Y h).obj L) ≫
          (G l E D hl f c t).map ((reassoc l E Y h k).hom.app L) =
        (reassoc l E X h k).hom.app ((G l E D hl f c m).obj L) ≫
          (b l E D hl f c (k.trans h)).app L := by
  sorry

end WeilConjectures.FiniteExceptional
