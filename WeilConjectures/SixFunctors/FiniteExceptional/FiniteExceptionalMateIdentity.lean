/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CoefficientCounitMateCocycle

/-! Mate transfer of the finite exceptional identity equation.

Source: `lem-coef-dualizing-quotient-mates`, specialized to the finite exceptional
adjunctions (blueprint: lem-sf-finite-exceptional-quotient-coherence).
Proof: apply the mate bijection to the q identity equation, move the
selfReduction unitors through the counit by naturality, and cancel the resulting
unit-counit pair using the triangle identity. This leaves exactly the displayed
b multiplication-unit component. The dependent endpoint transport is the
substantial categorical calculation represented by this split theorem.
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

theorem mate_identity
    (hi : ∀ (n : ℕ) (L : (domain l E Y n).FullSubcategory),
      (q l E D hl f c (le_refl n)).hom.app ((G l E D hl f c n).obj L) =
        (selfReduction l E Y n).hom.app
          ((F l E D hl f c n).obj ((G l E D hl f c n).obj L)) ≫
          (F l E D hl f c n).map
            ((selfReduction l E X n).inv.app ((G l E D hl f c n).obj L))) :
    ∀ (n : ℕ) (L : (domain l E Y n).FullSubcategory),
      (b l E D hl f c (le_refl n)).app L ≫
          (G l E D hl f c n).map ((selfReduction l E Y n).hom.app L) =
        (selfReduction l E X n).hom.app ((G l E D hl f c n).obj L) := by
  intro n L
  let tc := Q l E X (le_refl n)
  let td := Q l E Y (le_refl n)
  let uC := selfReduction l E X n
  let uD := selfReduction l E Y n
  let N := L
  let nn : td.obj N ≅ N := (uD.app N)
  have hN : nn.hom = uD.hom.app N := by
    simp [nn]
  have hc : (q l E D hl f c (le_refl n)).hom.app
      ((G l E D hl f c n).obj L) =
      uD.hom.app ((F l E D hl f c n).obj ((G l E D hl f c n).obj L)) ≫
        (F l E D hl f c n).map (uC.inv.app ((G l E D hl f c n).obj L)) := by
    simpa [uC, uD] using hi n L
  have hh := CategoryTheory.Adjunction.coefficientCounitMate_identity
      (a := adjunction l E D hl f c n)
      (tc := tc) (td := td) (uC := uC) (uD := uD)
      (N := N) (n := nn) (hN := hN)
      (c := (q l E D hl f c (le_refl n)).hom)
      (hc := hc)
  apply ((adjunction l E D hl f c n).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit]
  have hh' := congrArg ((adjunction l E D hl f c n).homEquiv _ _).symm hh
  simpa [b, tc, td, uC, uD, N, nn, Category.assoc] using hh'

end WeilConjectures.FiniteExceptional
