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
  intro m n t h k L
  let Fm := F l E D hl f c m
  let Ft := F l E D hl f c t
  let Gm := G l E D hl f c m
  let adjt := adjunction l E D hl f c t
  let ex := reassoc l E X h k
  let ey := reassoc l E Y h k
  let qab := q l E D hl f c h
  let qbc := q l E D hl f c k
  let qac := q l E D hl f c (k.trans h)
  let K := Gm.obj L
  have hi : Ft.map (ex.inv.app K) ≫ qbc.inv.app ((Q l E X h).obj K) ≫
      (Q l E Y k).map (qab.inv.app K) =
        qac.inv.app K ≫ ey.inv.app (Fm.obj K) := by
    have hh := IsIso.inv_eq_inv.mpr (hc h k K)
    simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
      Category.assoc] using hh
  have hc' : Ft.map (ex.hom.app K) ≫ qac.inv.app K =
      qbc.inv.app ((Q l E X h).obj K) ≫
        (Q l E Y k).map (qab.inv.app K) ≫ ey.hom.app (Fm.obj K) := by
    let : IsIso (Ft.map (ex.inv.app K)) := (Ft.mapIso (ex.app K)).isIso_inv
    let : Epi (Ft.map (ex.inv.app K)) := IsIso.epi_of_iso _
    apply (cancel_epi (Ft.map (ex.inv.app K))).1
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [Ft.map_id, Category.id_comp]
    have hh := (congrArg (fun z ↦ z ≫ ey.hom.app (Fm.obj K)) hi).symm
    simp only [Category.assoc] at hh
    rw [Iso.inv_hom_id_app] at hh
    exact (Category.comp_id (qac.inv.app K)).symm.trans hh
  apply (adjt.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [show Ft.map ((G l E D hl f c t).map (ey.hom.app L)) ≫ adjt.counit.app _ =
    adjt.counit.app _ ≫ ey.hom.app L from adjt.counit.naturality _]
  unfold b
  slice_lhs 2 3 => rw [mateEquiv_counit]
  slice_lhs 1 2 => exact qbc.inv.naturality _
  simp only [Functor.comp_map, Category.assoc]
  slice_lhs 2 3 => rw [← Functor.map_comp, mateEquiv_counit, Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 3 4 => exact ey.hom.naturality ((adjunction l E D hl f c m).counit.app L)
  slice_lhs 1 3 => exact hc'.symm
  rw [mateEquiv_counit]
  exact Category.assoc _ _ _

end WeilConjectures.FiniteExceptional
