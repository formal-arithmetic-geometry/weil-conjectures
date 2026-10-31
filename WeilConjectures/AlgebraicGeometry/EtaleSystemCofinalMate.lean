/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSystemCofinalData
import WeilConjectures.CategoryTheory.DerivedCategory.NormalizedAdjunctionComposition
import WeilConjectures.AlgebraicGeometry.EtaleCofinalSupportRealization
import WeilConjectures.AlgebraicGeometry.EtaleCofinalSupportComposition
import WeilConjectures.NumberTheory.Padics.LocalFieldCoefficientStages

/-! # Cofinal compact-support adjunction mates

The geometric interfaces are re-exported from EtaleSystemCofinalData.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a av b bv c cv d dv
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.Etale.SystemProjection

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
section FormalMate
variable
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {LX : C ⥤ A} {UX : A ⥤ C} {LY : D ⥤ B} {UY : B ⥤ D}
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    (x : LX ⊣ UX) (y : LY ⊣ UY) (f : F ⊣ G) (g : F' ⊣ G')
    (h : LX ⋙ F ≅ F' ⋙ LY)

private theorem cofinalMate_hom (N : C) (M : B) (z : N ⟶ UX.obj (G.obj M)) :
    z ≫ (cofinalMate x y f g h).hom.app M =
      g.homEquiv N (UY.obj M)
        (y.homEquiv _ M (h.inv.app N ≫ (f.homEquiv _ M).symm
          ((x.homEquiv N _).symm z))) := by
  let a := x.comp f
  let b := (g.comp y).ofNatIsoLeft h.symm
  change z ≫ (a.rightAdjointUniq b).hom.app M = _
  have hh : z ≫ (a.rightAdjointUniq b).hom.app M =
      b.homEquiv N M ((a.homEquiv N M).symm z) := by
    apply (b.homEquiv N M).symm.injective
    rw [Equiv.symm_apply_apply, b.homEquiv_naturality_left_symm]
    have hb := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app a b M
    simp only [Functor.comp_obj] at hb
    exact (congrArg (fun v ↦ (LX ⋙ F).map z ≫ v) hb).trans
      (a.homEquiv_counit N M z).symm
  rw [hh]
  simp only [b, a, Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv,
    Equiv.symm_trans_apply, Iso.symm_hom]
  rfl

private theorem cofinalMate_counit (M : B) :
    h.hom.app (UX.obj (G.obj M)) ≫
      LY.map (F'.map ((cofinalMate x y f g h).hom.app M)) ≫
      LY.map (g.counit.app (UY.obj M)) ≫ y.counit.app M =
        F.map (x.counit.app (G.obj M)) ≫ f.counit.app M := by
  let rho := (cofinalMate x y f g h).hom.app M
  have hh := (x.comp f).rightAdjointUniq_hom_app_counit
    ((g.comp y).ofNatIsoLeft h.symm) M
  have hn := h.hom.naturality rho
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  change F.map (LX.map rho) ≫ _ = _ at hh
  simp only [Adjunction.ofNatIsoLeft_counit, Functor.comp_obj,
    Functor.whiskerLeft_app, Iso.symm_inv, NatTrans.comp_app,
    Adjunction.comp_counit_app] at hh
  rw [← Category.assoc, hn, Category.assoc] at hh
  exact hh

private theorem cofinalMate_conjugate :
    (cofinalMate x y f g h).hom = conjugateEquiv (x.comp f) (g.comp y) h.inv := by
  ext M
  simp [cofinalMate, Adjunction.rightAdjointUniq, conjugateEquiv_apply_app,
    Adjunction.ofNatIsoLeft_unit, Functor.map_comp, Category.assoc]

end FormalMate

private theorem cofinalAdjunction_comp_assoc
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
    {H : C ⥤ D} {T : D ⥤ C} (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ T) :
    (a.comp b).comp c = a.comp (b.comp c) := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp,
    Functor.comp_obj, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
private theorem cofinalCompositor_conjugate
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {L L' : A ⥤ B} {R R' : B ⥤ A} (a : L ⊣ R) (b : L' ⊣ R') (i : R ≅ R') :
    conjugateEquiv a b (((a.ofNatIsoRight i).leftAdjointUniq b).inv) = i.hom := by
  ext M
  have hc : (conjugateEquiv a b
      (((a.ofNatIsoRight i).leftAdjointUniq b).inv)).app M =
      b.homEquiv _ _
        (((a.ofNatIsoRight i).leftAdjointUniq b).inv.app (R.obj M) ≫
          a.counit.app M) := by
    simp only [conjugateEquiv_apply_app, Adjunction.homEquiv_unit,
      Functor.map_comp]
  rw [hc, Adjunction.leftAdjointUniq_inv_app, leftAdjointUniq_homEquiv_comp,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit,
    Adjunction.right_triangle_components, Category.id_comp]
  rfl

private theorem cofinalMate_comp
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {E : Type c} [Category.{cv} E] {H : Type d} [Category.{dv} H]
    {Lx : C ⥤ A} {Ux : A ⥤ C} {Ly : D ⥤ B} {Uy : B ⥤ D}
    {Lx' : E ⥤ C} {Ux' : C ⥤ E} {Ly' : H ⥤ D} {Uy' : D ⥤ H}
    {Lxt : E ⥤ A} {Uxt : A ⥤ E} {Lyt : H ⥤ B} {Uyt : B ⥤ H}
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    {F'' : E ⥤ H} {G'' : H ⥤ E}
    (x : Lx ⊣ Ux) (y : Ly ⊣ Uy) (x' : Lx' ⊣ Ux') (y' : Ly' ⊣ Uy')
    (xt : Lxt ⊣ Uxt) (yt : Lyt ⊣ Uyt)
    (f : F ⊣ G) (g : F' ⊣ G') (k : F'' ⊣ G'')
    (cx : Ux ⋙ Ux' ≅ Uxt) (cy : Uy ⋙ Uy' ≅ Uyt)
    (h : Lx ⋙ F ≅ F' ⋙ Ly) (h' : Lx' ⋙ F' ≅ F'' ⋙ Ly')
    (ht : Lxt ⋙ F ≅ F'' ⋙ Lyt)
    (hc : ∀ N : E,
      F.map ((((x'.comp x).ofNatIsoRight cx).leftAdjointUniq xt).hom.app N) ≫
          ht.hom.app N =
        h.hom.app (Lx'.obj N) ≫ Ly.map (h'.hom.app N) ≫
          (((y'.comp y).ofNatIsoRight cy).leftAdjointUniq yt).hom.app (F''.obj N))
    (M : B) :
    cx.hom.app (G.obj M) ≫ (cofinalMate xt yt f k ht).hom.app M =
      Ux'.map ((cofinalMate x y f g h).hom.app M) ≫
        (cofinalMate x' y' g k h').hom.app (Uy.obj M) ≫ G''.map (cy.hom.app M) := by
  let ax := ((x'.comp x).ofNatIsoRight cx).leftAdjointUniq xt
  let ay := ((y'.comp y).ofNatIsoRight cy).leftAdjointUniq yt
  have hi : Functor.isoWhiskerRight ax F ≪≫ ht =
      Functor.isoWhiskerLeft Lx' h ≪≫ Functor.isoWhiskerRight h' Ly ≪≫
        Functor.isoWhiskerLeft F'' ay := by
    apply Iso.ext
    ext N
    exact hc N
  have hinv := congrArg Iso.inv hi
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv] at hinv
  let a0 := x'.comp (x.comp f)
  let a1 := x'.comp (g.comp y)
  let a2 := k.comp (y'.comp y)
  let a3 := xt.comp f
  let a4 := k.comp yt
  have hx : conjugateEquiv a0 a3 (Functor.whiskerRight ax.inv F) =
      Functor.whiskerLeft G cx.hom := by
    dsimp only [a0, a3]
    rw [← cofinalAdjunction_comp_assoc]
    exact (conjugateEquiv_whiskerRight (x'.comp x) xt f ax.inv).trans
      (congrArg (Functor.whiskerLeft G) (cofinalCompositor_conjugate (x'.comp x) xt cx))
  have hy : conjugateEquiv a2 a4 (Functor.whiskerLeft F'' ay.inv) =
      Functor.whiskerRight cy.hom G'' := by
    dsimp only [a2, a4]
    rw [conjugateEquiv_whiskerLeft, cofinalCompositor_conjugate]
  have h1 : conjugateEquiv a0 a1 (Functor.whiskerLeft Lx' h.inv) =
      Functor.whiskerRight (cofinalMate x y f g h).hom Ux' := by
    rw [cofinalMate_conjugate]
    exact conjugateEquiv_whiskerLeft (x.comp f) (g.comp y) x' h.inv
  have h2 : conjugateEquiv a1 a2 (Functor.whiskerRight h'.inv Ly) =
      Functor.whiskerLeft Uy (cofinalMate x' y' g k h').hom := by
    dsimp only [a1, a2]
    rw [← cofinalAdjunction_comp_assoc, ← cofinalAdjunction_comp_assoc]
    exact (conjugateEquiv_whiskerRight (x'.comp g) (k.comp y') y h'.inv).trans
      (congrArg (Functor.whiskerLeft Uy) (cofinalMate_conjugate x' y' g k h').symm)
  have hh : Functor.whiskerLeft G cx.hom ≫ (cofinalMate xt yt f k ht).hom =
      Functor.whiskerRight (cofinalMate x y f g h).hom Ux' ≫
        Functor.whiskerLeft Uy (cofinalMate x' y' g k h').hom ≫
          Functor.whiskerRight cy.hom G'' := by
    rw [← hx, ← hy, ← h1, ← h2, cofinalMate_conjugate]
    rw [conjugateEquiv_comp a0 a3 a4,
      ← Category.assoc, conjugateEquiv_comp a0 a1 a2,
      conjugateEquiv_comp a0 a2 a4]
    exact congrArg (conjugateEquiv a0 a4) (hinv.trans (Category.assoc _ _ _))
  exact congr_app hh M


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem cofinalSupport_mates
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (t : CofinalSupport c l)
    (hc : (∀ (B : Coefficients.{u} l) (r s : ℕ ↪o ℕ)
        (N : Derived X (cofinalCoefficients B (s.trans r)).rings),
        (t.projection.support B).F.map
            ((cofinalExtensionComposition (t.extensionX B r)
              (t.extensionX (cofinalCoefficients B r) s) (t.extensionX B (s.trans r))
              (t.compositionX B r s)).hom.app N) ≫ (t.h B (s.trans r)).hom.app N =
          (t.h B r).hom.app ((t.extensionX (cofinalCoefficients B r) s).model.derived.obj N) ≫
            (t.extensionY B r).model.derived.map ((t.h (cofinalCoefficients B r) s).hom.app N) ≫
            (cofinalExtensionComposition (t.extensionY B r)
              (t.extensionY (cofinalCoefficients B r) s) (t.extensionY B (s.trans r))
              (t.compositionY B r s)).hom.app
                ((t.projection.support (cofinalCoefficients B (s.trans r))).F.obj N))) :
      (∀ (B : Coefficients.{u} l) (r s : ℕ ↪o ℕ)
        (N : Derived X (cofinalCoefficients B (s.trans r)).rings),
        (t.projection.support B).F.map
            ((cofinalExtensionComposition (t.extensionX B r)
              (t.extensionX (cofinalCoefficients B r) s) (t.extensionX B (s.trans r))
              (t.compositionX B r s)).hom.app N) ≫ (t.h B (s.trans r)).hom.app N =
          (t.h B r).hom.app ((t.extensionX (cofinalCoefficients B r) s).model.derived.obj N) ≫
            (t.extensionY B r).model.derived.map ((t.h (cofinalCoefficients B r) s).hom.app N) ≫
            (cofinalExtensionComposition (t.extensionY B r)
              (t.extensionY (cofinalCoefficients B r) s) (t.extensionY B (s.trans r))
              (t.compositionY B r s)).hom.app
                ((t.projection.support (cofinalCoefficients B (s.trans r))).F.obj N)) ∧
      (∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
        (G : Derived Y B.rings ⥤ Derived X B.rings)
        (H : Derived Y (cofinalCoefficients B r).rings ⥤
          Derived X (cofinalCoefficients B r).rings)
        (a : (t.projection.support B).F ⊣ G)
        (b : (t.projection.support (cofinalCoefficients B r)).F ⊣ H),
        (∀ (N : Derived X (cofinalCoefficients B r).rings) (M : Derived Y B.rings)
          (z : N ⟶ (cofinalU X B r).obj (G.obj M)),
          z ≫ (t.rho B r a b).hom.app M =
            b.homEquiv N ((cofinalU Y B r).obj M)
              ((t.extensionY B r).model.adjunction.homEquiv _ M
                ((t.h B r).inv.app N ≫ (a.homEquiv _ M).symm
                  (((t.extensionX B r).model.adjunction.homEquiv N _).symm z)))) ∧
        (∀ M : Derived Y B.rings,
          (t.h B r).hom.app ((cofinalU X B r).obj (G.obj M)) ≫
            (t.extensionY B r).model.derived.map
              ((t.projection.support (cofinalCoefficients B r)).F.map
                ((t.rho B r a b).hom.app M)) ≫
            (t.extensionY B r).model.derived.map
              (b.counit.app ((cofinalU Y B r).obj M)) ≫
            (t.extensionY B r).model.adjunction.counit.app M =
          (t.projection.support B).F.map
              ((t.extensionX B r).model.adjunction.counit.app (G.obj M)) ≫ a.counit.app M)) ∧
      (∀ (B : Coefficients.{u} l) (r s : ℕ ↪o ℕ)
        (G : Derived Y B.rings ⥤ Derived X B.rings)
        (H : Derived Y (cofinalCoefficients B r).rings ⥤
          Derived X (cofinalCoefficients B r).rings)
        (K : Derived Y (cofinalCoefficients B (s.trans r)).rings ⥤
          Derived X (cofinalCoefficients B (s.trans r)).rings)
        (a : (t.projection.support B).F ⊣ G)
        (b : (t.projection.support (cofinalCoefficients B r)).F ⊣ H)
        (d : (t.projection.support (cofinalCoefficients B (s.trans r))).F ⊣ K)
        (M : Derived Y B.rings),
        (t.compositionX B r s).derived.hom.app (G.obj M) ≫
            (t.rho B (s.trans r) a d).hom.app M =
          (cofinalU X (cofinalCoefficients B r) s).map ((t.rho B r a b).hom.app M) ≫
            (t.rho (cofinalCoefficients B r) s b d).hom.app ((cofinalU Y B r).obj M) ≫
            K.map ((t.compositionY B r s).derived.hom.app M)) := by
  refine ⟨hc, ?_, ?_⟩
  · intro B r G H a b
    constructor
    · intro N M z
      exact cofinalMate_hom (t.extensionX B r).model.adjunction
        (t.extensionY B r).model.adjunction a b (t.h B r) N M z
    · intro M
      exact cofinalMate_counit (t.extensionX B r).model.adjunction
        (t.extensionY B r).model.adjunction a b (t.h B r) M
  · intro B r s G H K a b d M
    exact cofinalMate_comp
      (t.extensionX B r).model.adjunction (t.extensionY B r).model.adjunction
      (t.extensionX (cofinalCoefficients B r) s).model.adjunction
      (t.extensionY (cofinalCoefficients B r) s).model.adjunction
      (t.extensionX B (s.trans r)).model.adjunction
      (t.extensionY B (s.trans r)).model.adjunction a b d
      (t.compositionX B r s).derived (t.compositionY B r s).derived
      (t.h B r) (t.h (cofinalCoefficients B r) s) (t.h B (s.trans r))
      (hc B r s) M

/-- Cofinal restriction and the compact-support adjunction mate, with actual system
normalizations, evaluated inverse projection, Hom action, counits and composition.
Source: Zheng, Construction 4.1 and Lemma 5.22, printed pp. 21 and 36
(blueprint: lem-pur-etale-system-cofinal-mate).

Proof: (1) Repeat the selected tower in the finite blocks of the least-index map.
The block-repetition theorem supplies strict open comparison and the normalized
total-derived proper comparison. Simultaneously flat-term K-flat system representatives
identify selected extension with repetition followed by coefficient extension; the
unit and universal-counit equations fix this factorization, including maps and transitions.
(2) Apply lem-pur-etale-system-coefficient-projection to D_m=C_(r(t(m)))→C_m.
Its inverse, followed by the repetition comparison, constructs h on actual derived
systems. Its evaluation is exactly inverse single-ring projection; naturality and
the coefficient cocycle give the selected transitions, including equal least indices.
(3) Repetition preserves the normalized scalar unit and the restriction square, so
its coefficient comparison commutes with q by equality of scalar-adjunction transposes.
The identity t_(r∘s)=t_s∘t_r, the projection cocycle, and block composition give the
h-composition equation under the canonical adjunction-compatible extension compositor.
(4) Compose the extension/restriction and support adjunctions. Transport one left
adjoint along h and apply counit-compatible right-adjoint uniqueness. Expanding the
composite Hom equivalences gives precisely the displayed Hom chain. Its naturality
is map action on all derived morphisms. (5) Expand the two composite counits to obtain
the displayed counit equation. The canonical derived-functor factors and uniqueness
make all maps independent of resolutions. (6) Concatenate the Hom chains for r and s.
The h-composition equation identifies their middle factors, and uniqueness gives the
rho-composition equation. (7) The local-field specialization is stated separately
below: equality of principal ideals identifies the quotient towers and all maps.
No boundedness, normalization, flatness or separatedness of Y enters these arguments. -/
theorem etaleSystemCofinalMate
    (k : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (hl : l.Prime) (hlp : l ≠ k.p)
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) :
    ∃ t : CofinalSupport c l,
      (∀ (B : Coefficients.{u} l) (r s : ℕ ↪o ℕ)
        (N : Derived X.left (cofinalCoefficients B (s.trans r)).rings),
        (t.projection.support B).F.map
            ((cofinalExtensionComposition (t.extensionX B r)
              (t.extensionX (cofinalCoefficients B r) s) (t.extensionX B (s.trans r))
              (t.compositionX B r s)).hom.app N) ≫ (t.h B (s.trans r)).hom.app N =
          (t.h B r).hom.app ((t.extensionX (cofinalCoefficients B r) s).model.derived.obj N) ≫
            (t.extensionY B r).model.derived.map ((t.h (cofinalCoefficients B r) s).hom.app N) ≫
            (cofinalExtensionComposition (t.extensionY B r)
              (t.extensionY (cofinalCoefficients B r) s) (t.extensionY B (s.trans r))
              (t.compositionY B r s)).hom.app
                ((t.projection.support (cofinalCoefficients B (s.trans r))).F.obj N)) ∧
      (∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
        (G : Derived Y.left B.rings ⥤ Derived X.left B.rings)
        (H : Derived Y.left (cofinalCoefficients B r).rings ⥤
          Derived X.left (cofinalCoefficients B r).rings)
        (a : (t.projection.support B).F ⊣ G)
        (b : (t.projection.support (cofinalCoefficients B r)).F ⊣ H),
        (∀ (N : Derived X.left (cofinalCoefficients B r).rings) (M : Derived Y.left B.rings)
          (z : N ⟶ (cofinalU X.left B r).obj (G.obj M)),
          z ≫ (t.rho B r a b).hom.app M =
            b.homEquiv N ((cofinalU Y.left B r).obj M)
              ((t.extensionY B r).model.adjunction.homEquiv _ M
                ((t.h B r).inv.app N ≫ (a.homEquiv _ M).symm
                  (((t.extensionX B r).model.adjunction.homEquiv N _).symm z)))) ∧
        (∀ M : Derived Y.left B.rings,
          (t.h B r).hom.app ((cofinalU X.left B r).obj (G.obj M)) ≫
            (t.extensionY B r).model.derived.map
              ((t.projection.support (cofinalCoefficients B r)).F.map
                ((t.rho B r a b).hom.app M)) ≫
            (t.extensionY B r).model.derived.map
              (b.counit.app ((cofinalU Y.left B r).obj M)) ≫
            (t.extensionY B r).model.adjunction.counit.app M =
          (t.projection.support B).F.map
              ((t.extensionX B r).model.adjunction.counit.app (G.obj M)) ≫ a.counit.app M)) ∧
      (∀ (B : Coefficients.{u} l) (r s : ℕ ↪o ℕ)
        (G : Derived Y.left B.rings ⥤ Derived X.left B.rings)
        (H : Derived Y.left (cofinalCoefficients B r).rings ⥤
          Derived X.left (cofinalCoefficients B r).rings)
        (K : Derived Y.left (cofinalCoefficients B (s.trans r)).rings ⥤
          Derived X.left (cofinalCoefficients B (s.trans r)).rings)
        (a : (t.projection.support B).F ⊣ G)
        (b : (t.projection.support (cofinalCoefficients B r)).F ⊣ H)
        (d : (t.projection.support (cofinalCoefficients B (s.trans r))).F ⊣ K)
        (M : Derived Y.left B.rings),
        (t.compositionX B r s).derived.hom.app (G.obj M) ≫
            (t.rho B (s.trans r) a d).hom.app M =
          (cofinalU X.left (cofinalCoefficients B r) s).map ((t.rho B r a b).hom.app M) ≫
            (t.rho (cofinalCoefficients B r) s b d).hom.app ((cofinalU Y.left B r).obj M) ≫
            K.map ((t.compositionY B r s).derived.hom.app M)) := by
  obtain ⟨t, hi, hq⟩ := etaleCofinalSupport_realization k l hl hlp X Y f c
  exact ⟨t, cofinalSupport_mates t (etaleCofinalSupport_composition t hi hq)⟩

/-- The quotient projection at a positive tower level, fixing the canonical
identification on every ring element.
Source: Zheng 4.1 (blueprint: lem-pur-etale-system-cofinal-mate). -/
def cofinalQuotientProjection {O : Type (u + 1)} [CommRing O] (z : O) (n : ℕ) :
    O →+* (O ⧸ Ideal.span ({z} : Set O) ^ (n + 1)) :=
  Ideal.Quotient.mk (Ideal.span ({z} : Set O) ^ (n + 1))

private theorem cofinalQuotientTower_map_mk {O : Type (u + 1)} [CommRing O]
    (z : O) {m n : ℕᵒᵖ} (f : m ⟶ n) (x : O) :
    ((cofinalQuotientTower z).map f).hom (cofinalQuotientProjection z m.unop x) =
      cofinalQuotientProjection z n.unop x := by
  let q : (Functor.const ℕᵒᵖ).obj (CommRingCat.of O) ⟶ cofinalQuotientTower z :=
    NatTrans.ofOpSequence
      (fun n ↦ CommRingCat.ofHom (cofinalQuotientProjection z n)) (by
        intro n
        simp only [Functor.const_obj_map, cofinalQuotientTower,
          Functor.ofOpSequence_map_homOfLE_succ]
        ext x
        rfl)
  exact (congrArg (fun g ↦ g.hom x) (q.naturality f)).symm

private theorem quotient_eqToHom_mk {O : Type (u + 1)} [CommRing O]
    (I J : Ideal O) (h : I = J) (x : O) :
    (eqToHom (congrArg (fun K : Ideal O ↦ CommRingCat.of (O ⧸ K)) h)).hom
        (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x := by
  subst J
  rfl

private theorem quotientFunctor_eq
    {C : Type a} [Category.{av} C] {O : CommRingCat.{u + 1}}
    {F G : C ⥤ CommRingCat.{u + 1}}
    (p : (Functor.const C).obj O ⟶ F) (q : (Functor.const C).obj O ⟶ G)
    (hobj : ∀ n, F.obj n = G.obj n)
    (hq : ∀ n, p.app n ≫ eqToHom (hobj n) = q.app n)
    (hp : ∀ n, Function.Surjective (p.app n)) : F = G := by
  refine CategoryTheory.Functor.ext_of_iso
    (NatIso.ofComponents (fun n ↦ eqToIso (hobj n)) ?_) hobj (fun _ ↦ rfl)
  intro m n f
  let : Epi (p.app m) := ConcreteCategory.epi_of_surjective _ (hp m)
  apply (cancel_epi (p.app m)).1
  change p.app m ≫ (F.map f ≫ eqToHom (hobj n)) =
    p.app m ≫ (eqToHom (hobj m) ≫ G.map f)
  calc
    _ = p.app n ≫ eqToHom (hobj n) := by
      rw [← Category.assoc, ← p.naturality f]
      simp only [Functor.const_obj_map, Functor.const_obj_obj, Category.id_comp]
    _ = q.app n := hq n
    _ = _ := by
      rw [← Category.assoc, hq m]
      simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.id_comp] using
        q.naturality f

private def cofinalQuotientTowerProjection {O : Type (u + 1)} [CommRing O] (z : O) :
    (Functor.const ℕᵒᵖ).obj (CommRingCat.of O) ⟶ cofinalQuotientTower z where
  app n := CommRingCat.ofHom (cofinalQuotientProjection z n.unop)
  naturality := by
    intro m n f
    ext x
    exact (cofinalQuotientTower_map_mk z f x).symm

private def cofinalSelectedProjection {O : Type (u + 1)} [CommRing O]
    (v : O) (r : ℕ ↪o ℕ) : (Functor.const ℕᵒᵖ).obj (CommRingCat.of O) ⟶
      r.toOrderHom.toFunctor.op ⋙ cofinalQuotientTower v where
  app n := (cofinalQuotientTowerProjection v).app (r.toOrderHom.toFunctor.op.obj n)
  naturality := fun _ _ f ↦
    (cofinalQuotientTowerProjection v).naturality (r.toOrderHom.toFunctor.op.map f)

private theorem quotientProjection_eq {O : Type (u + 1)} [CommRing O]
    (I J : Ideal O) (h : I = J) :
    CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        eqToHom (congrArg (fun K : Ideal O ↦ CommRingCat.of (O ⧸ K)) h) =
      CommRingCat.ofHom (Ideal.Quotient.mk J) := by
  subst J
  rfl

private theorem cofinalQuotientTower_eq {O : Type (u + 1)} [CommRing O]
    (v s : O) (r : ℕ ↪o ℕ)
    (h : ∀ n : ℕ, Ideal.span ({v} : Set O) ^ (r n + 1) =
      Ideal.span ({s} : Set O) ^ (n + 1)) :
    r.toOrderHom.toFunctor.op ⋙ cofinalQuotientTower v = cofinalQuotientTower s := by
  exact quotientFunctor_eq (cofinalSelectedProjection v r) (cofinalQuotientTowerProjection s)
    (fun n ↦ congrArg (fun K : Ideal O ↦ CommRingCat.of (O ⧸ K)) (h n.unop))
    (fun n ↦ quotientProjection_eq _ _ (h n.unop))
    (fun _ ↦ Ideal.Quotient.mk_surjective)

/-- The ramified quotient identification is an equality of entire coefficient
functors, normalized by the identity on representatives. Hence substitution along
this equality transports the strict-system categories, all derived functors, h,
and its actual right-adjoint mate rho, including their action on every morphism.
It does not merely identify their separate evaluated objects.

Source: Zheng 4.1; the local-field clause of the DAG statement
(blueprint: lem-pur-etale-system-cofinal-mate).

Proof: The equality (s)=(v)^e gives (s)^(n+1)=(v)^(e*(n+1)).
The positive-index embedding has r(n)+1=e*(n+1). Equal ideals give the
identity-on-representatives quotient identification. Quotient transition maps
are induced by the identity on the integer ring, so the identifications commute
with every transition and give equality of the whole ring functors. Finite
quotients and l-primary torsion follow from the finite residue field of the
integer DVR and the fact that a power of its maximal ideal contains l. These
properties supply the two coefficient objects; proof irrelevance and the
functor equality identify the selected object with the s-power object. All
constructions and maps of etaleSystemCofinalMate then transport by substitution
of this equality, retaining the same compactification and fixed adjunctions. -/
theorem etaleSystemCofinalMate_localField
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (v s : Padic.coefficientExtensionIntegers l E)
    (hv : Ideal.span ({v} : Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E)
    (e : ℕ) (he : 1 ≤ e)
    (hs : Ideal.span ({s} : Set (Padic.coefficientExtensionIntegers l E)) =
      Ideal.span ({v} : Set (Padic.coefficientExtensionIntegers l E)) ^ e) :
    ((cofinalRamification e he).toOrderHom.toFunctor.op ⋙ cofinalQuotientTower v =
        cofinalQuotientTower s) ∧
      (∀ n : ℕ, HEq (cofinalQuotientProjection v (cofinalRamification e he n))
        (cofinalQuotientProjection s n)) ∧
      ∃ B C : Coefficients.{u} l,
        B.rings = cofinalQuotientTower v ∧ C.rings = cofinalQuotientTower s ∧
          cofinalCoefficients B (cofinalRamification e he) = C := by
  let O := Padic.coefficientExtensionIntegers l E
  have hindex (n : ℕ) : cofinalRamification e he n + 1 = e * (n + 1) := by
    change e * (n + 1) - 1 + 1 = e * (n + 1)
    exact Nat.sub_add_cancel (Nat.mul_pos (show 0 < e from he) (Nat.succ_pos n))
  have hideal (n : ℕ) :
      Ideal.span ({v} : Set O) ^ (cofinalRamification e he n + 1) =
        Ideal.span ({s} : Set O) ^ (n + 1) := by
    rw [hs, ← pow_mul, hindex]
  have htower := cofinalQuotientTower_eq v s (cofinalRamification e he) hideal
  refine ⟨htower, ?_, ?_⟩
  · intro n
    unfold cofinalQuotientProjection
    have hmk (I J : Ideal O) (h : I = J) :
        HEq (Ideal.Quotient.mk I) (Ideal.Quotient.mk J) := by
      subst J
      rfl
    exact hmk _ _ (hideal n)
  · obtain ⟨f, hf, _, _, e', w, he', hpow, hstages, _⟩ :=
      Padic.local_field_coefficient_stages l E E (fun _ ↦ rfl) v v hv hv
    let B : Coefficients.{u} l :=
      { rings := cofinalQuotientTower v
        finite := fun n ↦ by
          change Finite (O ⧸ Ideal.span ({v} : Set O) ^ (n + 1))
          rw [Ideal.span_singleton_pow]
          exact (hstages (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).2.1
        torsion := fun n ↦ by
          obtain ⟨N, _, hN, _⟩ :=
            (hstages (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).2.2.2.2.2.1
          refine ⟨N, ?_⟩
          change (l ^ N : O ⧸ Ideal.span ({v} : Set O) ^ (n + 1)) = 0
          rw [Ideal.span_singleton_pow]
          exact hN }
    exact ⟨B, cofinalCoefficients B (cofinalRamification e he), rfl, htower, rfl⟩

end AlgebraicGeometry.Etale.SystemProjection
