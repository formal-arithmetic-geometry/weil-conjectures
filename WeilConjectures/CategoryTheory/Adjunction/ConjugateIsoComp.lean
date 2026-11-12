/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCompCoherence

/-!
# Composition of conjugates and of mates along composition isomorphisms

This file contains three formal statements on the compatibility of mates and conjugates with
composition isomorphisms of the "horizontal" functors (e.g. extensions of scalars along `a`, `b`
and `c = a ≫ b`).

* `CategoryTheory.Adjunction.conjugateIsoEquiv_symm_hom_app_eq_comp`: let `Pᵢ ⊣ Qᵢ` be three
  adjunctions (e.g. extension by zero and restriction to an open, over three coefficient rings),
  `L ⊣ R` adjunctions on each side (extension and restriction of scalars along `a`, `b`, `c`),
  and `e : Q ⋙ R ≅ R ⋙ Q` isomorphisms of right adjoints. If `e_c` is the composite of `e_a` and
  `e_b` up to composition isomorphisms `κ : R_b ⋙ R_a ≅ R_c`, then the conjugate
  `P ⋙ L_c ≅ L_c ⋙ P` of `e_c` is the composite of the conjugates of `e_a` and `e_b`, up to the
  conjugates `θ : L_c ≅ L_a ⋙ L_b` of `κ`. This is the conjugate counterpart of
  `CategoryTheory.Adjunction.pushHomOfComapIso_app_eq_comp`.
* `CategoryTheory.compCoherence_of_mateEquiv_app_comp`: the converse of
  `CategoryTheory.mateEquiv_app_comp_of_compCoherence`: 2-squares of left adjoints are compatible
  with composition isomorphisms as soon as their mates are.
* `CategoryTheory.mateEquiv_inv_app_comp_of_hom_app_comp`: for *isomorphisms*
  `e : L ⋙ H ≅ G ⋙ L'` of left adjoints (e.g. the comparisons `Rf_! ⋙ T ≅ T ⋙ Rf_!`), if the `e`
  are transitive with respect to composition isomorphisms of the horizontal functors, then so
  are the right adjoint comparisons `R ⋙ G ⟶ H ⋙ R'` defined as the mates of their inverses
  (e.g. the comparisons `f^! ⋙ T ⟶ T ⋙ f^!`).
-/

@[expose] public section

open CategoryTheory Functor TwoSquare

namespace CategoryTheory

namespace Adjunction

section Conjugate

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [Category* X₁] [Category* X₂] [Category* X₃]
  [Category* Y₁] [Category* Y₂] [Category* Y₃]
  {LXa : X₁ ⥤ X₂} {RXa : X₂ ⥤ X₁} (adjXa : LXa ⊣ RXa)
  {LXb : X₂ ⥤ X₃} {RXb : X₃ ⥤ X₂} (adjXb : LXb ⊣ RXb)
  {LXc : X₁ ⥤ X₃} {RXc : X₃ ⥤ X₁} (adjXc : LXc ⊣ RXc)
  {LYa : Y₁ ⥤ Y₂} {RYa : Y₂ ⥤ Y₁} (adjYa : LYa ⊣ RYa)
  {LYb : Y₂ ⥤ Y₃} {RYb : Y₃ ⥤ Y₂} (adjYb : LYb ⊣ RYb)
  {LYc : Y₁ ⥤ Y₃} {RYc : Y₃ ⥤ Y₁} (adjYc : LYc ⊣ RYc)
  {P₁ : Y₁ ⥤ X₁} {Q₁ : X₁ ⥤ Y₁} (adj₁ : P₁ ⊣ Q₁)
  {P₂ : Y₂ ⥤ X₂} {Q₂ : X₂ ⥤ Y₂} (adj₂ : P₂ ⊣ Q₂)
  {P₃ : Y₃ ⥤ X₃} {Q₃ : X₃ ⥤ Y₃} (adj₃ : P₃ ⊣ Q₃)
  (ea : Q₂ ⋙ RYa ≅ RXa ⋙ Q₁) (eb : Q₃ ⋙ RYb ≅ RXb ⋙ Q₂) (ec : Q₃ ⋙ RYc ≅ RXc ⋙ Q₁)
  (κX : RXb ⋙ RXa ≅ RXc) (κY : RYb ⋙ RYa ≅ RYc)

/-- **Composition of conjugates.** If `e_c : Q₃ ⋙ R_c ≅ R_c ⋙ Q₁` is the composite of `e_a` and
`e_b` up to the composition isomorphisms `κ : R_b ⋙ R_a ≅ R_c` of the right adjoints, then the
conjugate `P₁ ⋙ L_c ≅ L_c ⋙ P₃` of `e_c` is the composite of the conjugates of `e_a` and `e_b`,
up to the conjugates `θ : L_c ≅ L_a ⋙ L_b` of `κ`. -/
theorem conjugateIsoEquiv_symm_hom_app_eq_comp
    (h : ∀ K, ec.hom.app K = κY.inv.app (Q₃.obj K) ≫ RYa.map (eb.hom.app K) ≫
      ea.hom.app (RXb.obj K) ≫ Q₁.map (κX.hom.app K)) (K : Y₁) :
    ((conjugateIsoEquiv (adjYc.comp adj₃) (adj₁.comp adjXc)).symm ec).hom.app K =
      ((conjugateIsoEquiv (adjXa.comp adjXb) adjXc).symm κX).hom.app (P₁.obj K) ≫
        LXb.map (((conjugateIsoEquiv (adjYa.comp adj₂) (adj₁.comp adjXa)).symm ea).hom.app K) ≫
        ((conjugateIsoEquiv (adjYb.comp adj₃) (adj₂.comp adjXb)).symm eb).hom.app (LYa.obj K) ≫
        P₃.map (((conjugateIsoEquiv (adjYa.comp adjYb) adjYc).symm κY).inv.app K) := by
  set θX := (conjugateIsoEquiv (adjXa.comp adjXb) adjXc).symm κX
  set θY := (conjugateIsoEquiv (adjYa.comp adjYb) adjYc).symm κY
  set ca := (conjugateIsoEquiv (adjYa.comp adj₂) (adj₁.comp adjXa)).symm ea
  set cb := (conjugateIsoEquiv (adjYb.comp adj₃) (adj₂.comp adjXb)).symm eb
  have hθX : conjugateEquiv (adjXa.comp adjXb) adjXc θX.hom = κX.hom := by
    simp [θX, conjugateIsoEquiv_symm_apply_hom]
  have hθY : conjugateEquiv adjYc (adjYa.comp adjYb) θY.inv = κY.inv := by
    simp [θY, conjugateIsoEquiv_symm_apply_inv]
  have hca : conjugateEquiv (adjYa.comp adj₂) (adj₁.comp adjXa) ca.hom = ea.hom := by
    simp [ca, conjugateIsoEquiv_symm_apply_hom]
  have hcb : conjugateEquiv (adjYb.comp adj₃) (adj₂.comp adjXb) cb.hom = eb.hom := by
    simp [cb, conjugateIsoEquiv_symm_apply_hom]
  let τ : P₁ ⋙ LXc ⟶ LYc ⋙ P₃ :=
    Functor.whiskerLeft P₁ θX.hom ≫ (Functor.associator P₁ LXa LXb).inv ≫
      Functor.whiskerRight ca.hom LXb ≫ (Functor.associator LYa P₂ LXb).hom ≫
      Functor.whiskerLeft LYa cb.hom ≫ (Functor.associator LYa LYb P₃).inv ≫
      Functor.whiskerRight θY.inv P₃
  have hassoc₁ : conjugateEquiv ((adj₁.comp adjXa).comp adjXb) (adj₁.comp (adjXa.comp adjXb))
      (Functor.associator P₁ LXa LXb).inv = (Functor.associator RXb RXa Q₁).inv := by
    have e := conjugateEquiv_comp (adj₁.comp (adjXa.comp adjXb)) ((adj₁.comp adjXa).comp adjXb)
      (adj₁.comp (adjXa.comp adjXb)) (Functor.associator P₁ LXa LXb).hom
      (Functor.associator P₁ LXa LXb).inv
    rw [conjugateEquiv_associator_hom, Iso.inv_hom_id, conjugateEquiv_id] at e
    exact (Iso.hom_comp_eq_id _).1 e
  have hassoc₂ : conjugateEquiv (adjYa.comp (adj₂.comp adjXb)) ((adjYa.comp adj₂).comp adjXb)
      (Functor.associator LYa P₂ LXb).hom = (Functor.associator RXb Q₂ RYa).hom :=
    conjugateEquiv_associator_hom _ _ _
  have hassoc₃ : conjugateEquiv ((adjYa.comp adjYb).comp adj₃) (adjYa.comp (adjYb.comp adj₃))
      (Functor.associator LYa LYb P₃).inv = (Functor.associator Q₃ RYb RYa).inv := by
    have e := conjugateEquiv_comp (adjYa.comp (adjYb.comp adj₃)) ((adjYa.comp adjYb).comp adj₃)
      (adjYa.comp (adjYb.comp adj₃)) (Functor.associator LYa LYb P₃).hom
      (Functor.associator LYa LYb P₃).inv
    rw [conjugateEquiv_associator_hom, Iso.inv_hom_id, conjugateEquiv_id] at e
    exact (Iso.hom_comp_eq_id _).1 e
  have key : conjugateEquiv (adjYc.comp adj₃) (adj₁.comp adjXc) τ = ec.hom := by
    simp only [τ]
    rw [← conjugateEquiv_comp (adjYc.comp adj₃) (adj₁.comp (adjXa.comp adjXb))
        (adj₁.comp adjXc),
      ← conjugateEquiv_comp (adjYc.comp adj₃) ((adj₁.comp adjXa).comp adjXb)
        (adj₁.comp (adjXa.comp adjXb)),
      ← conjugateEquiv_comp (adjYc.comp adj₃) ((adjYa.comp adj₂).comp adjXb)
        ((adj₁.comp adjXa).comp adjXb),
      ← conjugateEquiv_comp (adjYc.comp adj₃) (adjYa.comp (adj₂.comp adjXb))
        ((adjYa.comp adj₂).comp adjXb),
      ← conjugateEquiv_comp (adjYc.comp adj₃) (adjYa.comp (adjYb.comp adj₃))
        (adjYa.comp (adj₂.comp adjXb)),
      ← conjugateEquiv_comp (adjYc.comp adj₃) ((adjYa.comp adjYb).comp adj₃)
        (adjYa.comp (adjYb.comp adj₃))]
    simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, hassoc₁, hassoc₂,
      hassoc₃, hθX, hθY, hca, hcb]
    ext X
    simp [h]
  have hτ : ((conjugateIsoEquiv (adjYc.comp adj₃) (adj₁.comp adjXc)).symm ec).hom = τ := by
    rw [conjugateIsoEquiv_symm_apply_hom, ← key, Equiv.symm_apply_apply]
  rw [hτ]
  simp [τ]

end Conjugate

end Adjunction

section CompCoherence

variable {AZ AY AX BZ BY BX : Type*} [Category* AZ] [Category* AY] [Category* AX]
  [Category* BZ] [Category* BY] [Category* BX]
  {LZ : AZ ⥤ BZ} {RZ : BZ ⥤ AZ} {LY : AY ⥤ BY} {RY : BY ⥤ AY} {LX : AX ⥤ BX} {RX : BX ⥤ AX}
  {Gq : AZ ⥤ AY} {Gp : AY ⥤ AX} {Gpq : AZ ⥤ AX} {Hq : BZ ⥤ BY} {Hp : BY ⥤ BX} {Hpq : BZ ⥤ BX}
  (adjZ : LZ ⊣ RZ) (adjY : LY ⊣ RY) (adjX : LX ⊣ RX)

/-- **Converse of `mateEquiv_app_comp_of_compCoherence`.** If the mates `R ⋙ G ⟶ H ⋙ R` of
2-squares of left adjoints are compatible with composition isomorphisms `c_G` and `c_H`, then so
are the 2-squares themselves. -/
lemma compCoherence_of_mateEquiv_app_comp
    (cG : Gpq ≅ Gq ⋙ Gp) (cH : Hpq ≅ Hq ⋙ Hp) (aq : TwoSquare Gq LZ LY Hq)
    (ap : TwoSquare Gp LY LX Hp) (apq : TwoSquare Gpq LZ LX Hpq)
    (h : ∀ K, (mateEquiv adjZ adjX apq).natTrans.app K ≫ RX.map (cH.hom.app K) =
      cG.hom.app (RZ.obj K) ≫ Gp.map ((mateEquiv adjZ adjY aq).natTrans.app K) ≫
        (mateEquiv adjY adjX ap).natTrans.app (Hq.obj K)) (M : AZ) :
    apq.natTrans.app M ≫ cH.hom.app (LZ.obj M) =
      LX.map (cG.hom.app M) ≫ ap.natTrans.app (Gq.obj M) ≫ Hp.map (aq.natTrans.app M) := by
  have key : (mateEquiv adjZ adjX
      (TwoSquare.mk _ _ _ _ (apq.natTrans ≫ Functor.whiskerLeft LZ cH.hom))).natTrans =
      (mateEquiv adjZ adjX (TwoSquare.mk _ _ _ _
        (Functor.whiskerRight cG.hom LX ≫ (aq ≫ₕ ap).natTrans))).natTrans := by
    rw [mateEquiv_comp_whiskerLeft, mateEquiv_whiskerRight_comp, mateEquiv_vcomp adjZ adjY adjX]
    ext K
    simpa [TwoSquare.vComp] using h K
  have key' := congr_arg (fun s : TwoSquare Gpq LZ LX (Hq ⋙ Hp) => s.natTrans.app M)
    ((mateEquiv adjZ adjX).injective key)
  simpa [TwoSquare.hComp] using key'

/-- **Transitivity of right adjoint comparisons defined as mates.** Let
`e : L ⋙ H ≅ G ⋙ L'` be isomorphisms of left adjoints (e.g. the comparisons
`Rf_! ⋙ T ≅ T ⋙ Rf_!` for coefficient changes `q`, `p` and `pq`), transitive with respect to
composition isomorphisms `c_G : G_{pq} ≅ G_q ⋙ G_p` and `c_H : H_{pq} ≅ H_q ⋙ H_p` of the
horizontal functors (hypothesis `h`). Then the right adjoint comparisons `R ⋙ G ⟶ H ⋙ R'`
defined as the mates of the inverses `e⁻¹` (e.g. the comparisons `f^! ⋙ T ⟶ T ⋙ f^!`) are
transitive with respect to the same composition isomorphisms. -/
lemma mateEquiv_inv_app_comp_of_hom_app_comp (cG : Gpq ≅ Gq ⋙ Gp) (cH : Hpq ≅ Hq ⋙ Hp)
    (eq : LZ ⋙ Hq ≅ Gq ⋙ LY) (ep : LY ⋙ Hp ≅ Gp ⋙ LX) (epq : LZ ⋙ Hpq ≅ Gpq ⋙ LX)
    (h : ∀ M, epq.hom.app M = cH.hom.app (LZ.obj M) ≫ Hp.map (eq.hom.app M) ≫
      ep.hom.app (Gq.obj M) ≫ LX.map (cG.inv.app M)) (K : BZ) :
    (mateEquiv adjZ adjX (TwoSquare.mk _ _ _ _ epq.inv)).natTrans.app K =
      cG.hom.app (RZ.obj K) ≫
        Gp.map ((mateEquiv adjZ adjY (TwoSquare.mk _ _ _ _ eq.inv)).natTrans.app K) ≫
        (mateEquiv adjY adjX (TwoSquare.mk _ _ _ _ ep.inv)).natTrans.app (Hq.obj K) ≫
        RX.map (cH.inv.app K) := by
  have hc := mateEquiv_app_comp_of_compCoherence adjZ adjY adjX cG cH
    (TwoSquare.mk _ _ _ _ eq.inv) (TwoSquare.mk _ _ _ _ ep.inv)
    (TwoSquare.mk _ _ _ _ epq.inv) (fun M => by
      dsimp only [TwoSquare.natTrans, TwoSquare.mk]
      rw [← cancel_epi (epq.hom.app M), Iso.hom_inv_id_app_assoc, h M]
      simp only [Functor.comp_obj, Category.assoc, ← LX.map_comp_assoc, Iso.inv_hom_id_app,
        Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc, ← Hp.map_comp,
        Iso.hom_inv_id_app, Category.comp_id]) K
  rw [← cancel_mono (RX.map (cH.hom.app K)), hc]
  simp



/-- The form of `mateEquiv_inv_app_comp_of_hom_app_comp` for natural transformations of left
adjoints which are isomorphisms. -/
lemma mateEquiv_inv_app_comp_of_app_comp (cG : Gpq ≅ Gq ⋙ Gp) (cH : Hpq ≅ Hq ⋙ Hp)
    (αq : LZ ⋙ Hq ⟶ Gq ⋙ LY) (αp : LY ⋙ Hp ⟶ Gp ⋙ LX) (αpq : LZ ⋙ Hpq ⟶ Gpq ⋙ LX) [IsIso αq]
    [IsIso αp] [IsIso αpq]
    (h : ∀ M, αpq.app M = cH.hom.app (LZ.obj M) ≫ Hp.map (αq.app M) ≫
      αp.app (Gq.obj M) ≫ LX.map (cG.inv.app M)) (K : BZ) :
    (mateEquiv adjZ adjX (TwoSquare.mk _ _ _ _ (inv αpq))).natTrans.app K =
      cG.hom.app (RZ.obj K) ≫
        Gp.map ((mateEquiv adjZ adjY (TwoSquare.mk _ _ _ _ (inv αq))).natTrans.app K) ≫
        (mateEquiv adjY adjX (TwoSquare.mk _ _ _ _ (inv αp))).natTrans.app (Hq.obj K) ≫
        RX.map (cH.inv.app K) :=
  mateEquiv_inv_app_comp_of_hom_app_comp adjZ adjY adjX cG cH (asIso αq) (asIso αp) (asIso αpq)
    h K
end CompCoherence

section VerticalComp

variable {AX AY AZ BX BY BZ : Type*} [Category* AX] [Category* AY] [Category* AZ]
  [Category* BX] [Category* BY] [Category* BZ]
  {Lf : AX ⥤ AY} {Rf : AY ⥤ AX} {Lg : AY ⥤ AZ} {Rg : AZ ⥤ AY} {Lgf : AX ⥤ AZ} {Rgf : AZ ⥤ AX}
  {Lfₜ : BX ⥤ BY} {Rfₜ : BY ⥤ BX} {Lgₜ : BY ⥤ BZ} {Rgₜ : BZ ⥤ BY} {Lgfₜ : BX ⥤ BZ}
  {Rgfₜ : BZ ⥤ BX} {TX : AX ⥤ BX} {TY : AY ⥤ BY} {TZ : AZ ⥤ BZ}
  (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjgf : Lgf ⊣ Rgf) (adjfₜ : Lfₜ ⊣ Rfₜ) (adjgₜ : Lgₜ ⊣ Rgₜ)
  (adjgfₜ : Lgfₜ ⊣ Rgfₜ)

/-- **Right adjoint comparisons defined as mates are compatible with composition.** Let
`ι : L ⋙ T ≅ T ⋙ Lₜ` be commutation isomorphisms of left adjoints (e.g. the comparisons
`Rf_! ⋙ T ≅ T ⋙ Rf_!` for morphisms `f`, `g` and `g ∘ f`), compatible with composition
isomorphisms `e : L_{gf} ≅ L_f ⋙ L_g` and `eₜ` (hypothesis `h`, e.g. with `R(gf)_! ≅ Rg_! Rf_!`).
Then the right adjoint comparisons `ρ : R ⋙ T ⟶ T ⋙ Rₜ` defined as the mates of the inverses
`ι⁻¹` (e.g. the comparisons `f^! ⋙ T ⟶ T ⋙ f^!`) are compatible with the conjugate composition
isomorphisms `R_{gf} ≅ R_g ⋙ R_f` (e.g. `(gf)^! ≅ f^! g^!`). -/
lemma mateEquiv_inv_app_comp_conjugateIsoEquiv (ιf : Lf ⋙ TY ≅ TX ⋙ Lfₜ)
    (ιg : Lg ⋙ TZ ≅ TY ⋙ Lgₜ) (ιgf : Lgf ⋙ TZ ≅ TX ⋙ Lgfₜ) (e : Lgf ≅ Lf ⋙ Lg)
    (eₜ : Lgfₜ ≅ Lfₜ ⋙ Lgₜ)
    (h : NatTrans.SquareCompatible ιgf (Functor.pasteSquareIso ιf ιg) e.hom eₜ.hom) (K : AZ) :
    TX.map ((conjugateIsoEquiv adjgf (adjf.comp adjg) e.symm).hom.app K) ≫
        (mateEquiv adjf adjfₜ (TwoSquare.mk _ _ _ _ ιf.inv)).natTrans.app (Rg.obj K) ≫
        Rfₜ.map ((mateEquiv adjg adjgₜ (TwoSquare.mk _ _ _ _ ιg.inv)).natTrans.app K) =
      (mateEquiv adjgf adjgfₜ (TwoSquare.mk _ _ _ _ ιgf.inv)).natTrans.app K ≫
        (conjugateIsoEquiv adjgfₜ (adjfₜ.comp adjgₜ) eₜ.symm).hom.app (TZ.obj K) := by
  have hS : TwoSquare.mk _ _ _ _ ιgf.inv =
      (((TwoSquare.mk _ _ _ _ ιf.inv) ≫ᵥ (TwoSquare.mk _ _ _ _ ιg.inv)).whiskerLeft
        e.inv).whiskerRight eₜ.hom := by
    ext M
    have hM := h M
    simp only [Functor.pasteSquareIso_hom_app] at hM
    dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
      TwoSquare.natTrans, TwoSquare.mk]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Functor.comp_obj]
    rw [← cancel_epi (ιgf.hom.app M), Iso.hom_inv_id_app, ← cancel_mono (TZ.map (e.hom.app M)),
      Category.id_comp, Category.assoc, Category.assoc, Category.assoc, ← TZ.map_comp,
      Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← reassoc_of% hM]
    simp
  have key := congr_arg (mateEquiv adjgf adjgfₜ) hS
  rw [mateEquiv_conjugateEquiv_vcomp adjgf (adjfₜ.comp adjgₜ) adjgfₜ,
    conjugateEquiv_mateEquiv_vcomp adjgf (adjf.comp adjg) (adjfₜ.comp adjgₜ),
    mateEquiv_hcomp] at key
  have keyK := NatTrans.congr_app (congr_arg TwoSquare.natTrans key) K
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    TwoSquare.natTrans, TwoSquare.mk] at keyK
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.comp_obj] at keyK
  rw [keyK, conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_hom]
  have hc : ((conjugateEquiv (adjfₜ.comp adjgₜ) adjgfₜ) eₜ.hom).app (TZ.obj K) ≫
      ((conjugateEquiv adjgfₜ (adjfₜ.comp adjgₜ)) eₜ.inv).app (TZ.obj K) = 𝟙 _ := by
    rw [← NatTrans.comp_app, conjugateEquiv_comp, Iso.inv_hom_id,
      conjugateEquiv_id, NatTrans.id_app]
  simp only [Iso.symm_hom, Category.assoc, hc]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]

end VerticalComp

end CategoryTheory
