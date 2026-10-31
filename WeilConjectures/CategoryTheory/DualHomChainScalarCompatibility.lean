/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Opposites

/-! # Scalar compatibility of the four duality Hom bijections

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
lem-coef-finite-exceptional.proof.md, paragraphs 1--2, transposition under the
four displayed Hom bijections (blueprint: lem-sf-dual-hom-chain-scalar-compatibility).

The helpers construct the specified chain and comparison from actual functor maps.
-/

@[expose] public section

set_option autoImplicit false

universe uX uY vX vY uX0 uX1 uY0 uY1 vX0 vX1 vY0 vY1

open Opposite

namespace CategoryTheory

/-- The four-arrow chain whose inverse is Phi: duality, ordinary adjunction,
exchange, then duality. The first arrow is delta_V followed by D(z); the last is
 delta_A followed by D(w) followed by delta_L inverse, in diagrammatic order.
Source: latest blueprint, lem-coef-finite-exceptional.proof.md, paragraph 1
(blueprint: lem-sf-dual-hom-chain-scalar-compatibility). -/
def dualHomChain
    {X : Type uX} {Y : Type uY} [Category.{vX} X] [Category.{vY} Y]
    (DX : Xᵒᵖ ≌ X) (DY : Yᵒᵖ ≌ Y)
    (δX : 𝟭 X ≅ DX.functor.rightOp ⋙ DX.functor)
    (δY : 𝟭 Y ≅ DY.functor.rightOp ⋙ DY.functor)
    (F : X ⥤ Y) (U : Y ⥤ X) (R : X ⥤ Y) (adj : U ⊣ R)
    (E : DX.functor ⋙ R ≅ F.op ⋙ DY.functor) (K : X) (L : Y) :
    (K ⟶ DX.functor.obj (op (U.obj (DY.functor.obj (op L))))) ≃ (F.obj K ⟶ L) :=
  (((opEquiv _ _).symm.trans DX.fullyFaithfulFunctor.homEquiv).trans
    (Iso.homCongr (δX.app (U.obj (DY.functor.obj (op L)))).symm (Iso.refl _))).trans
    ((adj.homEquiv _ _).trans
      ((Iso.homCongr (Iso.refl _) (E.app (op K))).trans
        (((opEquiv _ _).symm.trans DY.fullyFaithfulFunctor.homEquiv).trans
          (Iso.homCongr (δY.app (F.obj K)).symm (δY.app L).symm))))

/-- The prescribed h_L: d_X at U_0 D_Y, followed by D_X of the inverse of
 t_L = p at D_Y followed by U_1(d_Y). This is a constructed isomorphism.
Source: latest blueprint, lem-coef-finite-exceptional.proof.md, paragraph 2,
the two coherent duality comparisons and ordinary pullback comparison
(blueprint: lem-sf-dual-hom-chain-scalar-compatibility). -/
def dualHomChainScalarComparison
    {X0 : Type uX0} {X1 : Type uX1} {Y0 : Type uY0} {Y1 : Type uY1}
    [Category.{vX0} X0] [Category.{vX1} X1]
    [Category.{vY0} Y0] [Category.{vY1} Y1]
    (DX0 : X0ᵒᵖ ≌ X0) (DX1 : X1ᵒᵖ ≌ X1)
    (DY0 : Y0ᵒᵖ ≌ Y0) (DY1 : Y1ᵒᵖ ≌ Y1)
    (QX : X0 ⥤ X1) (QY : Y0 ⥤ Y1) (U0 : Y0 ⥤ X0) (U1 : Y1 ⥤ X1)
    (p : U0 ⋙ QX ≅ QY ⋙ U1)
    (dX : DX0.functor ⋙ QX ≅ QX.op ⋙ DX1.functor)
    (dY : DY0.functor ⋙ QY ≅ QY.op ⋙ DY1.functor) (L : Y0) :
    QX.obj (DX0.functor.obj (op (U0.obj (DY0.functor.obj (op L))))) ≅
      DX1.functor.obj (op (U1.obj (DY1.functor.obj (op (QY.obj L))))) :=
  dX.app (op (U0.obj (DY0.functor.obj (op L)))) ≪≫
    DX1.functor.mapIso
      ((p.app (DY0.functor.obj (op L)) ≪≫ U1.mapIso (dY.app (op L))).symm.op)

/-- The four duality Hom bijections commute with the change functors on actual morphisms.
Source: latest blueprint, lem-coef-finite-exceptional.proof.md, paragraph 2,
"To identify its adjunction maps, transpose under the displayed bijections"
(blueprint: lem-sf-dual-hom-chain-scalar-compatibility).

Proof plan from the node, in diagrammatic composition order:
1. Write Psi for dualHomChain and Phi for its inverse. For z_0 put
   b_0 = delta_V followed by D_X(z_0), r_0 = adj_0.homEquiv(b_0),
   w_0 = r_0 followed by E_0, and a_0 = Psi_0(z_0). The inverse adjunction
   formula is U_0(r_0) followed by epsilon_0 (Stacks 0037,
   lem-weil-pbc-adjunction-of-natural-bijection).
2. Set z_1 = Q_X(z_0) followed by h_L. Expand h_L, use delta_1 naturality,
   the biduality comparison at V, and d_X naturality at z_0. This gives
   b_1 = t_L inverse followed by Q_X(b_0) followed by d_X at K.
3. Set r' = d_Y at L inverse followed by Q_Y(r_0), c at D_X K,
   and R_1(d_X at K). Apply the inverse adjunction formula, multiply by t_L,
   use counit naturality, p naturality and the assumed counit square.
   Cancel t_L and invert the Hom bijection to get r_1 = r'.
4. Substitute r_1 and apply the assumed exchange square. This gives w_1 as
   d_Y at L inverse, Q_Y(w_0), d_Y at F_0 K, then D_Y(q_K inverse).
5. Expand the final duality arrow contravariantly. Delta naturality at q_K inverse,
   the biduality square at F_0 K and d_Y naturality at w_0 replace its middle factors.
6. The biduality square at L cancels the remaining d_Y factors, giving
   Psi_1(z_1) = q_K inverse followed by Q_Y(Psi_0(z_0)).
7. Take z_0 = Phi_0(a) and apply Phi_1. No Hom set is tensored and neither
   Q_X nor Q_Y is assumed full or faithful. -/
theorem dualHomChain_scalar_compatibility
    {X0 : Type uX0} {X1 : Type uX1} {Y0 : Type uY0} {Y1 : Type uY1}
    [Category.{vX0} X0] [Category.{vX1} X1]
    [Category.{vY0} Y0] [Category.{vY1} Y1]
    (DX0 : X0ᵒᵖ ≌ X0) (DX1 : X1ᵒᵖ ≌ X1)
    (DY0 : Y0ᵒᵖ ≌ Y0) (DY1 : Y1ᵒᵖ ≌ Y1)
    (δX0 : 𝟭 X0 ≅ DX0.functor.rightOp ⋙ DX0.functor)
    (δX1 : 𝟭 X1 ≅ DX1.functor.rightOp ⋙ DX1.functor)
    (δY0 : 𝟭 Y0 ≅ DY0.functor.rightOp ⋙ DY0.functor)
    (δY1 : 𝟭 Y1 ≅ DY1.functor.rightOp ⋙ DY1.functor)
    (hδX0 : ∀ M : X0, (δX0.hom.app (DX0.functor.obj (op M))) ≫
      DX0.functor.map (δX0.hom.app M).op = 𝟙 _)
    (hδX1 : ∀ M : X1, (δX1.hom.app (DX1.functor.obj (op M))) ≫
      DX1.functor.map (δX1.hom.app M).op = 𝟙 _)
    (hδY0 : ∀ M : Y0, (δY0.hom.app (DY0.functor.obj (op M))) ≫
      DY0.functor.map (δY0.hom.app M).op = 𝟙 _)
    (hδY1 : ∀ M : Y1, (δY1.hom.app (DY1.functor.obj (op M))) ≫
      DY1.functor.map (δY1.hom.app M).op = 𝟙 _)
    (F0 : X0 ⥤ Y0) (F1 : X1 ⥤ Y1)
    (U0 : Y0 ⥤ X0) (U1 : Y1 ⥤ X1) (R0 : X0 ⥤ Y0) (R1 : X1 ⥤ Y1)
    (adj0 : U0 ⊣ R0) (adj1 : U1 ⊣ R1)
    (E0 : DX0.functor ⋙ R0 ≅ F0.op ⋙ DY0.functor)
    (E1 : DX1.functor ⋙ R1 ≅ F1.op ⋙ DY1.functor)
    (QX : X0 ⥤ X1) (QY : Y0 ⥤ Y1)
    (q : F0 ⋙ QY ≅ QX ⋙ F1) (p : U0 ⋙ QX ≅ QY ⋙ U1)
    (c : R0 ⋙ QY ≅ QX ⋙ R1)
    (dX : DX0.functor ⋙ QX ≅ QX.op ⋙ DX1.functor)
    (dY : DY0.functor ⋙ QY ≅ QY.op ⋙ DY1.functor)
    (hX : ∀ M : X0, QX.map (δX0.hom.app M) ≫
      dX.hom.app (op (DX0.functor.obj (op M))) =
        δX1.hom.app (QX.obj M) ≫ DX1.functor.map (dX.hom.app (op M)).op)
    (hY : ∀ M : Y0, QY.map (δY0.hom.app M) ≫
      dY.hom.app (op (DY0.functor.obj (op M))) =
        δY1.hom.app (QY.obj M) ≫ DY1.functor.map (dY.hom.app (op M)).op)
    (hCounit : ∀ N : X0, p.hom.app (R0.obj N) ≫ U1.map (c.hom.app N) ≫
      adj1.counit.app (QX.obj N) = QX.map (adj0.counit.app N))
    (hExchange : ∀ K : X0, QY.map (E0.hom.app (op K)) ≫ dY.hom.app (op (F0.obj K)) =
      c.hom.app (DX0.functor.obj (op K)) ≫ R1.map (dX.hom.app (op K)) ≫
        E1.hom.app (op (QX.obj K)) ≫ DY1.functor.map (q.hom.app K).op)
    (K : X0) (L : Y0) (a : F0.obj K ⟶ L) :
    QX.map ((dualHomChain DX0 DY0 δX0 δY0 F0 U0 R0 adj0 E0 K L).symm a) ≫
        (dualHomChainScalarComparison DX0 DX1 DY0 DY1 QX QY U0 U1 p dX dY L).hom =
      (dualHomChain DX1 DY1 δX1 δY1 F1 U1 R1 adj1 E1 (QX.obj K) (QY.obj L)).symm
        (q.inv.app K ≫ QY.map a) := by
  have _ := hδX0
  have _ := hδX1
  have _ := hδY0
  have _ := hδY1
  let z0 := (dualHomChain DX0 DY0 δX0 δY0 F0 U0 R0 adj0 E0 K L).symm a
  let V := U0.obj (DY0.functor.obj (op L))
  let t := p.app (DY0.functor.obj (op L)) ≪≫ U1.mapIso (dY.app (op L))
  let z1 := QX.map z0 ≫ dX.hom.app (op V) ≫ DX1.functor.map t.inv.op
  let b0 := δX0.hom.app V ≫ DX0.functor.map z0.op
  let b1 := δX1.hom.app (U1.obj (DY1.functor.obj (op (QY.obj L)))) ≫
    DX1.functor.map z1.op
  -- The first duality transpose uses the biduality comparison at V.
  have hb : b1 = t.inv ≫ QX.map b0 ≫ dX.hom.app (op K) := by
    have hn := δX1.hom.naturality t.inv
    have hd := dX.hom.naturality z0.op
    dsimp at hn hd
    dsimp only [b1, z1, b0]
    simp only [op_comp, Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hn, ← reassoc_of% (hX V), ← hd]
  let r0 := adj0.homEquiv _ _ b0
  let r1 := dY.inv.app (op L) ≫ QY.map r0 ≫
    c.hom.app (DX0.functor.obj (op K)) ≫ R1.map (dX.hom.app (op K))
  -- Compare the adjunction transposes through the inverse counit formula.
  have hr : adj1.homEquiv _ _ b1 = r1 := by
    apply (adj1.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, hb]
    apply (cancel_epi t.hom).mp
    dsimp only [r1]
    simp only [Functor.map_comp, Category.assoc]
    have hn := adj1.counit.naturality (dX.hom.app (op K))
    have hp := p.hom.naturality r0
    dsimp at hn hp
    have hb0 : U0.map r0 ≫ adj0.counit.app _ = b0 :=
      (adj0.homEquiv _ _).symm_apply_apply b0
    rw [hn, t.hom_inv_id_assoc]
    dsimp only [t, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    rw [← U1.map_comp_assoc, Iso.hom_inv_id_app]
    simp only [Functor.comp_obj, Functor.map_id, Category.id_comp]
    rw [← reassoc_of% hp, reassoc_of% (hCounit (DX0.functor.obj (op K))),
      ← QX.map_comp_assoc, hb0]
  let w0 := r0 ≫ E0.hom.app (op K)
  let w1 := r1 ≫ E1.hom.app (op (QX.obj K))
  -- The exchange square compares the third arrows.
  have hw : w1 = dY.inv.app (op L) ≫ QY.map w0 ≫
      dY.hom.app (op (F0.obj K)) ≫ DY1.functor.map (q.inv.app K).op := by
    dsimp only [w1, r1, w0]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hExchange K)]
    simp only [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id]
    simp
  -- Cancel the comparison at L in the final duality transpose.
  have hlast : dY.hom.app (op (DY0.functor.obj (op L))) ≫
      DY1.functor.map (dY.inv.app (op L)).op ≫ δY1.inv.app (QY.obj L) =
      QY.map (δY0.inv.app L) := by
    apply (cancel_epi (QY.map (δY0.hom.app L))).mp
    rw [← Category.assoc, hY L]
    simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
      ← op_comp, Iso.inv_hom_id_app, Iso.hom_inv_id_app, op_id]
    simp
  have ha : δY1.hom.app (F1.obj (QX.obj K)) ≫ DY1.functor.map w1.op ≫
      δY1.inv.app (QY.obj L) = q.inv.app K ≫
      QY.map (δY0.hom.app (F0.obj K) ≫ DY0.functor.map w0.op ≫ δY0.inv.app L) := by
    have hn := δY1.hom.naturality (q.inv.app K)
    have hd := dY.hom.naturality w0.op
    dsimp at hn hd
    rw [hw]
    simp only [op_comp, Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hn, ← reassoc_of% (hY (F0.obj K)),
      ← reassoc_of% hd, hlast]
  have ha0 : δY0.hom.app (F0.obj K) ≫ DY0.functor.map w0.op ≫
      δY0.inv.app L = a := by
    have he0 :=
      (dualHomChain DX0 DY0 δX0 δY0 F0 U0 R0 adj0 E0 K L).apply_symm_apply a
    change dualHomChain DX0 DY0 δX0 δY0 F0 U0 R0 adj0 E0 K L z0 = a at he0
    dsimp [dualHomChain, Iso.homCongr, opEquiv, Functor.FullyFaithful.homEquiv] at he0
    simpa only [Category.comp_id, Category.id_comp, op_comp, w0, r0, b0] using he0
  apply (dualHomChain DX1 DY1 δX1 δY1 F1 U1 R1 adj1 E1
    (QX.obj K) (QY.obj L)).injective
  rw [Equiv.apply_symm_apply]
  change dualHomChain DX1 DY1 δX1 δY1 F1 U1 R1 adj1 E1
    (QX.obj K) (QY.obj L) z1 = q.inv.app K ≫ QY.map a
  have he1 : dualHomChain DX1 DY1 δX1 δY1 F1 U1 R1 adj1 E1
      (QX.obj K) (QY.obj L) z1 = δY1.hom.app (F1.obj (QX.obj K)) ≫
      DY1.functor.map ((adj1.homEquiv _ _ b1) ≫ E1.hom.app (op (QX.obj K))).op ≫
        δY1.inv.app (QY.obj L) := by
    simp [dualHomChain, b1, opEquiv, Category.assoc]
  rw [he1, hr]
  exact ha.trans (by rw [ha0])

end CategoryTheory
