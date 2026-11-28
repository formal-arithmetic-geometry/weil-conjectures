/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic

/-! # Invertibility of transposed representatives in pair categories

In the pair category of a stage system, a morphism represented by an isomorphism is an
isomorphism. We use this to show that a transposition normalized by stage-level
transpositions sends a composite represented at a finite stage to an isomorphism, as soon as
the corresponding stage-level transpose is an isomorphism.

## Main statements

* `CategoryTheory.StageSystem.PairCategory.isIso_mkHom`: a morphism represented by an
  isomorphism is an isomorphism.
* `CategoryTheory.StageSystem.PairCategory.isIso_transpose_of_representatives`: the
  pair-category computation behind invertibility of the common-stage internal Hom
  comparison.
-/

@[expose] public section

namespace CategoryTheory.StageSystem.PairCategory

variable {I : Type*} [Preorder I] [IsDirectedOrder I]

omit [IsDirectedOrder I] in
/-- Equal objects of the pair category have equal transports to a common stage. -/
theorem toStage_congr {C : I → Type*} [∀ i, Category (C i)] {S : StageSystem C}
    {X Y : S.PairCategory} (e : X = Y) {n : I} (hX : X.stage ≤ n) (hY : Y.stage ≤ n) :
    X.toStage hX = Y.toStage hY := by
  subst e
  rfl

/-- A morphism of the pair category represented by an isomorphism is an isomorphism. -/
theorem isIso_mkHom {C : I → Type*} [∀ i, Category (C i)] {S : StageSystem C}
    {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n) (hY : Y.stage ≤ n)
    (u : X.toStage hX ⟶ Y.toStage hY) [IsIso u] : IsIso (mkHom n hX hY u) :=
  ⟨⟨mkHom n hY hX (inv u), by rw [mkHom_comp_mkHom, IsIso.hom_inv_id, ← id_eq_mkHom],
    by rw [mkHom_comp_mkHom, IsIso.inv_hom_id, ← id_eq_mkHom]⟩⟩

/-- Let `t` be a transposition on the target pair category whose inverse is given on
representatives at the stage `n` by a stage-level inverse transposition `r.symm`, conjugated
by the isomorphisms `d` and `c`. Let `ev` be the inverse transpose of an identity on the
source side, similarly normalized, and let `G` and `μ` be represented at `n` by `RP` and by
`p`. Then `t (μ⁻¹ ≫ G ev)` is an isomorphism as soon as the stage-level transpose of the
corresponding representative is. -/
theorem isIso_transpose_of_representatives
    {CY CX : I → Type*} [∀ i, Category (CY i)] [∀ i, Category (CX i)]
    {SY : StageSystem CY} {SX : StageSystem CX} (G : SY.PairCategory ⥤ SX.PairCategory)
    {n : I} {A A' N TY TY' : SY.PairCategory}
    (eA : A = A') (eTY : TY = TY')
    (hA : A.stage ≤ n) (hA' : A'.stage ≤ n) (hTY : TY'.stage ≤ n) (hN : N.stage ≤ n)
    {RHY UY : CY n} (cY : A'.toStage hA' ≅ RHY) (dY : TY'.toStage hTY ≅ UY)
    (rY : (A.toStage hA ⟶ RHY) → (UY ⟶ N.toStage hN))
    (sY : (A ⟶ A) → (TY ⟶ N))
    (hsY : ∀ (ψ : A.toStage hA ⟶ A'.toStage hA') (q : A ⟶ A),
      HEq q (mkHom n hA hA' ψ) → HEq (sY q) (mkHom n hTY hN (dY.hom ≫ rY (ψ ≫ cY.hom))))
    {XH XH' TX TX' TXl GTY GN : SX.PairCategory}
    (eXH : XH = XH') (eTX : TX = TX') (eTXl : TX' = TXl) (eGT : G.obj TY' = GTY)
    (eGN : G.obj N = GN)
    (hXA : (G.obj A).stage ≤ n) (hXH : XH'.stage ≤ n) (hTX : TX'.stage ≤ n)
    (hTXl : TXl.stage ≤ n) (hGT : GTY.stage ≤ n) (hGN : GN.stage ≤ n)
    (hXN : (G.obj N).stage ≤ n)
    {RHX UX : CX n} (cX : XH'.toStage hXH ≅ RHX) (dX : TX'.toStage hTX ≅ UX)
    (rX : (UX ⟶ (G.obj N).toStage hXN) ≃ ((G.obj A).toStage hXA ⟶ RHX))
    (t : (TX ⟶ G.obj N) ≃ (G.obj A ⟶ XH))
    (hsX : ∀ (ψ : (G.obj A).toStage hXA ⟶ XH'.toStage hXH) (q : G.obj A ⟶ XH),
      HEq q (mkHom n hXA hXH ψ) →
        HEq (t.symm q) (mkHom n hTX hXN (dX.hom ≫ rX.symm (ψ ≫ cX.hom))))
    (μ : G.obj TY ≅ TX) (p : GTY.toStage hGT ≅ TXl.toStage hTXl)
    (hμ : HEq μ.hom (mkHom n hGT hTXl p.hom))
    {RP : CY n ⥤ CX n} (pT : GTY.toStage hGT ≅ RP.obj (TY'.toStage hTY))
    (pN : GN.toStage hGN ≅ RP.obj (N.toStage hN))
    (hG : ∀ u : TY'.toStage hTY ⟶ N.toStage hN,
      HEq (G.map (mkHom n hTY hN u)) (mkHom n hGT hGN (pT.hom ≫ RP.map u ≫ pN.inv)))
    (h₁ : TX'.toStage hTX = TXl.toStage hTXl) (h₂ : A.toStage hA = A'.toStage hA')
    (h₃ : GN.toStage hGN = (G.obj N).toStage hXN)
    (hiso : IsIso (rX (dX.inv ≫ eqToHom h₁ ≫ p.inv ≫ pT.hom ≫
      RP.map (dY.hom ≫ rY (eqToHom h₂ ≫ cY.hom)) ≫ pN.inv ≫ eqToHom h₃))) :
    IsIso (t (μ.inv ≫ G.map (sY (𝟙 A)))) := by
  subst eA eTY eXH eTX eTXl eGT eGN
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hiso
  have hev : sY (𝟙 A) = mkHom n hTY hN (dY.hom ≫ rY (𝟙 _ ≫ cY.hom)) :=
    eq_of_heq (hsY _ _ (heq_of_eq (id_eq_mkHom A hA)))
  have hμ' : μ.inv = mkHom n hTXl hGT p.inv := by
    rw [← cancel_epi μ.hom, Iso.hom_inv_id, eq_of_heq hμ, mkHom_comp_mkHom, Iso.hom_inv_id,
      ← id_eq_mkHom]
  have hx : μ.inv ≫ G.map (sY (𝟙 A)) =
      mkHom n hTX hXN (p.inv ≫ pT.hom ≫ RP.map (dY.hom ≫ rY (cY.hom)) ≫ pN.inv) := by
    rw [hev, eq_of_heq (hG _), hμ', mkHom_comp_mkHom, Category.id_comp]
  have ht : t (μ.inv ≫ G.map (sY (𝟙 A))) = mkHom n hXA hXH
      (rX (dX.inv ≫ p.inv ≫ pT.hom ≫ RP.map (dY.hom ≫ rY (cY.hom)) ≫ pN.inv) ≫
        cX.inv) := by
    apply t.symm.injective
    rw [Equiv.symm_apply_apply, eq_of_heq (hsX _ _ HEq.rfl), hx, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  rw [ht]
  exact isIso_mkHom _ _ _

end CategoryTheory.StageSystem.PairCategory
