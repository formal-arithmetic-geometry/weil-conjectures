/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalPairingQuotient
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalTraceQuotient
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionComponents
public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierSignedCalculus

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

end WeilConjectures.FiniteExceptional

namespace WeilConjectures.FiniteExceptional

private theorem conjugate_hom_cancel {C : Type*} [Category C]
    {A B C' D : C} (a : A ≅ B) (b : B ≅ C') (c : D ≅ C') :
    (a ≪≫ b ≪≫ c.symm).hom ≫ c.hom = a.hom ≫ b.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem cancel_natural_comparison {C : Type*} [Category C]
    {X X' Y Y' Z : C} (e : X ≅ X') (a : X ⟶ Y) (b : X' ⟶ Y')
    (k : Y ⟶ Y') (c : Y' ⟶ Z) (d : X' ⟶ Z)
    (hn : a ≫ k = e.hom ≫ b) (h : a ≫ k ≫ c = e.hom ≫ d) :
    b ≫ c = d := by
  apply (cancel_epi e.hom).1
  rw [← reassoc_of% hn]
  exact h

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
  classical
  obtain ⟨aXm⟩ := IntegralHom.reduction_target_exists l E X m
  obtain ⟨aZm⟩ := IntegralHom.reduction_target_exists l E c.Z m
  obtain ⟨aYm⟩ := IntegralHom.reduction_target_exists l E Y m
  obtain ⟨aXn⟩ := IntegralHom.reduction_target_exists l E X n
  obtain ⟨aZn⟩ := IntegralHom.reduction_target_exists l E c.Z n
  obtain ⟨aYn⟩ := IntegralHom.reduction_target_exists l E Y n
  obtain ⟨sXm, _⟩ := IntegralVerdier.presentation_symmetry X _ aXm
  obtain ⟨sXn, _⟩ := IntegralVerdier.presentation_symmetry X _ aXn
  obtain ⟨sYn, _⟩ := IntegralVerdier.presentation_symmetry Y _ aYn
  rw [NatTrans.isIso_iff_isIso_app]
  intro L
  let L' := (Q l E Y h).obj L
  let K := (Q l E X h).obj ((G l E D hl f c m).obj L)
  let k := (dualFormulaIso l E D hl f c n).app L'
  let e := exceptionalQuotientComponent l E D hl f c h L
  let v : K ⟶ (G l E D hl f c n).obj L' := ObjectProperty.homMk e.hom
  have hm := dualFormula_pairing l E D hl f c m aXm aZm aYm sXm L
  have hn := dualFormula_pairing l E D hl f c n aXn aZn aYn sXn L'
  have hs := tracePairing_quotient l E D hl f c h aXm aZm aYm aXn aZn aYn
    sXm sXn (finiteTrace_quotient l E D hl f c h) ((G l E D hl f c m).obj L) L
    ((dualFormulaIso l E D hl f c m).hom.app L)
    ((adjunction l E D hl f c m).counit.app L).hom hm
  have hk : v.hom ≫ k.hom =
      (reduction l E X h).map ((dualFormulaIso l E D hl f c m).hom.app L) ≫
        (formulaQuotientIso l E D hl f h L).hom := by
    exact conjugate_hom_cancel
      ((reduction l E X h).mapIso ((dualFormulaIso l E D hl f c m).app L))
      (formulaQuotientIso l E D hl f h L)
      ((dualFormulaIso l E D hl f c n).app ((Q l E Y h).obj L))
  have hp := tracePairing_precomp l E D f c n aXn aZn aYn sXn K
    ((G l E D hl f c n).obj L') L' v k.hom
  have he :
      (PurCompactSupport.image
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c).map v.hom ≫
        (PurCompactSupport.finiteImageIso l E n c).hom.app
          ((G l E D hl f c n).obj L').obj ≫
        ((adjunction l E D hl f c n).counit.app L').hom =
      (PurCompactSupport.finiteImageIso l E n c).hom.app K.obj ≫
        ((q l E D hl f c h).inv.app ((G l E D hl f c m).obj L)).hom ≫
        (reduction l E Y h).map ((adjunction l E D hl f c m).counit.app L).hom := by
    apply evaluationPairing_injective l E D hl n aYn sYn
      ((PurCompactSupport.image
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c).obj K.obj) L'
    change tracePairing l E D f c n aXn aZn aYn sXn K L' (v.hom ≫ k.hom) = _ at hp
    let w := (PurCompactSupport.image
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c).map v.hom
    have hv := evaluationPairing_precomp l E D n aYn _ _ L' w
      ((PurCompactSupport.finiteImageIso l E n c).hom.app
        ((G l E D hl f c n).obj L').obj ≫
        ((adjunction l E D hl f c n).counit.app L').hom)
    have ht := congrArg (fun z ↦ aYn.tensor.map
      (Prod.mkHom w (𝟙 ((dual l E D Y n).obj (op L'.obj)))) ≫ z) hn.symm
    exact hv.trans (ht.trans (hp.symm.trans ((congrArg
      (tracePairing l E D f c n aXn aZn aYn sXn K L') hk).trans hs)))
  have hc : (F l E D hl f c n).map v ≫
        (adjunction l E D hl f c n).counit.app L' =
      (q l E D hl f c h).inv.app ((G l E D hl f c m).obj L) ≫
        (Q l E Y h).map ((adjunction l E D hl f c m).counit.app L) := by
    apply ObjectProperty.hom_ext
    exact cancel_natural_comparison
      ((PurCompactSupport.finiteImageIso l E n c).app K.obj) _ _ _ _ _
      ((PurCompactSupport.finiteImageIso l E n c).hom.naturality v.hom) he
  have hb : (b l E D hl f c h).app L = v := by
    apply ((adjunction l E D hl f c n).homEquiv K L').symm.injective
    change (F l E D hl f c n).map ((b l E D hl f c h).app L) ≫
      (adjunction l E D hl f c n).counit.app L' = _
    exact (mateEquiv_counit (adjunction l E D hl f c m)
      (adjunction l E D hl f c n) (q l E D hl f c h).inv L).trans hc.symm
  rw [hb]
  have : IsIso ((domain l E X n).ι.map v) := e.isIso_hom
  exact isIso_of_reflects_iso v (domain l E X n).ι

end WeilConjectures.FiniteExceptional
