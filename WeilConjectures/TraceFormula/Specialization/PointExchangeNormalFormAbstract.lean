/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.NatIso

/-!

# The exchange `ν_X` on a proper component in normal form, abstractly

The identity `pointCompactSupportExchangeOfSeparated_app_lowerStar_normalForm` is deduced, in
arbitrary categories (`CategoryTheory.pointNormalForm_aux`), from

* the identity of `ν_X` on `G N = Rg_* N` through the compactification (hypothesis `hF1`, the
  conclusion of `openPointExchangeAux_app_comp_aux_of_eq`);
* the normal forms of the compactification routes of the source and of the target
  (hypotheses `hS`, `hT`);
* the descriptions of the exchanges on bounded constructible complexes as the ambient ones
  (`hχg`, `hχ`) and the definition of `ν_B` as an inverse exchange (`hνB`).

-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- **`ν_X` on a proper component in normal form**, abstractly (see the module docstring). -/
theorem pointNormalForm_aux {A A' CX' CP Cs Cs' CB CB' DA DA' DX' DP Ds Ds' DB DB' : Type*}
    [Category A] [Category A'] [Category CX'] [Category CP] [Category Cs]
    [Category Cs'] [Category CB] [Category CB'] [Category DA] [Category DA']
    [Category DX'] [Category DP] [Category Ds] [Category Ds'] [Category DB] [Category DB']
    {SpA : A ⥤ A'} {Ts : Cs ⥤ Cs'} {Lu' : A' ⥤ CX'} {LSa : A ⥤ Cs}
    {LSa' : A' ⥤ Cs'} {LSb' : CX' ⥤ Cs'} (i' : LSa' ≅ Lu' ⋙ LSb')
    {LSh OLS : CX' ⥤ CP} {LSp LStp : CP ⥤ Cs'}
    {ιA : A ⥤ DA} {ιA' : A' ⥤ DA'} {ιX' : CX' ⥤ DX'} {ιP : CP ⥤ DP}
    {ιs : Cs ⥤ Ds} {ιs' : Cs' ⥤ Ds'} {ιB : CB ⥤ DB} {ιB' : CB' ⥤ DB'} (hι : ιs'.Faithful)
    {ΨA : DA ⥤ DA'} {Ψs : Ds ⥤ Ds'} {ΨB : DB ⥤ DB'} {Dh : DX' ⥤ DP} {Rp : DP ⥤ Ds'}
    (i1 : LSb' ≅ LSh ⋙ LSp) (i2 : LSh ≅ OLS) (i3 : LSp ≅ LStp)
    (cO : OLS ⋙ ιP ≅ ιX' ⋙ Dh) (cR : LStp ⋙ ιs' ≅ ιP ⋙ Rp) (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs)
    (ν : SpA ⋙ LSa' ⟶ LSa ⋙ Ts) {DuS' : DA' ⥤ DX'} (cSpA : SpA ⋙ ιA' ≅ ιA ⋙ ΨA)
    (cLu' : Lu' ⋙ ιX' ≅ ιA' ⋙ DuS') {G : CB ⥤ A} {Rg : DB ⥤ DA} (cG : G ⋙ ιA ≅ ιB ⋙ Rg)
    {Rphg : DB ⥤ Ds} {Rg' : DB' ⥤ DA'} {Rug' : DB' ⥤ DX'} {Rhug' : DB' ⥤ DP}
    {Rphg' : DB' ⥤ Ds'} (χg : Rg ⋙ ΨA ⟶ ΨB ⋙ Rg') (eU' : Rg' ⋙ DuS' ⟶ Rug')
    (eH' : Rug' ⋙ Dh ⟶ Rhug') (conj' : Rphg' ≅ Rhug' ⋙ Rp) (χphg : Rphg ⋙ Ψs ⟶ ΨB ⋙ Rphg')
    (N : CB) (Hs : ιs.obj (LSa.obj (G.obj N)) ⟶ Rphg.obj (ιB.obj N))
    (hF1 : ιs'.map (i3.inv.app (OLS.obj (Lu'.obj (SpA.obj (G.obj N)))) ≫
        LSp.map (i2.inv.app (Lu'.obj (SpA.obj (G.obj N)))) ≫
        i1.inv.app (Lu'.obj (SpA.obj (G.obj N))) ≫ i'.inv.app (SpA.obj (G.obj N))) ≫
        ιs'.map (ν.app (G.obj N)) ≫ cT.hom.app (LSa.obj (G.obj N)) ≫
        Ψs.map Hs ≫ χphg.app (ιB.obj N) =
      cR.hom.app (OLS.obj (Lu'.obj (SpA.obj (G.obj N)))) ≫
        Rp.map (cO.hom.app (Lu'.obj (SpA.obj (G.obj N))) ≫
          Dh.map (cLu'.hom.app (SpA.obj (G.obj N))) ≫ Dh.map (DuS'.map (cSpA.hom.app (G.obj N))) ≫
          Dh.map (DuS'.map (ΨA.map (cG.hom.app N))) ≫ Dh.map (DuS'.map (χg.app (ιB.obj N))) ≫
          Dh.map (eU'.app (ΨB.obj (ιB.obj N))) ≫ eH'.app (ΨB.obj (ιB.obj N))) ≫
        conj'.inv.app (ΨB.obj (ιB.obj N)))
    {G' : CB' ⥤ A'} {SB : CB ⥤ CB'} (cG' : G' ⋙ ιA' ≅ ιB' ⋙ Rg') (cSB : SB ⋙ ιB' ≅ ιB ⋙ ΨB)
    (χgB : G ⋙ SpA ⟶ SB ⋙ G')
    (hχg : ιA'.map (χgB.app N) = cSpA.hom.app (G.obj N) ≫ ΨA.map (cG.hom.app N) ≫
      χg.app (ιB.obj N) ≫ Rg'.map (cSB.inv.app N) ≫ cG'.inv.app (SB.obj N))
    {LSB RB : CB ⥤ Cs} {LSB' RB' : CB' ⥤ Cs'} (is : LSB ≅ RB) (is' : LSB' ≅ RB')
    (χB : RB ⋙ Ts ⟶ SB ⋙ RB') [Mono (χB.app N)] (νB : SB ⋙ LSB' ⟶ LSB ⋙ Ts)
    (hνB : νB.app N ≫ Ts.map (is.hom.app N) ≫ χB.app N = is'.hom.app (SB.obj N))
    (Φ₁ : LSa.obj (G.obj N) ⟶ LSa.obj (G.obj N)) (Φ₂ : LSa.obj (G.obj N) ⟶ LSB.obj N)
    (Φ'₁ : LSa'.obj (G'.obj (SB.obj N)) ⟶ LSa'.obj (G'.obj (SB.obj N)))
    (Φ'₂ : LSa'.obj (G'.obj (SB.obj N)) ⟶ LSB'.obj (SB.obj N))
    (e_s : Rphg.obj (ιB.obj N) ⟶ ιs.obj (RB.obj N))
    (e_t : Rphg'.obj (ιB'.obj (SB.obj N)) ⟶ ιs'.obj (RB'.obj (SB.obj N)))
    (hS : ιs.map (Φ₁ ≫ Φ₂ ≫ is.hom.app N) = Hs ≫ e_s)
    (hT : ιs'.map (i3.inv.app (OLS.obj (Lu'.obj (G'.obj (SB.obj N)))) ≫
        LSp.map (i2.inv.app (Lu'.obj (G'.obj (SB.obj N)))) ≫
        i1.inv.app (Lu'.obj (G'.obj (SB.obj N))) ≫ i'.inv.app (G'.obj (SB.obj N))) ≫
        ιs'.map (Φ'₁ ≫ Φ'₂ ≫ is'.hom.app (SB.obj N)) =
      cR.hom.app (OLS.obj (Lu'.obj (G'.obj (SB.obj N)))) ≫
        Rp.map (cO.hom.app (Lu'.obj (G'.obj (SB.obj N))) ≫
          Dh.map (cLu'.hom.app (G'.obj (SB.obj N))) ≫
          Dh.map (DuS'.map (cG'.hom.app (SB.obj N))) ≫
          Dh.map (eU'.app (ιB'.obj (SB.obj N))) ≫ eH'.app (ιB'.obj (SB.obj N))) ≫
        conj'.inv.app (ιB'.obj (SB.obj N)) ≫ e_t)
    (hχ : χphg.app (ιB.obj N) ≫ Rphg'.map (cSB.inv.app N) ≫ e_t =
      Ψs.map e_s ≫ cT.inv.app (RB.obj N) ≫ ιs'.map (χB.app N)) :
    ν.app (G.obj N) ≫ Ts.map (Φ₁ ≫ Φ₂) =
      LSa'.map (χgB.app N) ≫ Φ'₁ ≫ Φ'₂ ≫ νB.app N := by
  rw [← cancel_mono (Ts.map (is.hom.app N) ≫ χB.app N)]
  simp only [Category.assoc]
  rw [hνB]
  apply hι.map_injective
  rw [← cancel_epi (ιs'.map (i3.inv.app (OLS.obj (Lu'.obj (SpA.obj (G.obj N)))) ≫
    LSp.map (i2.inv.app (Lu'.obj (SpA.obj (G.obj N)))) ≫ i1.inv.app (Lu'.obj (SpA.obj (G.obj N))) ≫ i'.inv.app (SpA.obj (G.obj N))))]
  -- the source side
  have hTy {Y Z : Cs} (y : Y ⟶ Z) :
      ιs'.map (Ts.map y) = cT.hom.app Y ≫ Ψs.map (ιs.map y) ≫ cT.inv.app Z := by
    have := cT.hom.naturality y
    simp only [Functor.comp_map, Functor.comp_obj] at this
    rw [← reassoc_of% this, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hL : ιs'.map (ν.app (G.obj N) ≫ Ts.map (Φ₁ ≫ Φ₂) ≫ Ts.map (is.hom.app N) ≫
      χB.app N) = ιs'.map (ν.app (G.obj N)) ≫ cT.hom.app (LSa.obj (G.obj N)) ≫ Ψs.map Hs ≫
        χphg.app (ιB.obj N) ≫ Rphg'.map (cSB.inv.app N) ≫ e_t := by
    rw [← Ts.map_comp_assoc, Functor.map_comp, Functor.map_comp, hTy, Category.assoc Φ₁, hS, hχ,
      Functor.map_comp]
    simp only [Category.assoc]
  rw [hL, reassoc_of% hF1]
  -- the target side
  have hχg' : cSpA.hom.app (G.obj N) ≫ ΨA.map (cG.hom.app N) ≫ χg.app (ιB.obj N) ≫
      Rg'.map (cSB.inv.app N) = ιA'.map (χgB.app N) ≫ cG'.hom.app (SB.obj N) := by
    rw [hχg]
    simp
  have n1 := conj'.inv.naturality (cSB.inv.app N)
  have n2 := eH'.naturality (cSB.inv.app N)
  have n3 := eU'.naturality (cSB.inv.app N)
  simp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3
  have hX : (cO.hom.app (Lu'.obj (SpA.obj (G.obj N))) ≫ Dh.map (cLu'.hom.app (SpA.obj (G.obj N))) ≫
      Dh.map (DuS'.map (cSpA.hom.app (G.obj N))) ≫ Dh.map (DuS'.map (ΨA.map (cG.hom.app N))) ≫
      Dh.map (DuS'.map (χg.app (ιB.obj N))) ≫ Dh.map (eU'.app (ΨB.obj (ιB.obj N))) ≫
      eH'.app (ΨB.obj (ιB.obj N))) ≫ Rhug'.map (cSB.inv.app N) =
      cO.hom.app (Lu'.obj (SpA.obj (G.obj N))) ≫ Dh.map (cLu'.hom.app (SpA.obj (G.obj N))) ≫
        Dh.map (DuS'.map (ιA'.map (χgB.app N) ≫ cG'.hom.app (SB.obj N))) ≫
        Dh.map (eU'.app (ιB'.obj (SB.obj N))) ≫ eH'.app (ιB'.obj (SB.obj N)) := by
    rw [← hχg']
    simp only [Category.assoc, Functor.map_comp]
    rw [← n2, ← Dh.map_comp_assoc (eU'.app (ΨB.obj (ιB.obj N))), ← n3]
    simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% n1, ← Rp.map_comp_assoc, hX]
  -- the naturality of the composition isomorphisms

  have hQ {Z : Cs'} (h : LSa'.obj (G'.obj (SB.obj N)) ⟶ Z) :
      i3.inv.app (OLS.obj (Lu'.obj (SpA.obj (G.obj N)))) ≫
        LSp.map (i2.inv.app (Lu'.obj (SpA.obj (G.obj N)))) ≫
        i1.inv.app (Lu'.obj (SpA.obj (G.obj N))) ≫ i'.inv.app (SpA.obj (G.obj N)) ≫
        LSa'.map (χgB.app N) ≫ h =
      LStp.map (OLS.map (Lu'.map (χgB.app N))) ≫
        i3.inv.app (OLS.obj (Lu'.obj (G'.obj (SB.obj N)))) ≫
        LSp.map (i2.inv.app (Lu'.obj (G'.obj (SB.obj N)))) ≫
        i1.inv.app (Lu'.obj (G'.obj (SB.obj N))) ≫ i'.inv.app (G'.obj (SB.obj N)) ≫ h := by
    have a1 := i'.inv.naturality (χgB.app N)
    have a2 := i1.inv.naturality (Lu'.map (χgB.app N))
    have a3 := i2.inv.naturality (Lu'.map (χgB.app N))
    have a4 := i3.inv.naturality (OLS.map (Lu'.map (χgB.app N)))
    simp only [Functor.comp_map, Functor.comp_obj] at a1 a2 a3 a4
    rw [← reassoc_of% a1, ← reassoc_of% a2, ← LSp.map_comp_assoc, ← a3, LSp.map_comp_assoc,
      reassoc_of% a4]
  have hT' := hT
  rw [← ιs'.map_comp] at hT'
  simp only [Category.assoc] at hT'
  rw [← ιs'.map_comp]
  simp only [Category.assoc]
  rw [hQ, ιs'.map_comp, hT']
  have b1 := cR.hom.naturality (OLS.map (Lu'.map (χgB.app N)))
  have b2 := cO.hom.naturality (Lu'.map (χgB.app N))
  have b3 := cLu'.hom.naturality (χgB.app N)
  simp only [Functor.comp_map, Functor.comp_obj] at b1 b2 b3
  rw [reassoc_of% b1, ← Rp.map_comp_assoc, reassoc_of% b2,
    ← Dh.map_comp_assoc (ιX'.map (Lu'.map (χgB.app N))), b3]
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
