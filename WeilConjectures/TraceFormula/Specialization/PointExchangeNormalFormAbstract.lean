/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.NatIso
public import WeilConjectures.TraceFormula.Specialization.MatchTactic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

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
    (χB : RB ⋙ Ts ⟶ SB ⋙ RB') (hχB : Mono (χB.app N)) (νB : SB ⋙ LSB' ⟶ LSB ⋙ Ts)
    (hνB : νB.app N ≫ Ts.map (is.hom.app N) ≫ χB.app N = is'.hom.app (SB.obj N))
    {Z₁ : Cs} {Z₁' : Cs'} (Φ₁ : LSa.obj (G.obj N) ⟶ Z₁) (Φ₂ : Z₁ ⟶ LSB.obj N)
    (Φ'₁ : LSa'.obj (G'.obj (SB.obj N)) ⟶ Z₁')
    (Φ'₂ : Z₁' ⟶ LSB'.obj (SB.obj N))
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
  have := hχB
  rw [← cancel_mono (Ts.map (is.hom.app N) ≫ χB.app N)]
  simp only [Category.assoc]
  rw [hνB]
  apply hι.map_injective
  rw [← cancel_epi (ιs'.map (i3.inv.app (OLS.obj (Lu'.obj (SpA.obj (G.obj N)))) ≫
    LSp.map (i2.inv.app (Lu'.obj (SpA.obj (G.obj N)))) ≫
    i1.inv.app (Lu'.obj (SpA.obj (G.obj N))) ≫ i'.inv.app (SpA.obj (G.obj N))))]
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

/-- `pointNormalForm_aux` with the image `LSa'(φ)` written on `(SB ⋙ G')(N)` (the form of the
concrete statement). -/
theorem pointNormalForm_aux' {A A' CX' CP Cs Cs' CB CB' DA DA' DX' DP Ds Ds' DB DB' : Type*}
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
    (χB : RB ⋙ Ts ⟶ SB ⋙ RB') (hχB : Mono (χB.app N)) (νB : SB ⋙ LSB' ⟶ LSB ⋙ Ts)
    (hνB : νB.app N ≫ Ts.map (is.hom.app N) ≫ χB.app N = is'.hom.app (SB.obj N))
    {Z₁ : Cs} (Φ₁ : LSa.obj (G.obj N) ⟶ Z₁) (Φ₂ : Z₁ ⟶ LSB.obj N)
    {W : A'} (φ : G'.obj (SB.obj N) ⟶ W)
    (Φ'₂ : LSa'.obj W ⟶ LSB'.obj (SB.obj N))
    (e_s : Rphg.obj (ιB.obj N) ⟶ ιs.obj (RB.obj N))
    (e_t : Rphg'.obj (ιB'.obj (SB.obj N)) ⟶ ιs'.obj (RB'.obj (SB.obj N)))
    (hS : ιs.map (Φ₁ ≫ Φ₂ ≫ is.hom.app N) = Hs ≫ e_s)
    (hT : ιs'.map (i3.inv.app (OLS.obj (Lu'.obj (G'.obj (SB.obj N)))) ≫
        LSp.map (i2.inv.app (Lu'.obj (G'.obj (SB.obj N)))) ≫
        i1.inv.app (Lu'.obj (G'.obj (SB.obj N))) ≫ i'.inv.app (G'.obj (SB.obj N))) ≫
        ιs'.map (LSa'.map φ ≫ Φ'₂ ≫ is'.hom.app (SB.obj N)) =
      cR.hom.app (OLS.obj (Lu'.obj (G'.obj (SB.obj N)))) ≫
        Rp.map (cO.hom.app (Lu'.obj (G'.obj (SB.obj N))) ≫
          Dh.map (cLu'.hom.app (G'.obj (SB.obj N))) ≫
          Dh.map (DuS'.map (cG'.hom.app (SB.obj N))) ≫
          Dh.map (eU'.app (ιB'.obj (SB.obj N))) ≫ eH'.app (ιB'.obj (SB.obj N))) ≫
        conj'.inv.app (ιB'.obj (SB.obj N)) ≫ e_t)
    (hχ : χphg.app (ιB.obj N) ≫ Rphg'.map (cSB.inv.app N) ≫ e_t =
      Ψs.map e_s ≫ cT.inv.app (RB.obj N) ≫ ιs'.map (χB.app N))
    (_hιB' : ιB' = ιB') :
    ν.app (G.obj N) ≫ Ts.map (Φ₁ ≫ Φ₂) =
      LSa'.map (χgB.app N) ≫ @Functor.map _ _ _ _ LSa' ((SB ⋙ G').obj N) W φ ≫ Φ'₂ ≫
        νB.app N :=
  pointNormalForm_aux i' hι i1 i2 i3 cO cR cT ν cSpA cLu' cG χg eU' eH' conj' χphg N Hs hF1 cG' cSB
    χgB hχg is is' χB hχB νB hνB Φ₁ Φ₂ (LSa'.map φ) Φ'₂ e_s e_t hS hT hχ

/-- The gluing of the target route: `Rp_* h_!(u_! g_* ≅ R(gu)_*)` read through the compatibility
isomorphisms `cR`, `cO` (abstractly; `ht1` is the description of the `u`-step, `hA` the
compactification route of `gu`). -/
theorem targetRoute_glue_aux {CS DS CP DP CX DX : Type*} [Category CS] [Category DS]
    [Category CP] [Category DP] [Category CX] [Category DX] {ι : CS ⥤ DS} {ιP : CP ⥤ DP}
    {ιX : CX ⥤ DX} {LStp : CP ⥤ CS} {Rp : DP ⥤ DS} {OLS : CX ⥤ CP} {Dh : DX ⥤ DP}
    (cR : LStp ⋙ ι ≅ ιP ⋙ Rp) (cO : OLS ⋙ ιP ≅ ιX ⋙ Dh) {Z Z' : CX} (y : Z ⟶ Z')
    {A1 A2 A3 W : DP} (x1 : Dh.obj (ιX.obj Z) ⟶ A1) (x2 : A1 ⟶ A2) (x3 : A2 ⟶ A3)
    (c : Dh.obj (ιX.obj Z') ⟶ A3) (ht1 : x1 ≫ x2 ≫ x3 = Dh.map (ιX.map y) ≫ c) (d : A3 ⟶ W)
    {S1 : CS} {T T' : DS} (b : Rp.obj W ⟶ T) (e : T ⟶ T') (w : LStp.obj (OLS.obj Z') ⟶ S1)
    (V : ι.obj S1 ⟶ T)
    (hA : cR.hom.app (OLS.obj Z') ≫ Rp.map (cO.hom.app Z') ≫ Rp.map c ≫ Rp.map d ≫ b =
      ι.map w ≫ V) :
    ι.map (LStp.map (OLS.map y)) ≫ ι.map w ≫ V ≫ e =
      cR.hom.app (OLS.obj Z) ≫ Rp.map (cO.hom.app Z ≫ x1 ≫ x2 ≫ x3 ≫ d) ≫ b ≫ e := by
  have n1 := cO.hom.naturality y
  have n2 := cR.hom.naturality (OLS.map y)
  simp only [Functor.comp_map, Functor.comp_obj] at n1 n2
  rw [reassoc_of% ht1, ← reassoc_of% n1, Rp.map_comp_assoc, ← reassoc_of% n2]
  simp only [Functor.map_comp, Category.assoc] at hA ⊢
  rw [reassoc_of% hA]

/-- `exact_kernel h` closes the goal with `h`, leaving the comparison of the type of `h` with the
goal to the kernel (see `exact_unchecked`). -/
elab "exact_kernel " h:term : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let e ← Lean.Elab.Tactic.elabTerm h none
  g.assign (← Lean.Meta.mkExpectedTypeHint e (← g.getType))
  Lean.Elab.Tactic.replaceMainGoal []

/-- `trans_kernel h₁ h₂` reduces a goal `a = d` to `b = c`, for `h₁ : a = b` and `h₂ : c = d`,
leaving all comparisons (of `a`, `d` with the goal and of the types of `b`, `c`) to the kernel. -/
elab "trans_kernel " h₁:term:max h₂:term:max : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let e₁ ← Lean.Elab.Tactic.elabTerm h₁ none
  let e₂ ← Lean.Elab.Tactic.elabTerm h₂ none
  let some (α, a, b) := (← Lean.Meta.whnfR (← Lean.Meta.inferType e₁)).eq? | throwError "h₁"
  let some (_, c, d) := (← Lean.Meta.whnfR (← Lean.Meta.inferType e₂)).eq? | throwError "h₂"
  let u ← Lean.Meta.getLevel α
  let mid ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
    (Lean.mkApp3 (Lean.mkConst ``Eq [u]) α b c)
  let p₁ := Lean.mkApp6 (Lean.mkConst ``Eq.trans [u]) α a b c e₁ mid
  let p := Lean.mkApp6 (Lean.mkConst ``Eq.trans [u]) α a c d p₁ e₂
  g.assign (← Lean.Meta.mkExpectedTypeHint p (← g.getType))
  Lean.Elab.Tactic.replaceMainGoal [mid.mvarId!]

/-- `trans_kernel_last h₁ k` is `trans_kernel h₁ (k T' e)`, where `e : _ ⟶ T'` is the last factor
of the right-hand side of the goal. -/
elab "trans_kernel_last " h₁:term:max k:term:max : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let e₁ ← Lean.Elab.Tactic.elabTerm h₁ none
  let ek ← Lean.Elab.Tactic.elabTerm k none
  let some (_, _, rhs) := (← Lean.Meta.whnfR (← g.getType)).eq? | throwError "goal"
  let mut last := rhs
  while last.isAppOfArity ``CategoryStruct.comp 7 do
    last := last.getArg! 6
  let some (_, _, _, T') := (← Lean.Meta.whnfR (← Lean.Meta.inferType last)).app4? ``Quiver.Hom
    | throwError "last factor"
  let e₂ := Lean.mkApp2 ek T' last
  let some (α, a, b) := (← Lean.Meta.whnfR (← Lean.Meta.inferType e₁)).eq? | throwError "h₁"
  let some (_, c, d) := (← Lean.Meta.whnfR (← Lean.Meta.inferType e₂)).eq? | throwError "k"
  let u ← Lean.Meta.getLevel α
  let mid ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
    (Lean.mkApp3 (Lean.mkConst ``Eq [u]) α b c)
  let p₁ := Lean.mkApp6 (Lean.mkConst ``Eq.trans [u]) α a b c e₁ mid
  let p := Lean.mkApp6 (Lean.mkConst ``Eq.trans [u]) α a c d p₁ e₂
  g.assign (← Lean.Meta.mkExpectedTypeHint p (← g.getType))
  Lean.Elab.Tactic.replaceMainGoal [mid.mvarId!]

/-- Splitting `ι(a ≫ b ≫ c ≫ d ≫ f ≫ e₁ ≫ e₂)` for the inclusion of a full subcategory. -/
lemma ObjectProperty.ι_map_comp_aux {C : Type*} [Category C] {P : ObjectProperty C}
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : P.FullSubcategory} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (f : X₄ ⟶ X₅) (e₁ : X₅ ⟶ X₆) (e₂ : X₆ ⟶ X₇) (e : X₅.obj ⟶ X₇.obj)
    (hq : P.ι.map (e₁ ≫ e₂) = e) :
    P.ι.map (a ≫ b ≫ c ≫ d ≫ f ≫ e₁ ≫ e₂) = P.ι.map a ≫ P.ι.map b ≫ (c ≫ d ≫ f).hom ≫ e := by
  subst hq
  simp

/-- The image of a composite of two `eqToHom`s is an `eqToHom`. -/
lemma Functor.map_eqToHom_comp_eqToHom {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} (p : X = Y) (q : Y = Z) (r : F.obj X = F.obj Z) :
    F.map (eqToHom p ≫ eqToHom q) = eqToHom r := by
  subst p q
  simp

/-- The exchange hypothesis `hχ` of `pointNormalForm_aux`, from the description of the `Dᵇc`
exchange `χB` as the ambient one `χBa` (`hmap`), the agreement of `χphg` and `χBa` up to transport
(`heq`) and of the transports `e_s`, `e_t` with the compatibility isomorphisms (`hs`, `ht`). -/
theorem pointNormalForm_hχ_aux {Ds Ds' DB DB' Cs Cs' CB CB' : Type*} [Category Ds]
    [Category Ds'] [Category DB] [Category DB'] [Category Cs] [Category Cs'] [Category CB]
    [Category CB'] {ιs : Cs ⥤ Ds} {ιs' : Cs' ⥤ Ds'} {ιB : CB ⥤ DB} {ιB' : CB' ⥤ DB'}
    {Ts : Cs ⥤ Cs'} {Ψs : Ds ⥤ Ds'} (cT : Ts ⋙ ιs' ≅ ιs ⋙ Ψs) {ΨB : DB ⥤ DB'} {SB : CB ⥤ CB'}
    (cSB : SB ⋙ ιB' ≅ ιB ⋙ ΨB) {RB : CB ⥤ Cs} {RB' : CB' ⥤ Cs'} {RBa : DB ⥤ Ds}
    {RBa' : DB' ⥤ Ds'} (cRB : RB ⋙ ιs ≅ ιB ⋙ RBa) (cRB' : RB' ⋙ ιs' ≅ ιB' ⋙ RBa')
    (χB : RB ⋙ Ts ⟶ SB ⋙ RB') (χBa : RBa ⋙ Ψs ⟶ ΨB ⋙ RBa') {Rphg : DB ⥤ Ds}
    {Rphg' : DB' ⥤ Ds'} (χphg : Rphg ⋙ Ψs ⟶ ΨB ⋙ Rphg') (N : CB)
    (hmap : ιs'.map (χB.app N) = cT.hom.app (RB.obj N) ≫ Ψs.map (cRB.hom.app N) ≫
      χBa.app (ιB.obj N) ≫ RBa'.map (cSB.inv.app N) ≫ cRB'.inv.app (SB.obj N))
    (h : Rphg.obj (ιB.obj N) = RBa.obj (ιB.obj N))
    (h' : Rphg'.obj (ΨB.obj (ιB.obj N)) = RBa'.obj (ΨB.obj (ιB.obj N)))
    (heq : χphg.app (ιB.obj N) ≫ eqToHom h' = Ψs.map (eqToHom h) ≫ χBa.app (ιB.obj N))
    (e_s : Rphg.obj (ιB.obj N) ⟶ ιs.obj (RB.obj N)) (hs : e_s ≫ cRB.hom.app N = eqToHom h)
    (e_t : Rphg'.obj (ιB'.obj (SB.obj N)) ⟶ ιs'.obj (RB'.obj (SB.obj N)))
    (ht : Rphg'.map (cSB.inv.app N) ≫ e_t =
      eqToHom h' ≫ RBa'.map (cSB.inv.app N) ≫ cRB'.inv.app (SB.obj N)) :
    χphg.app (ιB.obj N) ≫ Rphg'.map (cSB.inv.app N) ≫ e_t =
      Ψs.map e_s ≫ cT.inv.app (RB.obj N) ≫ ιs'.map (χB.app N) := by
  rw [hmap, ht, reassoc_of% heq, Iso.inv_hom_id_app_assoc, ← Ψs.map_comp_assoc, hs]

end CategoryTheory

open Lean Meta Elab Tactic in
/-- `close_by_match c` closes the goal with the lemma `c`, whose conclusion is matched
syntactically against the goal (`synMatch`, proof arguments are assigned without type check); the
comparison is left to the kernel. -/
elab "close_by_match " c:ident : tactic => withMainContext do
  let g ← getMainGoal
  let cst ← realizeGlobalConstNoOverload c
  let e ← mkConstWithFreshMVarLevels cst
  let (mvs, _, concl) ← forallMetaTelescope (← inferType e)
  let tgt ← instantiateMVars (← g.getType)
  synMatch concl tgt
  let pf ← instantiateMVars (mkAppN e mvs)
  if pf.hasExprMVar then throwError "close_by_match: unassigned arguments"
  g.assign (← mkExpectedTypeHint pf tgt)
  replaceMainGoal []

open Lean Meta Elab Tactic in
/-- `close_by_match_lhs c` closes a goal `l = eqToHom r` with the lemma `c : … → l' = eqToHom r'`
(last argument `r'`), matching `l'` syntactically against `l` and taking `r' := r`; the comparison
is left to the kernel. -/
elab "close_by_match_lhs " c:ident : tactic => withMainContext do
  let g ← getMainGoal
  let cst ← realizeGlobalConstNoOverload c
  let e ← mkConstWithFreshMVarLevels cst
  let (mvs, _, concl) ← forallMetaTelescope (← inferType e)
  let tgt ← instantiateMVars (← g.getType)
  let some (_, l, rhs) := (← whnfR tgt).eq? | throwError "not an equation"
  let some (_, l', _) := (← whnfR concl).eq? | throwError "not an equation"
  synMatch l' l
  (mvs[mvs.size - 1]!).mvarId!.assign rhs.consumeMData.appArg!
  let pf ← instantiateMVars (mkAppN e mvs)
  if pf.hasExprMVar then throwError "close_by_match_lhs: unassigned arguments"
  g.assign (← mkExpectedTypeHint pf tgt)
  replaceMainGoal []

