/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.SixFunctors.OpenClosedWeilMateData
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Sheaf.Paper.AutomorphismConstructibleStageEquivalence
import Sheaf.Paper.FiniteImmersionConstructibilityInterval
import Sheaf.Paper.OpenFiniteConstructibilityInterval
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-! # Finite constructibility and normalized finite presentations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor
universe u v
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
section
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
  {G G' : C ⥤ E} {H H' : D ⥤ F}
  (g : G ⟶ G') (h : H ⟶ H')
  (b : R₁ ⋙ G ⟶ H ⋙ R₂) (b' : R₁ ⋙ G' ⟶ H' ⋙ R₂)
private theorem inverseMate_naturality
    (hb : ∀ Y, g.app (R₁.obj Y) ≫ b'.app Y = b.app Y ≫ R₂.map (h.app Y))
    (X : C) :
    L₂.map (g.app X) ≫ ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b')).natTrans.app X =
      ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ b)).natTrans.app X ≫ h.app (L₁.obj X) := by
  simp only [mateEquiv_symm_apply]
  dsimp only [TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj, Functor.id_obj,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.comp_map]
  simp only [L₂.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  have hg := g.naturality (a₁.unit.app X)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hg
  have hh := a₂.counit.naturality (h.app (L₁.obj X))
  change L₂.map (R₂.map (h.app (L₁.obj X))) ≫ a₂.counit.app _ =
    a₂.counit.app _ ≫ h.app (L₁.obj X) at hh
  rw [← L₂.map_comp_assoc, ← hg]
  simp only [L₂.map_comp, Category.assoc]
  rw [← L₂.map_comp_assoc (g.app _) (b'.app _), hb, L₂.map_comp]
  simp only [Category.assoc]
  rw [hh]

private theorem mate_naturality
    (c : G ⋙ L₂ ⟶ L₁ ⋙ H) (c' : G' ⋙ L₂ ⟶ L₁ ⋙ H')
    (hc : ∀ X, L₂.map (g.app X) ≫ c'.app X = c.app X ≫ h.app (L₁.obj X))
    (Y : D) :
    g.app (R₁.obj Y) ≫ (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ c')).natTrans.app Y =
      (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ c)).natTrans.app Y ≫ R₂.map (h.app Y) := by
  simp only [mateEquiv_apply]
  dsimp only [TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj, Functor.id_obj,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.comp_map]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  have hg := a₂.unit.naturality (g.app (R₁.obj Y))
  change g.app (R₁.obj Y) ≫ a₂.unit.app _ =
    a₂.unit.app _ ≫ R₂.map (L₂.map (g.app (R₁.obj Y))) at hg
  have hh := h.naturality (a₁.counit.app Y)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hh
  rw [← Category.assoc, ← Category.assoc, hg]
  simp only [Category.assoc]
  rw [← R₂.map_comp_assoc, hc]
  simp only [R₂.map_comp, Category.assoc]
  rw [← R₂.map_comp, ← hh, R₂.map_comp]

end

section Cube
variable {X : Type u₁} {U : Type u₂} {X' : Type u₃} {U' : Type u₄}
  [Category.{v₁} X] [Category.{v₂} U] [Category.{v₃} X'] [Category.{v₄} U']
  {J : U ⥤ X} {j : X ⥤ U} {J' : U' ⥤ X'} {j' : X' ⥤ U'}
  (a : J ⊣ j) (a' : J' ⊣ j')
  {FX : X ⥤ X} {FU : U ⥤ U} {FX' : X' ⥤ X'} {FU' : U' ⥤ U'}
  (b : j ⋙ FU ≅ FX ⋙ j) (b' : j' ⋙ FU' ≅ FX' ⋙ j')
  (TX : X ⥤ X') (TU : U ⥤ U') (sj : j ⋙ TU ≅ TX ⋙ j')
  (sFX : FX ⋙ TX ≅ TX ⋙ FX') (sFU : FU ⋙ TU ≅ TU ⋙ FU')
private theorem inverseMate_unit (sJ : J ⋙ TX ≅ TU ⋙ J')
    (hJ : sJ.inv = ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ sj.hom)).natTrans)
    (N : U) :
    TU.map (a.unit.app N) ≫ sj.hom.app (J.obj N) ≫ j'.map (sJ.hom.app N) =
      a'.unit.app (TU.obj N) := by
  have h := unit_mateEquiv_symm a a' (TwoSquare.mk _ _ _ _ sj.hom) N
  change sJ.inv = (mateEquiv a a').symm (TwoSquare.mk _ _ _ _ sj.hom) at hJ
  rw [← hJ] at h
  change TU.map (a.unit.app N) ≫ sj.hom.app (J.obj N) =
    a'.unit.app (TU.obj N) ≫ j'.map (sJ.inv.app N) at h
  rw [← Category.assoc, h, Category.assoc, ← j'.map_comp,
    sJ.inv_hom_id_app]
  erw [j'.map_id, Category.comp_id]
private theorem inverseMate_counit (sJ : J ⋙ TX ≅ TU ⋙ J')
    (hJ : sJ.inv = ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ sj.hom)).natTrans)
    (K : X) :
    sJ.hom.app (j.obj K) ≫ J'.map (sj.hom.app K) ≫ a'.counit.app (TX.obj K) =
      TX.map (a.counit.app K) := by
  have h := mateEquiv_counit_symm a a' (TwoSquare.mk _ _ _ _ sj.hom) K
  change sJ.inv = (mateEquiv a a').symm (TwoSquare.mk _ _ _ _ sj.hom) at hJ
  rw [← hJ] at h
  change J'.map (sj.hom.app K) ≫ a'.counit.app (TX.obj K) =
    sJ.inv.app (j.obj K) ≫ TX.map (a.counit.app K) at h
  rw [h, ← Category.assoc, sJ.hom_inv_id_app, Category.id_comp]
private theorem inverseMate_cube (sJ : J ⋙ TX ≅ TU ⋙ J')
    (hJ : sJ.inv = ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ sj.hom)).natTrans)
    (hb : ∀ K, TU.map (b.hom.app K) ≫ sj.hom.app (FX.obj K) ≫
      j'.map (sFX.hom.app K) = sFU.hom.app (j.obj K) ≫
        FU'.map (sj.hom.app K) ≫ b'.hom.app (TX.obj K)) (N : U) :
    TX.map (((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans.app N) ≫
        sFX.hom.app (J.obj N) ≫ FX'.map (sJ.hom.app N) =
      sJ.hom.app (FU.obj N) ≫ J'.map (sFU.hom.app N) ≫
        ((mateEquiv a' a').symm (TwoSquare.mk _ _ _ _ b'.hom)).natTrans.app (TU.obj N) := by
  let bl := TwoSquare.vComp (TwoSquare.mk _ _ _ _ b.hom) (TwoSquare.mk _ _ _ _ sj.hom)
  let br := TwoSquare.vComp (TwoSquare.mk _ _ _ _ sj.hom) (TwoSquare.mk _ _ _ _ b'.hom)
  have hc := inverseMate_naturality a a' sFU.hom sFX.hom bl.natTrans br.natTrans
    (fun K ↦ by simpa [bl, br, Category.assoc] using (hb K).symm) N
  have hL := mateEquiv_vcomp a a a'
    ((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ b.hom))
    ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ sj.hom))
  simp only [Equiv.apply_symm_apply] at hL
  have hL' := congrArg (fun w ↦ ((mateEquiv a a').symm w).natTrans.app N) hL
  simp only [Equiv.symm_apply_apply] at hL'
  have hR := mateEquiv_vcomp a a' a'
    ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ sj.hom))
    ((mateEquiv a' a').symm (TwoSquare.mk _ _ _ _ b'.hom))
  simp only [Equiv.apply_symm_apply] at hR
  have hR' := congrArg (fun w ↦ ((mateEquiv a a').symm w).natTrans.app N) hR
  simp only [Equiv.symm_apply_apply] at hR'
  change _ = ((mateEquiv a a').symm bl).natTrans.app N at hL'
  change _ = ((mateEquiv a a').symm br).natTrans.app N at hR'
  rw [← hL', ← hR'] at hc
  dsimp only [TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app] at hc
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hc
  dsimp only [TwoSquare.mk, TwoSquare.natTrans] at hJ
  change sJ.inv = (mateEquiv a a').symm (TwoSquare.mk _ _ _ _ sj.hom) at hJ
  rw [← hJ] at hc
  apply (cancel_epi (sJ.inv.app (FU.obj N))).mp
  apply (cancel_mono (FX'.map (sJ.inv.app N))).mp
  simp only [Category.assoc, ← FX'.map_comp, sJ.hom_inv_id_app,
    sJ.inv_hom_id_app_assoc]
  erw [FX'.map_id, Category.comp_id]
  simpa only [TwoSquare.natTrans, Category.assoc, Category.comp_id] using hc.symm
end Cube

section ClosedCube
variable {X : Type u₁} {Z : Type u₂} {X' : Type u₃} {Z' : Type u₄}
  [Category.{v₁} X] [Category.{v₂} Z] [Category.{v₃} X'] [Category.{v₄} Z']
  {i : X ⥤ Z} {I : Z ⥤ X} {i' : X' ⥤ Z'} {I' : Z' ⥤ X'}
  (a : i ⊣ I) (a' : i' ⊣ I')
  {FX : X ⥤ X} {FZ : Z ⥤ Z} {FX' : X' ⥤ X'} {FZ' : Z' ⥤ Z'}
  (d : i ⋙ FZ ≅ FX ⋙ i) (d' : i' ⋙ FZ' ≅ FX' ⋙ i')
  (TX : X ⥤ X') (TZ : Z ⥤ Z') (si : i ⋙ TZ ≅ TX ⋙ i')
  (sFX : FX ⋙ TX ≅ TX ⋙ FX') (sFZ : FZ ⋙ TZ ≅ TZ ⋙ FZ')
private theorem mate_cube
    (hd : ∀ K, TZ.map (d.hom.app K) ≫ si.hom.app (FX.obj K) ≫
      i'.map (sFX.hom.app K) = sFZ.hom.app (i.obj K) ≫
        FZ'.map (si.hom.app K) ≫ d'.hom.app (TX.obj K)) (M : Z) :
    TX.map ((mateEquiv a a (TwoSquare.mk _ _ _ _ d.inv)).natTrans.app M) ≫
        (mateEquiv a a' (TwoSquare.mk _ _ _ _ si.inv)).natTrans.app (FZ.obj M) ≫
        I'.map (sFZ.hom.app M) =
      sFX.hom.app (I.obj M) ≫
        FX'.map ((mateEquiv a a' (TwoSquare.mk _ _ _ _ si.inv)).natTrans.app M) ≫
        (mateEquiv a' a' (TwoSquare.mk _ _ _ _ d'.inv)).natTrans.app (TZ.obj M) := by
  have hd' (K : X) :
      i'.map (sFX.hom.app K) ≫ d'.inv.app (TX.obj K) ≫ FZ'.map (si.inv.app K) =
        si.inv.app (FX.obj K) ≫ TZ.map (d.inv.app K) ≫ sFZ.hom.app (i.obj K) := by
    apply (cancel_epi (TZ.map (d.hom.app K) ≫ si.hom.app (FX.obj K))).mp
    simp only [Category.assoc]
    rw [← Category.assoc (si.hom.app _) (i'.map _),
      ← Category.assoc (TZ.map _) (si.hom.app _ ≫ _), hd]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← FZ'.map_comp,
      Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    erw [FZ'.map_id]
    erw [Category.comp_id]
    rw [← TZ.map_comp_assoc,
      d.hom_inv_id_app, TZ.map_id, Category.id_comp]
  let dl := TwoSquare.hComp (TwoSquare.mk _ _ _ _ d.inv)
    (TwoSquare.mk _ _ _ _ si.inv)
  let dr := TwoSquare.hComp (TwoSquare.mk _ _ _ _ si.inv)
    (TwoSquare.mk _ _ _ _ d'.inv)
  have hc := mate_naturality a a' sFX.hom sFZ.hom dl.natTrans dr.natTrans
    (fun K ↦ by simpa [dl, dr, Category.assoc] using hd' K) M
  have hL := mateEquiv_vcomp a a a' (TwoSquare.mk _ _ _ _ d.inv)
    (TwoSquare.mk _ _ _ _ si.inv)
  have hR := mateEquiv_vcomp a a' a' (TwoSquare.mk _ _ _ _ si.inv)
    (TwoSquare.mk _ _ _ _ d'.inv)
  have hL' := congrArg (fun w ↦ w.natTrans.app M) hL
  have hR' := congrArg (fun w ↦ w.natTrans.app M) hR
  change (mateEquiv a a' dl).natTrans.app M = _ at hL'
  change (mateEquiv a a' dr).natTrans.app M = _ at hR'
  rw [hL', hR'] at hc
  dsimp only [TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hc
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hc.symm
end ClosedCube

section Lift
universe uX vX uU vU uZ vZ uX' vX' uU' vU' uZ' vZ'
open WeilConjectures
private theorem scalarMateLift_of_equivalences
    {X : Type uX} [Category.{vX} X] {U : Type uU} [Category.{vU} U]
    {Z : Type uZ} [Category.{vZ} Z]
    {X' : Type uX'} [Category.{vX'} X'] {U' : Type uU'} [Category.{vU'} U']
    {Z' : Type uZ'} [Category.{vZ'} Z']
    {J : U ⥤ X} {j : X ⥤ U} {i : X ⥤ Z} {I : Z ⥤ X}
    {J' : U' ⥤ X'} {j' : X' ⥤ U'} {i' : X' ⥤ Z'} {I' : Z' ⥤ X'}
    (aj : J ⊣ j) (ai : i ⊣ I) (aj' : J' ⊣ j') (ai' : i' ⊣ I')
    {FX : X ⥤ X} {FU : U ⥤ U} {FZ : Z ⥤ Z}
    {FX' : X' ⥤ X'} {FU' : U' ⥤ U'} {FZ' : Z' ⥤ Z'}
    (b : j ⋙ FU ≅ FX ⋙ j) (d : i ⋙ FZ ≅ FX ⋙ i)
    (b' : j' ⋙ FU' ≅ FX' ⋙ j') (d' : i' ⋙ FZ' ≅ FX' ⋙ i')
    (TX : X ⥤ X') (TU : U ⥤ U') (TZ : Z ⥤ Z')
    [TX.IsEquivalence] [TU.IsEquivalence] [TZ.IsEquivalence]
    (sj : j ⋙ TU ≅ TX ⋙ j') (si : i ⋙ TZ ≅ TX ⋙ i')
    (sFX : FX ⋙ TX ≅ TX ⋙ FX') (sFU : FU ⋙ TU ≅ TU ⋙ FU')
    (sFZ : FZ ⋙ TZ ≅ TZ ⋙ FZ')
    (hb : ∀ K, TU.map (b.hom.app K) ≫ sj.hom.app (FX.obj K) ≫
      j'.map (sFX.hom.app K) = sFU.hom.app (j.obj K) ≫
        FU'.map (sj.hom.app K) ≫ b'.hom.app (TX.obj K))
    (hd : ∀ K, TZ.map (d.hom.app K) ≫ si.hom.app (FX.obj K) ≫
      i'.map (sFX.hom.app K) = sFZ.hom.app (i.obj K) ≫
        FZ'.map (si.hom.app K) ≫ d'.hom.app (TX.obj K)) :
    OpenClosedScalarMateLift aj ai aj' ai' b d b' d' TX TU TZ sj si sFX sFU sFZ := by
  let invJ := ((mateEquiv aj aj').symm (TwoSquare.mk _ _ _ _ sj.hom)).natTrans
  have : IsIso invJ := isIso_inverseMate_of_equivalences aj aj' sj
  let sJ := (asIso invJ).symm
  have hJ : sJ.inv = invJ := rfl
  have : IsIso (mateEquiv ai ai' (TwoSquare.mk _ _ _ _ si.inv)).natTrans :=
    isIso_mateEquiv_of_isEquivalence_of_fullyFaithful ai ai' TX TZ si.symm
  refine ⟨sJ, rfl, ?_⟩
  refine ⟨fun _ _ ↦ inferInstance, fun _ _ ↦ inferInstance,
    fun K _ ↦ hb K, fun K _ ↦ hd K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N _
    exact inverseMate_unit aj aj' TX TU sj sJ hJ N
  · intro K _
    exact inverseMate_counit aj aj' TX TU sj sJ hJ K
  · intro K _
    exact (unit_mateEquiv ai ai' (TwoSquare.mk _ _ _ _ si.inv) K).symm
  · intro M _
    exact mateEquiv_counit ai ai' (TwoSquare.mk _ _ _ _ si.inv) M
  · intro N _
    exact inverseMate_cube aj aj' b b' TX TU sj sFX sFU sJ hJ hb N
  · intro M _
    exact mate_cube ai ai' d d' TX TZ si sFX sFZ hd M
end Lift

section Conjugation
variable {X : Type u₁} {U : Type u₂} [Category.{v₁} X] [Category.{v₂} U]
  {j j' : X ⥤ U} {FX FX' : X ⥤ X} {FU FU' : U ⥤ U}
private theorem conjugation_coherence
    (sj : j ≅ j') (sx : FX ≅ FX') (su : FU ≅ FU')
    (b' : j' ⋙ FU' ≅ FX' ⋙ j') (K : X) :
    FU.map (sj.hom.app K) ≫ su.hom.app (j'.obj K) ≫ b'.hom.app K ≫
        j'.map (sx.inv.app K) ≫ sj.inv.app (FX.obj K) ≫ sj.hom.app (FX.obj K) ≫
        j'.map (sx.hom.app K) =
      su.hom.app (j.obj K) ≫ FU'.map (sj.hom.app K) ≫ b'.hom.app K := by
  rw [sj.inv_hom_id_app_assoc, ← j'.map_comp, sx.inv_hom_id_app,
    j'.map_id]
  erw [Category.comp_id]
  rw [← Category.assoc, su.hom.naturality]
  simp only [Category.assoc]
end Conjugation

section FinitePresentation
open WeilConjectures AlgebraicGeometry AlgebraicGeometry.Scheme
private theorem finitePresentation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    (n : ℕ) : sfFinitePresentationOpenClosedWeilMateAssertions D l E j₀ i₀ n := by
  unfold sfFinitePresentationOpenClosedWeilMateAssertions
  apply scalarMateLift_of_equivalences
  all_goals
    intro K
    simp only [sfFiniteRingFrobeniusSquare, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.id_map,
      Category.assoc]
    dsimp only [Functor.id_obj, Functor.comp_obj]
    first
    | exact conjugation_coherence (sfFiniteRingPullIso l E n (zlFiberMap D j₀))
        (sfFiniteRingPullIso l E n (D.geometricFrobenius X₀).hom)
        (sfFiniteRingPullIso l E n (D.geometricFrobenius U₀).hom) _ K
    | exact conjugation_coherence (sfFiniteRingPullIso l E n (zlFiberMap D i₀))
        (sfFiniteRingPullIso l E n (D.geometricFrobenius X₀).hom)
        (sfFiniteRingPullIso l E n (D.geometricFrobenius Z₀).hom) _ K

end FinitePresentation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
universe uX vX uU vU uZ vZ
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
omit [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] in
private theorem fiber_complement (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    (h : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ) :
    Set.range (zlFiberMap D j₀) = (Set.range (zlFiberMap D i₀))ᶜ := by
  have h' : Set.range j₀.left = (Set.range i₀.left)ᶜ := by
    change Set.range i₀.left = (Set.range j₀.left)ᶜ at h
    rw [h, compl_compl]
  simp only [zlFiberMap, Over.pullback_map_left]
  let t := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have hm {V₀ : Over (Spec (.of D.k₀))} (f₀ : V₀ ⟶ X₀) :
      pullback.lift (pullback.fst V₀.hom t ≫ f₀.left) (pullback.snd V₀.hom t)
          (by simp [pullback.condition]) =
        pullback.map V₀.hom t X₀.hom t f₀.left (𝟙 _) (𝟙 _)
          (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp
  rw [hm j₀, hm i₀]
  erw [Scheme.Pullback.range_map, Scheme.Pullback.range_map]
  have hid : (⇑(𝟙 (Spec (.of D.k))) : Spec (.of D.k) → Spec (.of D.k)) = id := rfl
  simp only [hid, Set.range_id, Set.preimage_univ, Set.inter_univ, h', Set.preimage_compl]

private theorem intrinsicPull_equivalence (A : Type u) [CommRing A] [Finite A]
    {X : Scheme.{u}} (e : Aut X) : (sfIntrinsicDerivedPullback A e.hom).IsEquivalence := by
  let J := sfIntrinsicDerivedPullback A e.inv
  let counit : sfIntrinsicDerivedPullback A e.hom ⋙ J ≅ 𝟭 _ :=
    (sfIntrinsicDerivedPullbackComp A e.inv e.hom).symm ≪≫
      eqToIso (congrArg (sfIntrinsicDerivedPullback A) e.inv_hom_id) ≪≫
        sfIntrinsicDerivedPullbackId A X
  let unit : J ⋙ sfIntrinsicDerivedPullback A e.hom ≅ 𝟭 _ :=
    (sfIntrinsicDerivedPullbackComp A e.hom e.inv).symm ≪≫
      eqToIso (congrArg (sfIntrinsicDerivedPullback A) e.hom_inv_id) ≪≫
        sfIntrinsicDerivedPullbackId A X
  exact Functor.IsEquivalence.mk' J counit.symm unit

private instance fiber_finiteType (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    LocallyOfFiniteType (D.geometricFiber T₀).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

private instance fiber_quasiCompact (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    QuasiCompact (D.geometricFiber T₀).hom :=
  inferInstanceAs (QuasiCompact
    (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

private instance fiber_noetherian (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    IsLocallyNoetherian (D.geometricFiber T₀).left :=
  LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber T₀).hom

private instance fiber_compact (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    CompactSpace (D.geometricFiber T₀).left :=
  QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber T₀).hom

include D hl in
private theorem finite_preservation
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {X U Z : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (h : Set.range j = (Set.range i)ᶜ)
    (hu : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) :
    let hn := Nat.succ_le_succ (Nat.zero_le n)
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) hn
    let PX := intrinsicFiniteTorsionConstructible l E (n + 1) hn X
    let PU := intrinsicFiniteTorsionConstructible l E (n + 1) hn U
    let PZ := intrinsicFiniteTorsionConstructible l E (n + 1) hn Z
    (∀ K, PX K → PU ((sfIntrinsicDerivedPullback A j).obj K)) ∧
    (∀ K, PX K → PZ ((sfIntrinsicDerivedPullback A i).obj K)) ∧
    (∀ N, PU N → PX ((sfIntrinsicDerivedOpen A j).obj N)) ∧
    (∀ M, PZ M → PX ((proEtaleConstantDerivedDirectImage i A).obj M)) := by
  let hn := Nat.succ_le_succ (Nat.zero_le n)
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) hn
  let PX := intrinsicFiniteTorsionConstructible l E (n + 1) hn X
  let PU := intrinsicFiniteTorsionConstructible l E (n + 1) hn U
  let PZ := intrinsicFiniteTorsionConstructible l E (n + 1) hn Z
  let : IsNoetherian X := ⟨⟩
  let : PU.IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated U A).1
  let : PZ.IsClosedUnderIsomorphisms :=
    (proEtale_bounded_constructible_isTriangulated Z A).1
  have hglobal : IsUnit (l : Γ(X, ⊤)) := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using hu x
  obtain ⟨hi, hj, hI, _⟩ := finiteImmersion_constructibility_interval D l hl E
    (n + 1) hn hglobal i j h
  refine ⟨?_, ?_, ?_, hI.2.2.2.2.2.1⟩
  · intro K hK
    exact PU.prop_of_iso ((openSquareDerivedPullbackModel A j).app K)
      (hj.2.2.2.2.2.1 K hK)
  · intro K hK
    exact PZ.prop_of_iso ((openSquareDerivedPullbackModel A i).app K)
      (hi.2.2.2.2.2.1 K hK)
  · intro N hN
    have hs : (proEtaleCohomologicalSupport N).Finite := hN.1
    obtain ⟨a, ha⟩ := hs.bddBelow
    obtain ⟨b, hb⟩ := hs.bddAbove
    have hsupport : proEtaleCohomologicalSupport N ⊆ Set.Icc (min a b) b :=
      fun r hr ↦ ⟨(min_le_left _ _).trans (ha hr), hb hr⟩
    exact (open_finite_constructibility_interval l E (n + 1) hn j hu
      (min a b) b (min_le_right _ _) N hN hsupport).1
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openClosedMateAssertions_of_isIso
    {X : Type uX} [Category.{vX} X]
    {U : Type uU} [Category.{vU} U]
    {Z : Type uZ} [Category.{vZ} Z]
    (jL : U ⥤ X) (jR : X ⥤ U) (iL : X ⥤ Z) (iR : Z ⥤ X)
    (adjJ : jL ⊣ jR) (adjI : iL ⊣ iR)
    (FX : X ⥤ X) (FU : U ⥤ U) (FZ : Z ⥤ Z)
    (b : jR ⋙ FU ≅ FX ⋙ jR) (d : iL ⋙ FZ ≅ FX ⋙ iL)
    (hAlpha : IsIso (openClosedAlpha adjJ b)) (hC : IsIso (openClosedC adjI d)) :
    OpenClosedWeilMateAssertions jL jR iL iR adjJ adjI FX FU FZ b d := by
  let alpha := ((mateEquiv adjJ adjJ).symm (TwoSquare.mk _ _ _ _ b.hom)).natTrans
  let c := (mateEquiv adjI adjI (TwoSquare.mk _ _ _ _ d.inv)).natTrans
  have : IsIso alpha := hAlpha
  have : IsIso c := hC
  let a := asIso alpha
  let ci := asIso c
  have ha (K : X) : FX.map (adjJ.counit.app K) =
      a.inv.app (jR.obj K) ≫ jL.map (b.hom.app K) ≫ adjJ.counit.app (FX.obj K) := by
    have h := mateEquiv_counit_symm adjJ adjJ (TwoSquare.mk _ _ _ _ b.hom) K
    change jL.map (b.hom.app K) ≫ adjJ.counit.app (FX.obj K) =
      a.hom.app (jR.obj K) ≫ FX.map (adjJ.counit.app K) at h
    rw [h, ← Category.assoc, a.inv_hom_id_app, Category.id_comp]
  have hc (K : X) : FX.map (adjI.unit.app K) ≫ ci.hom.app (iL.obj K) ≫
      iR.map (d.hom.app K) = adjI.unit.app (FX.obj K) := by
    have h := unit_mateEquiv adjI adjI (TwoSquare.mk _ _ _ _ d.inv) K
    change FX.map (adjI.unit.app K) ≫ ci.hom.app (iL.obj K) =
      adjI.unit.app (FX.obj K) ≫ iR.map (d.inv.app K) at h
    rw [← Category.assoc, h, Category.assoc, ← iR.map_comp,
      d.inv_hom_id_app]
    change adjI.unit.app (FX.obj K) ≫ iR.map (𝟙 _) = _
    rw [iR.map_id]
    exact Category.comp_id (adjI.unit.app (FX.obj K))
  refine ⟨a, ci, rfl, rfl, ?_, ?_, ha, hc, ?_⟩
  · intro N
    simp [a, alpha]
  · intro M
    simp [ci, c]
  · intro K theta
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · have hn := adjJ.counit.naturality theta.hom
      change jL.map (jR.map theta.hom) ≫ adjJ.counit.app K =
        adjJ.counit.app (FX.obj K) ≫ theta.hom at hn
      rw [Category.assoc, Category.assoc, hn, ha K]
      simp only [Category.assoc]
    · have hn := adjI.unit.naturality theta.hom
      change theta.hom ≫ adjI.unit.app K =
        adjI.unit.app (FX.obj K) ≫ iR.map (iL.map theta.hom) at hn
      rw [hn, ← hc K]
      simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictedOpenClosed_of_assertions
    {X : Type uX} [Category.{vX} X]
    {U : Type uU} [Category.{vU} U]
    {Z : Type uZ} [Category.{vZ} Z]
    (PX : ObjectProperty X) (PU : ObjectProperty U) (PZ : ObjectProperty Z)
    (jL : U ⥤ X) (jR : X ⥤ U) (iL : X ⥤ Z) (iR : Z ⥤ X)
    (adjJ : jL ⊣ jR) (adjI : iL ⊣ iR)
    (FX : X ⥤ X) (FU : U ⥤ U) (FZ : Z ⥤ Z)
    (b : jR ⋙ FU ≅ FX ⋙ jR) (d : iL ⋙ FZ ≅ FX ⋙ iL)
    (h : OpenClosedWeilMateAssertions jL jR iL iR adjJ adjI FX FU FZ b d)
    (hj : ∀ K, PX K → PU (jR.obj K))
    (hi : ∀ K, PX K → PZ (iL.obj K))
    (hJ : ∀ N, PU N → PX (jL.obj N))
    (hI : ∀ M, PZ M → PX (iR.obj M)) :
    RestrictedOpenClosedWeilMateAssertions PX PU PZ jL jR iL iR adjJ adjI
      FX FU FZ b d := by
  obtain ⟨a, c, ha, hc, hfa, hfc, hea, hec, _⟩ := h
  change a.hom = openClosedAlpha adjJ b at ha
  change c.hom = openClosedC adjI d at hc
  unfold RestrictedOpenClosedWeilMateAssertions
  rw [← ha, ← hc]
  refine ⟨fun _ _ ↦ inferInstance, fun _ _ ↦ inferInstance,
    fun N _ ↦ hfa N, fun M _ ↦ hfc M, ?_⟩
  intro K hK
  exact ⟨hj K hK, hi K hK, hJ _ (hj K hK), hI _ (hi K hK),
    a.symm.app (jR.obj K), c.app (iL.obj K), rfl, rfl, hea K, hec K⟩

attribute [local irreducible] sfIntrinsicModuleEquivalence
  exceptionalOpenAdjunction
  sfIntrinsicConstantModuleAdjunction sfFiniteOpenClosedWeilMateAssertions

include hl in
private theorem finite_mates
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left]
    (h : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ) (n : ℕ) :
    sfFiniteOpenClosedWeilMateAssertions D l E j₀ i₀ n := by
  let : IsOpenImmersion (zlFiberMap D j₀) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance
  let : IsClosedImmersion (zlFiberMap D i₀) :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) i₀ inferInstance
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  have hX := intrinsicPull_equivalence A (D.geometricFrobenius X₀)
  have hU := intrinsicPull_equivalence A (D.geometricFrobenius U₀)
  have hZ := intrinsicPull_equivalence A (D.geometricFrobenius Z₀)
  let : IsLocallyNoetherian (D.geometricFiber X₀).left := fiber_noetherian D X₀
  let : CompactSpace (D.geometricFiber X₀).left := fiber_compact D X₀
  have hp := finite_preservation D l hl E n
    (X := (D.geometricFiber X₀).left) (U := (D.geometricFiber U₀).left)
    (Z := (D.geometricFiber Z₀).left) (zlFiberMap D j₀) (zlFiberMap D i₀)
    (fiber_complement D j₀ i₀ h)
    (automorphismConstructibleStage_units D l hl (D.geometricFiber X₀)).1
  let aj := exceptionalOpenAdjunction (zlFiberMap D j₀) A
  let ai := (sfIntrinsicConstantModuleAdjunction (zlFiberMap D i₀) A)
    |>.mapDerivedCategoryRightDerivedAdjunction.{u+1,u+1,u+2,u+2,u+2,u+2}
  let b := sfIntrinsicDerivedSquarePullback A (D.geometricFrobenius U₀).hom
    (zlFiberMap D j₀) (zlFiberMap D j₀) (D.geometricFrobenius X₀).hom
    (zlFrobenius_naturality D j₀)
  let d := sfIntrinsicDerivedSquarePullback A (D.geometricFrobenius Z₀).hom
    (zlFiberMap D i₀) (zlFiberMap D i₀) (D.geometricFrobenius X₀).hom
    (zlFrobenius_naturality D i₀)
  have ha : IsIso (openClosedAlpha aj b) :=
    isIso_inverseMate_of_equivalences aj aj b
  have hc : IsIso (openClosedC ai d) :=
    isIso_mateEquiv_of_isEquivalence_of_fullyFaithful ai ai
      (sfIntrinsicDerivedPullback A (D.geometricFrobenius X₀).hom)
      (sfIntrinsicDerivedPullback A (D.geometricFrobenius Z₀).hom) d.symm
  have hfull := openClosedMateAssertions_of_isIso
    (sfIntrinsicDerivedOpen A (zlFiberMap D j₀))
    (sfIntrinsicDerivedPullback A (zlFiberMap D j₀))
    (sfIntrinsicDerivedPullback A (zlFiberMap D i₀))
    (proEtaleConstantDerivedDirectImage (zlFiberMap D i₀) A) aj ai
    (sfIntrinsicDerivedPullback A (D.geometricFrobenius X₀).hom)
    (sfIntrinsicDerivedPullback A (D.geometricFrobenius U₀).hom)
    (sfIntrinsicDerivedPullback A (D.geometricFrobenius Z₀).hom) b d ha hc
  unfold sfFiniteOpenClosedWeilMateAssertions
  exact restrictedOpenClosed_of_assertions _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfull
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
end WeilConjectures

namespace WeilConjectures
/-- Finite constructibility and normalized finite presentations.
Source: main-20261015, open/closed localization, coefficient and Weil paragraphs.
(blueprint: lem-sf-open-closed-weil-mate-finite-stage).

Proof: Use the geometric-Frobenius automorphisms and their inverse pullbacks to obtain
finite intrinsic equivalences. The finite immersion constructibility interval
preserves the two restrictions and the closed image; finite open extension
preserves the bounded support interval. Restrict the ordinary adjunctions.
The intrinsic inverse and forward mates are invertible by the equivalence mate
lemmas. Their unit/counit identities follow from the mate correspondence.
Conjugate the intrinsic pullback squares by sfFiniteRingPullIso. The mates of
these comparisons identify both adjoints and their units and counits. Pasting
mates gives both three-factor transport equations, including identity and empty
immersions. -/
theorem sf_openClosed_weil_finite_stage
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (_ιE : E →ₐ[Padic l] Ω)
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left]
    (_hij : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ) :
    (∀ n : ℕ, sfFiniteOpenClosedWeilMateAssertions D l E j₀ i₀ n) ∧
    (∀ n : ℕ, sfFinitePresentationOpenClosedWeilMateAssertions D l E j₀ i₀ n) := by
  exact ⟨fun n ↦ finite_mates D l hl E j₀ i₀ _hij n,
    fun n ↦ finitePresentation D l E j₀ i₀ n⟩

end WeilConjectures
