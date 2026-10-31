/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedFiniteExchangeCoordinates
import WeilConjectures.AlgebraicGeometry.TowerOpenBetaNormalization
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Ordinary completed-to-finite scalar compatibility

The coefficient projection intertwines the normalized ordinary inverse exchanges.
Source: Stacks Project, Modules on Sites, Tags 03DI, 03D7 and 04J0;
blueprint finite-exchange identification before derived inverse limits.
(blueprint: lem-cbc-completed-finite-scalar-exchange).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower


private theorem openRestriction_section {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ)
    (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) T) (V : W.ProEt)
    (m : M.val.obj (op ((cbcOpenSiteFunctor e he).obj V))) :
    ((cbcFiniteOpenRestriction d e he n).hom.app M).val.app (op V)
      (@openBetaSection (cbcFiniteRing d n) _ W T e he M V m) = m := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
    (cbcOpenWeaklyEtale e he) trivial
  have h := (cbcFiniteOpenRestriction_existsUnique d e he n).exists.choose_spec
    M V ((cbcOpenSiteFunctor e he).obj V) (a.unit.app V) m
  have hid := a.homEquiv_symm_unit V
  have hmap := congrArg (fun f ↦ M.val.map f.op m) hid
  have hm : M.val.map (𝟙 ((cbcOpenSiteFunctor e he).obj V)).op m = m := by
    exact congrArg (fun k ↦ k.hom m) (M.val.map_id _)
  have h' := (h.trans hmap).trans hm
  unfold cbcFiniteOpenRestriction
  dsimp only [openBetaSection, openBetaModuleAdj, cbcOpenSiteFunctor, a] at h' ⊢
  exact h'

private theorem openRestriction_generator {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ)
    (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) T) (V : W.ProEt)
    (x : ((modulePullback (cbcFiniteRing d n) e).obj M).val.obj (op V)) :
    @openBetaSection (cbcFiniteRing d n) _ W T e he M V
      (((cbcFiniteOpenRestriction d e he n).hom.app M).val.app (op V) x) = x := by
  apply (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation _ (op V)).map
      ((cbcFiniteOpenRestriction d e he n).hom.app M))).injective
  exact openRestriction_section d e he n M V _

private theorem directRes_apply {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) S) (V : T.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange f).op.obj V)) :
    ((cbcFiniteDirectRes d f n).hom.app M).val.app V x = x := by
  simpa only [cbcFiniteDirectRes] using
    (cbcFiniteDirectRes_existsUnique d f n).exists.choose_spec M V x

set_option maxHeartbeats 4000000 in
-- Sectionwise equality unfolds restriction of scalars on completed coefficient sheaves.
private theorem right_exchange_square (n : ℕ)
    (N : ProEtale.StrictTower.Modules (cbcFiniteRing d n) X') :
    (cbcFiniteOpenRestriction d j sq.isOpenImmersion n).hom.app
        ((moduleDirectImage (cbcFiniteRing d n) g).obj N) ≫
      (cbcOpenRestriction d j sq.isOpenImmersion).map
        ((cbcFiniteDirectRes d g n).hom.app N) ≫
      (cbcRightExchange d sq).app ((cbcFiniteRes d X' n).obj N) =
    (cbcFiniteRes d U n).map
        ((openBetaRestriction (cbcFiniteRing d n) gU j' j g sq.w).app N) ≫
      (cbcFiniteDirectRes d gU n).hom.app
        ((modulePullback (cbcFiniteRing d n) j').obj N) ≫
      (cbcCompletedModuleDirectImage d gU).map
        ((cbcFiniteOpenRestriction d j' sq.isOpenImmersion' n).hom.app N) := by
  let := sq.isOpenImmersion
  let := sq.isOpenImmersion'
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [directRes_apply d g n, directRes_apply d gU n]
  erw [(cbcRightExchange_exists d sq).exists.choose_spec]
  let m := ((cbcFiniteOpenRestriction d j sq.isOpenImmersion n).hom.app
    ((moduleDirectImage (cbcFiniteRing d n) g).obj N)).val.app V x
  have hx := openRestriction_generator d j sq.isOpenImmersion n
    ((moduleDirectImage (cbcFiniteRing d n) g).obj N) V.unop x
  have hb := (openBetaRestriction_normalized (cbcFiniteRing d n) gU j' j g sq.w
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)).2
      N V.unop m
  rw [hx] at hb
  change N.val.map
      ((MorphismProperty.Over.pullbackMapComparison
        (cbcOpenWeaklyEtale j sq.isOpenImmersion)
        (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq).app V.unop).op m =
    ((cbcFiniteOpenRestriction d j' sq.isOpenImmersion' n).hom.app N).val.app
      (op ((proEtaleBaseChange gU).obj V.unop))
      (((openBetaRestriction (cbcFiniteRing d n) gU j' j g sq.w).app N).val.app
        (op V.unop) x)
  rw [hb, openRestriction_section]
  rfl

private theorem mates_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q : TwoSquare G L₁ L₃ H) (r : TwoSquare G L₂ L₄ H)
    (s : L₄ ⟶ L₃) (t : L₂ ⟶ L₁)
    (h : (mateEquiv a₁ a₃ q).whiskerBottom (conjugateEquiv a₃ a₄ s) =
      (mateEquiv a₂ a₄ r).whiskerTop (conjugateEquiv a₁ a₂ t)) :
    q.whiskerRight s = r.whiskerLeft t := by
  apply (mateEquiv a₁ a₄).injective
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp]
  exact h

/-- The ordinary inverse exchange commutes with the finite scalar projection.
Source: Stacks Project, Modules on Sites, lemma-extension-by-zero (03DI),
lemma-adjoint-pullback-pushforward-modules (03D7), and
lemma-localize-morphism-ringed-sites (04J0); finite-exchange identification
in the blueprint completed-extension-zero comparison, Step 8 of the parent.
(blueprint: lem-cbc-completed-finite-scalar-exchange).

Proof: transpose the square under the two composite extension/pullback adjunctions.
The source and target coordinate maps are the mates of the prescribed direct-image
and open-restriction comparisons. Mates commute with composition, so the transposed
square compares the cartesian right exchange before and after scalar restriction.
For the finite exchange, conjugate the two module pullback compositors: their
conjugates are the prescribed direct-image compositors. Equality transport commutes
with conjugation by equality induction. Thus the conjugate of moduleSquareG.inv is
moduleRComp for j-prime,g, followed by transport across the square equation and
moduleRComp for gU,j inverted. The defining section formula for moduleRComp, its
inverse identity, and presheaf functoriality identify this with restriction along
the pullback-pasting site isomorphism. The open-unit formula defining singleBetaInv
and the mates pasting law then give the finite right exchange used in this square.
The direct-image comparison is identity on sections. The open-restriction comparison
sends a pullback-unit generator along the adjoint site arrow. On such a generator,
both composites therefore restrict the original section along the same cartesian
comparison V times_U U' to V times_X X'. The projection equations identify the scalar
actions. These distinguished unit generators cover all sections: their image under
the normalized open-restriction isomorphism is the original section, and applying
its inverse expresses any section in this form. Sectionwise extensionality therefore
proves the right square. Injectivity of the mates equivalence proves the displayed left
square. This uses arbitrary finite-coefficient modules; no complexes, resolutions,
completeness, quasi-compactness, or inverse limits enter. -/
theorem cbcFiniteScalarExchange_inverse (n : ℕ)
    (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) U) :
    (cbcFiniteTargetRes d sq n).hom.app M ≫
      (cbcFiniteRes d X' n).map
        ((@singleBetaInv.{u} (cbcFiniteRing d n) _ U' U X' X gU j' j g
          sq.isOpenImmersion sq.isOpenImmersion' sq.w).app M) =
    (cbcUnderivedInverseExchange d sq).app ((cbcFiniteRes d U n).obj M) ≫
      (cbcFiniteSourceRes d sq n).hom.app M := by
  let := sq.isOpenImmersion
  let := sq.isOpenImmersion'
  let B := cbcFiniteRing d n
  let a := (moduleJAdj B j).comp (openBetaModuleAdj B g)
  let b := (openBetaModuleAdj B gU).comp (moduleJAdj B j')
  let c := (cbcOpenAdjunction d j sq.isOpenImmersion).comp
    (cbcModulePullbackAdjunction d g)
  let e := (cbcModulePullbackAdjunction d gU).comp
    (cbcOpenAdjunction d j' sq.isOpenImmersion')
  let q := (TwoSquare.mk _ _ _ _ (cbcFiniteOpenRes d j sq.isOpenImmersion n)).vComp
    (TwoSquare.mk _ _ _ _ (cbcFinitePullRes d g n))
  let r := (TwoSquare.mk _ _ _ _ (cbcFinitePullRes d gU n)).vComp
    (TwoSquare.mk _ _ _ _ (cbcFiniteOpenRes d j' sq.isOpenImmersion' n))
  have h : q.whiskerRight (cbcUnderivedInverseExchange d sq) =
      r.whiskerLeft (singleBetaInv B gU j' j g sq.w) := by
    apply mates_square a b c e
    dsimp only [a, b, c, e, q, r]
    rw [mateEquiv_hcomp, mateEquiv_hcomp]
    have hp {S T : Scheme.{u}} (f : S ⟶ T) :
        mateEquiv (openBetaModuleAdj B f) (cbcModulePullbackAdjunction d f)
          (TwoSquare.mk _ _ _ _ (cbcFinitePullRes d f n)) =
        TwoSquare.mk _ _ _ _ (cbcFiniteDirectRes d f n).hom := by
      exact (mateEquiv (openBetaModuleAdj B f) (cbcModulePullbackAdjunction d f))
        |>.apply_symm_apply (TwoSquare.mk _ _ _ _ (cbcFiniteDirectRes d f n).hom)
    have ho {S T : Scheme.{u}} (f : S ⟶ T) (hf : IsOpenImmersion f) :
        mateEquiv (@moduleJAdj B _ S T f hf) (cbcOpenAdjunction d f hf)
          (TwoSquare.mk _ _ _ _ (cbcFiniteOpenRes d f hf n)) =
        TwoSquare.mk _ _ _ _ (cbcFiniteOpenRestriction d f hf n).hom := by
      exact (mateEquiv (@moduleJAdj B _ S T f hf) (cbcOpenAdjunction d f hf))
        |>.apply_symm_apply (TwoSquare.mk _ _ _ _ (cbcFiniteOpenRestriction d f hf n).hom)
    erw [hp g, hp gU, ho j sq.isOpenImmersion, ho j' sq.isOpenImmersion']
    have hc : conjugateEquiv c e (cbcUnderivedInverseExchange d sq) =
        cbcRightExchange d sq := Equiv.apply_symm_apply _ _
    have hn := (openBetaModule_normalized B gU j' j g sq.w
      (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)).1
    change conjugateEquiv a b (singleBetaInv B gU j' j g sq.w) = _ at hn
    erw [hc, hn]
    apply TwoSquare.ext
    intro N
    simpa only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc, B] using
      right_exchange_square d sq n N
  have hM := congrArg (fun z ↦ z.app M) h
  simpa only [q, r, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.vComp, TwoSquare.mk, cbcFiniteSourceRes, cbcFiniteTargetRes,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, asIso_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, B] using hM.symm

end AlgebraicGeometry.Scheme
