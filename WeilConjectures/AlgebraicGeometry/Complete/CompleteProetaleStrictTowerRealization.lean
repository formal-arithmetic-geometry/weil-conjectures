/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenStrictMateIdentification
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerScalarPushLimitCoherence
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization

/-! # Strict-tower realization of the ordered completed proper/open composite

Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc, Definition 1939;
Stacks 03DI, 09BP, 0A07.
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.StrictTower
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

private theorem cbcRealizationConstantPush_map {V W : Scheme.{t}} (u : V ⟶ W)
    {M N : ProEtale.StrictTower.Derived A V} (x : M ⟶ N) :
    (exchangeConstantPush (A := A) u).map x = (ProEtale.StrictTower.R A u).map x := by
  rfl

private theorem cbcRealizationConstantPull_map {V W : Scheme.{t}} (u : V ⟶ W)
    {M N : ProEtale.StrictTower.Derived A W} (x : M ⟶ N) :
    (exchangeConstantPull (A := A) u).map x = (ProEtale.StrictTower.G A u).map x := by
  rfl

private theorem cbcRealizationCombine
    {C C₀ D D₀ E E₀ H H₀ : Type*}
    [Category C] [Category C₀] [Category D] [Category D₀]
    [Category E] [Category E₀] [Category H] [Category H₀]
    (S : C ⥤ D) (S₀ : C₀ ⥤ D₀) (L : C ⥤ E) (L₀ : C₀ ⥤ E₀)
    (L' : D ⥤ H) (L₀' : D₀ ⥤ H₀) (U : E ⥤ H) (U₀ : E₀ ⥤ H₀)
    (P : E₀ ⥤ E) (T : C₀ ⥤ C) (P' : H₀ ⥤ H) (T' : D₀ ⥤ D)
    (lam : L ⋙ U ≅ S ⋙ L') (lam₀ : L₀ ⋙ U₀ ≅ S₀ ⋙ L₀')
    (c : L₀ ⋙ P ≅ T ⋙ L) (c' : L₀' ⋙ P' ≅ T' ⋙ L')
    (d : P ⋙ U ≅ U₀ ⋙ P') (dt : T ⋙ S ≅ S₀ ⋙ T')
    {Q : C₀} {B : C} {N N' : D₀} {V : D} {Z : E} {W : E₀}
    (x : Z ⟶ L.obj B) (h : B ⟶ T.obj Q) (v : L₀.obj Q ⟶ W)
    (a : S₀.obj Q ⟶ N) (b : S.obj B ⟶ V) (e : V ⟶ T'.obj N)
    (beta : N ⟶ N') (o : L₀'.obj N' ⟶ U₀.obj W)
    (hc : U.map (c.hom.app Q) ≫ lam.hom.app (T.obj Q) ≫ L'.map (dt.hom.app Q) =
      d.hom.app (L₀.obj Q) ≫ P'.map (lam₀.hom.app Q) ≫ c'.hom.app (S₀.obj Q))
    (hh : S.map h ≫ dt.hom.app Q ≫ T'.map a = b ≫ e)
    (hv : U₀.map v = lam₀.hom.app Q ≫ L₀'.map a ≫ L₀'.map beta ≫ o) :
    U.map (x ≫ L.map h ≫ c.inv.app Q ≫ P.map v) =
      (U.map x ≫ lam.hom.app B ≫ L'.map b) ≫
        L'.map (e ≫ T'.map beta) ≫ c'.inv.app N' ≫ P'.map o ≫ d.inv.app W := by
  have hi : U.map (c.inv.app Q) ≫ d.hom.app (L₀.obj Q) ≫
      P'.map (lam₀.hom.app Q) =
      lam.hom.app (T.obj Q) ≫ L'.map (dt.hom.app Q) ≫ c'.inv.app (S₀.obj Q) := by
    apply (cancel_epi (U.map (c.hom.app Q))).1
    simp only [← U.map_comp_assoc, Iso.hom_inv_id_app, U.map_id, Category.id_comp]
    rw [reassoc_of% hc]
    simp only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  apply (cancel_mono (d.hom.app W)).1
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app,
    Functor.comp_obj, Category.comp_id]
  have hn := d.hom.naturality v
  dsimp only [Functor.comp_map] at hn
  rw [hn, hv]
  simp only [Functor.map_comp]
  rw [reassoc_of% hi]
  have hl := lam.hom.naturality h
  dsimp only [Functor.comp_map] at hl
  rw [reassoc_of% hl]
  have ha := c'.inv.naturality a
  have hb := c'.inv.naturality beta
  dsimp only [Functor.comp_map] at ha hb
  rw [← reassoc_of% ha, ← reassoc_of% hb]
  simp only [← L'.map_comp_assoc]
  rw [reassoc_of% hh]

/-- The ordered open-factor formula uses the already defined beta and normalized limit mate.
Source: blueprint Definition 1939; Stacks 03DI and 09BP
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof: scalar restriction preserves the open unit and its transpose, on whole strict
complexes, hence preserves beta before evaluation. The finite-reduction comparisons
respect every quotient transition. Apply Rlim to this beta and then the inverse
canonical extension/limit comparison. The exact-product strict-limit theorem identifies
that comparison with cbcRealizationOpenLimit, with its resolution and augmentation
normalizations. The resulting map obeys the ordinary-exchange/completion-unit equation
of cbcDatumCompletedExchange. Completeness and that definition's uniqueness identify
the maps. Both displayed endpoints use the same finite reduction and scalar transports. -/
theorem completeProetaleStrictTowerRealization_open [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :
    (cbcRealizationRes d c'.Z).mapDerivedCategory.map
        (cbcRealizationOpenFactor d c c' gbar sj r a ha K) =
      (cbcRealizationOpenSource d c c' gbar K.obj).hom ≫
        (completedRlim c'.Z (exchangeConstantRing c'.Z A)).map
          ((ProEtale.StrictTower.beta A g' c'.i c.i gbar sj.w
            (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app
              ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K.obj))) ≫
        (cbcRealizationOpenTarget d c' g' (qc := cbcRealizationOpenQC c c' gbar sj) K.obj).hom := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hc := ((completedOpenExchangeComparison d sj r a ha).2 K).1
  have h := (completedOpenStrictMateIdentification d sj r a ha K hc).2.1
  have hh := congrArg (fun z ↦ z ≫
    (cbcOpenMateCompletedB d (j' := c'.i) (v := g') K.obj).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh
  simpa only [cbcRealizationOpenFactor, cbcRealizationOpenSource,
    cbcRealizationOpenTarget, cbcOpenMateCompletedA, cbcOpenMateCompletedB,
    cbcOpenMateBeta, cbcOpenMateM, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
    Functor.comp_obj, Category.assoc] using hh

/-- The ordered completed compact-support exchange is the image of the actual
strict-tower composite under the specified, normalized source and target comparisons.
All isomorphisms in the statement are the definitions above; none is an existential
isomorphism of endpoints. The theorem's naturality and evaluation clauses follow below.

Source: blueprint main-20261015, Definition 1939 and proof of thm-cbc-complete-proetale
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
Proof:
1. The completed-open comparison supplies completeness of the extended input.
   The specified strict-open mate identification, followed by cancellation of
   its target comparison, gives the open-factor formula above.
2. The existing completedExchange_mate and restrictedExchange_mate identities
   normalize the actual proper factor on the whole strict tower. Naturality of
   that mate moves the quotient/open comparison to its source corner.
3. Apply strictTowerScalarPushLimitCoherence to the pullback of the completed
   reduction tower of j!K. This is the normalized scalar/direct-image/limit square.
4. The private categorical lemma cbcRealizationCombine cancels the scalar/limit
   comparison and moves the open factor through direct image by naturality.
   Substitute the proper and open formulas, then use functoriality of Rlim.
5. Unfolding the specified endpoint comparisons gives the displayed identity.
   The evaluation and naturality identities in the comparison module concern
   these same maps. No faithfulness of evaluation is used. -/
theorem completeProetaleStrictTowerRealization [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj)
    (_completeOpen : cbcCompleteProperty d c.Z r a ha
      ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K.obj)) :
    (cbcRealizationRes d Y').mapDerivedCategory.map
        (completedCompactSupportExchange d c c' gbar sp sj r a ha K) =
      (cbcRealizationSource d c c' gbar (g := g) K.obj).hom ≫
        (completedRlim Y' (exchangeConstantRing Y' A)).map
          (cbcRealizationStrict (A := A) c c' gbar sp sj
            ((exchangeTowerRes d X).obj ((completedReductionTower X d).obj K.obj))) ≫
        (cbcRealizationTarget d c' g' (qc := cbcRealizationOpenQC c c' gbar sj) K.obj).hom := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  let : QuasiCompact c'.i := cbcRealizationOpenQC c c' gbar sj
  let F := (cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K.obj
  let RF := (completedReductionTower c.Z d).obj F
  let M := (exchangeTowerRes d X).obj ((completedReductionTower X d).obj K.obj)
  let q := cbcRealizationQuotientOpen d c.i K.obj
  let Q := (d.towerPull gbar).obj RF
  let aa := (exchangeResPull d gbar).hom.app RF ≫
    (ProEtale.StrictTower.G A gbar).map q.hom
  let bb := (exchangeCornerB d c.g g).hom.app RF ≫
    (ProEtale.StrictTower.G A g).map ((ProEtale.StrictTower.R A c.g).map q.hom)
  let ee := (exchangeConstantSquare (A := A) sp).exchangeTowerMate
  let be := (ProEtale.StrictTower.beta A g' c'.i c.i gbar sj.w
    (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app M
  have hh : (exchangeTowerRes d Y').map (d.towerV' sp F) ≫
      (exchangeResPush d c'.g).hom.app Q ≫
      (ProEtale.StrictTower.R A c'.g).map aa = bb ≫ ee.app _ := by
    have h := restrictedExchange_mate d sp RF
    rw [← completedExchange_mate d sp F] at h
    have hn := ee.naturality q.hom
    dsimp only [Functor.comp_map] at hn
    have ht := congrArg (fun z ↦ z ≫
      (ProEtale.StrictTower.R A c'.g).map
        ((ProEtale.StrictTower.G A gbar).map q.hom)) h
    dsimp only [exchangeCornerD, Iso.trans_hom, NatTrans.comp_app,
      Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app] at ht
    simp only [Category.id_comp, Category.comp_id, Category.assoc,
      cbcRealizationConstantPush_map] at ht
    have hn' : ee.app ((exchangeTowerRes d c.Z).obj RF) ≫
        (ProEtale.StrictTower.R A c'.g).map
          ((ProEtale.StrictTower.G A gbar).map q.hom) =
      (ProEtale.StrictTower.G A g).map ((ProEtale.StrictTower.R A c.g).map q.hom) ≫
        ee.app _ := by
      change (exchangeConstantPull (A := A) g).map
          ((exchangeConstantPush (A := A) c.g).map q.hom) ≫ ee.app _ =
        ee.app _ ≫ (exchangeConstantPush (A := A) c'.g).map
          ((exchangeConstantPull (A := A) gbar).map q.hom) at hn
      simpa only [cbcRealizationConstantPush_map, cbcRealizationConstantPull_map]
        using hn.symm
    have hnat := congrArg (fun z ↦ (exchangeCornerB d c.g g).hom.app RF ≫ z) hn'
    simpa only [aa, bb, Q, Functor.map_comp, Category.assoc,
      AdicCoefficientDatum.integralTowerRingedSquare, AdicCoefficientDatum.fourTowerCorners,
      Matrix.cons_val_zero, Matrix.cons_val_one, RF, F] using
      ht.trans (by simpa only [Category.assoc] using hnat)
  -- Insert the open factor into the scalar/direct-image/limit square.
  have hv : (cbcRealizationRes d c'.Z).mapDerivedCategory.map
      ((cbcDatumCompletedExchange d sj r a ha).app K) =
      (cbcRealizationResLimit d c'.Z).hom.app Q ≫
      (completedRlim c'.Z (exchangeConstantRing c'.Z A)).map aa ≫
      (completedRlim c'.Z (exchangeConstantRing c'.Z A)).map be ≫
      (cbcRealizationOpenTarget d c' g' K.obj).hom := by
    simpa only [cbcRealizationOpenFactor, cbcRealizationOpenSource,
      cbcRealizationPullLimit, Iso.trans_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc, Iso.app_hom, aa, Q, RF, F, be, M, q]
      using completeProetaleStrictTowerRealization_open d c c' gbar sj r a ha K
  have result := cbcRealizationCombine
    (exchangeTowerRes d Y') (exchangeTowerRes d c'.Z)
    (completedRlim Y' (d.completedRing Y')) (completedRlim c'.Z (d.completedRing c'.Z))
    (completedRlim Y' (exchangeConstantRing Y' A))
    (completedRlim c'.Z (exchangeConstantRing c'.Z A))
    (cbcRealizationRes d Y').mapDerivedCategory
    (cbcRealizationRes d c'.Z).mapDerivedCategory
    (d.push c'.g) (d.towerPush c'.g)
    (ProEtale.StrictTower.moduleDirectImage A c'.g).rightDerivedFunctor
    (ProEtale.StrictTower.R A c'.g)
    (cbcRealizationResLimit d Y') (cbcRealizationResLimit d c'.Z)
    (d.directImageRlimIso c'.g) (cbcRealizationPushLimit (A := A) c'.g)
    (cbcRealizationResPush d c'.g) (exchangeResPush d c'.g)
    ((completedRlim Y' (d.completedRing Y')).map
      (d.towerH (f := c.g) (f' := c'.g) (g := g) (g' := gbar) F).hom)
    (d.towerV' sp F) ((cbcDatumCompletedExchange d sj r a ha).app K)
    aa bb (ee.app _) be (cbcRealizationOpenTarget d c' g' K.obj).hom
    (strictTowerScalarPushLimitCoherence d c'.g Q) hh hv
  simpa only [completedCompactSupportExchange, AdicCoefficientDatum.completedExchange,
    cbcRealizationSource, cbcRealizationStrict, cbcRealizationTarget,
    cbcRealizationOpenTarget, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    AdicCoefficientDatum.fourTowerCorners, AdicCoefficientDatum.completedPull,
    Functor.comp_obj, Matrix.cons_val_zero, Matrix.cons_val_one, ObjectProperty.ι_obj,
    aa, bb, ee, be, F, RF, Q, M, q] using result

end AlgebraicGeometry.Scheme
