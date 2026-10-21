/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Double counits in an etale-horizontal square

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md, Step 1;
Stacks Project, Tags 0037, 0DV0, 0F7J, 0F7K, 0F7L and 03S6
(blueprint: lem-pur-etale-horizontal-double-counit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar etaleLowerShriek
  Functor.mapDerivedCategory derivedEtaleLowerShriekUpperStarAdjunction

/-- The right-adjoint restriction comparison determined by inverse compact-support exchange.
Source: Stacks Project, Tags 0037 and 0F7L
(blueprint: lem-pur-etale-horizontal-double-counit). -/
noncomputable def etaleHorizontalCounitRightExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {h : X ⟶ Y} {h' : X' ⟶ Y'} {e : Y' ⟶ Y} {e' : X' ⟶ X}
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification h] [HasCompactification h'] [QuasiCompact h']
    (sq : IsPullback e' h' h e)
    {G : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
    {G' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X'}
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h ⊣ G)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h' ⊣ G') :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙ G' :=
  (mateEquiv adj adj'
    (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A sq).inv)).natTrans

private lemma conjugate_transport
    {C D : Type*} [Category* C] [Category* D]
    {L L' F : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (i : L ≅ F) (j : L' ≅ F) (t : L' ≅ L)
    (ht : t.hom ≫ i.hom = j.hom) :
    conjugateEquiv a b t.hom =
      conjugateEquiv (a.ofNatIsoLeft i) (b.ofNatIsoLeft j) (𝟙 F) := by
  ext K
  apply ((b.ofNatIsoLeft j).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, NatTrans.id_app, Category.id_comp]
  rw [← Category.assoc, j.inv.naturality]
  simp only [Category.assoc]
  rw [conjugateEquiv_counit, ← Category.assoc]
  have he : j.inv ≫ t.hom = i.inv := by
    apply (cancel_mono i.hom).1
    simp [Category.assoc, ht]
  exact congrArg (fun z ↦ z.app (R.obj K) ≫ a.counit.app K) he

private lemma mate_change_right_adjoints
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R S : D ⥤ C} {L' : E ⥤ F} {R' S' : F ⥤ E}
    (a : L ⊣ R) (b : L ⊣ S) (a' : L' ⊣ R') (b' : L' ⊣ S')
    {U : C ⥤ E} {V : D ⥤ F} (α : TwoSquare U L L' V) :
    Functor.whiskerRight (conjugateEquiv a b (𝟙 L)) U ≫
        (mateEquiv b b' α).natTrans =
      (mateEquiv a a' α).natTrans ≫
        Functor.whiskerLeft V (conjugateEquiv a' b' (𝟙 L')) := by
  have h₁ := conjugateEquiv_mateEquiv_vcomp a b b' (𝟙 L) α
  have h₂ := mateEquiv_conjugateEquiv_vcomp a a' b' α (𝟙 L')
  have hh : α.whiskerLeft (𝟙 L) = α.whiskerRight (𝟙 L') := by
    ext K
    simp
  rw [hh, h₂] at h₁
  exact (congrArg TwoSquare.natTrans h₁).symm

private lemma mate_top
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {U U' : C ⥤ E} {V : D ⥤ F}
    (α : TwoSquare U' L L' V) (t : U ⟶ U') (K : D) :
    (mateEquiv a b (α.whiskerTop t)).app K =
      t.app (R.obj K) ≫ (mateEquiv a b α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_bottom
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {U : C ⥤ E} {V V' : D ⥤ F}
    (α : TwoSquare U L L' V) (t : V ⟶ V') (K : D) :
    (mateEquiv a b (α.whiskerBottom t)).app K =
      (mateEquiv a b α).app K ≫ R'.map (t.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, t.naturality]

private lemma mate_cube
    {C₀ D₀ C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
    [Category* C₀] [Category* D₀] [Category* C₁] [Category* D₁]
    [Category* C₂] [Category* D₂] [Category* C₃] [Category* D₃]
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂} {L₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    {U₀₁ : C₀ ⥤ C₁} {V₀₁ : D₀ ⥤ D₁} {U₁₃ : C₁ ⥤ C₃} {V₁₃ : D₁ ⥤ D₃}
    {U₀₂ : C₀ ⥤ C₂} {V₀₂ : D₀ ⥤ D₂} {U₂₃ : C₂ ⥤ C₃} {V₂₃ : D₂ ⥤ D₃}
    (α : TwoSquare U₀₁ L₀ L₁ V₀₁) (β : TwoSquare U₁₃ L₁ L₃ V₁₃)
    (γ : TwoSquare U₀₂ L₀ L₂ V₀₂) (δ : TwoSquare U₂₃ L₂ L₃ V₂₃)
    (s : U₀₁ ⋙ U₁₃ ≅ U₀₂ ⋙ U₂₃) (t : V₀₁ ⋙ V₁₃ ≅ V₀₂ ⋙ V₂₃)
    (hc : α.hComp β = ((γ.hComp δ).whiskerTop s.hom).whiskerBottom t.inv) :
    Functor.whiskerRight (mateEquiv a₀ a₁ α).natTrans U₁₃ ≫
        Functor.whiskerLeft V₀₁ (mateEquiv a₁ a₃ β).natTrans =
      Functor.whiskerLeft R₀ s.hom ≫
        Functor.whiskerRight (mateEquiv a₀ a₂ γ).natTrans U₂₃ ≫
        Functor.whiskerLeft V₀₂ (mateEquiv a₂ a₃ δ).natTrans ≫
        Functor.whiskerRight t.inv R₃ := by
  ext K
  have hh := congrArg (fun q ↦ (mateEquiv a₀ a₃ q).app K) hc
  rw [mate_bottom, mate_top, mateEquiv_vcomp, mateEquiv_vcomp] at hh
  simpa only [TwoSquare.vComp_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc] using hh

private noncomputable def pullComp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (upperStar (ModuleCat.{u + 1} A) fg).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  Functor.mapDerivedCategoryTriangleIso
    (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg)

private lemma support_paste_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    {dX : X'' ⟶ X} {dY : Y'' ⟶ Y}
    (hx : dX = w' ≫ v') (hy : dY = w ≫ v)
    (sq₃ : IsPullback dX f'' f dY) (M : DerivedCategoryModule A X) :
    (etaleHorizontalSupportBaseChangeIso A sq₃).inv.app M =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'').map
          ((pullComp A w' v' dX hx).hom.app M) ≫
        (etaleHorizontalSupportBaseChangeIso A sq₂).inv.app
          ((upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory.obj M) ≫
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map
          ((etaleHorizontalSupportBaseChangeIso A sq₁).inv.app M) ≫
        (pullComp A w v dY hy).inv.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) := by
  subst hx hy
  have hi : etaleHorizontalSupportBaseChangeIso A sq₃ =
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
          (pullComp A w v (w ≫ v) rfl) ≪≫
        Functor.isoWhiskerRight (etaleHorizontalSupportBaseChangeIso A sq₁)
          (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory
          (etaleHorizontalSupportBaseChangeIso A sq₂) ≪≫
        Functor.isoWhiskerRight (pullComp A w' v' (w' ≫ v') rfl).symm
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'') := by
    apply Iso.ext
    ext K
    have hh := congr_app (unboundedEtaleCompactSupport_baseChange_comp A sq₁ sq₂ sq₃) K
    simpa only [etaleHorizontalSupportBaseChangeIso, asIso_hom,
      pullComp, Functor.mapDerivedCategoryTriangleIso,
      unboundedEtaleUpperStarCompIso, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom, Category.assoc] using hh
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_inv, Category.assoc] using congrArg (fun i ↦ i.inv.app M) hi

section Square

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X X' Y Y' : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
  {h : X ⟶ Y} {h' : X' ⟶ Y'} {e : Y' ⟶ Y} {e' : X' ⟶ X}
  [IsSeparated h] [IsSeparated h'] [IsSeparated e] [IsSeparated e']
  [Etale e] [Etale e']
  [LocallyOfFiniteType h] [LocallyOfFiniteType h']
  [QuasiCompact h] [QuasiCompact h'] [QuasiCompact e] [QuasiCompact e']
  [HasCompactification h] [HasCompactification h']
  [HasCompactification e] [HasCompactification e']
  [HasCompactification (e' ≫ h)] [HasCompactification (h' ≫ e)]
  (sq : ChosenCartesianSquare e' h' h e) (N : EtaleCompactSupportNormalization A)
  {G : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
  {G' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X'}
  (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h ⊣ G)
  (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h' ⊣ G')

/-- Conjugate the specified inverse delta under the two normalized composite adjunctions.
This is the map b of the node; the compositor formula is recorded below.
Source: Stacks Project, Tags 0037 and 0DV0
(blueprint: lem-pur-etale-horizontal-double-counit). -/
noncomputable def etaleHorizontalDoubleCounitIso :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙ G' :=
  conjugateIsoEquiv
    ((derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e' inferInstance).comp adj)
    (adj'.comp (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance))
    (etaleHorizontalSupportMateDelta A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) N).symm

set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
/-- Double-counit equality, single-counit equality, and the unique adjunct description.
Source: blueprint co-smooth etale locality, Step 1; Stacks 0037, 0DV0 and 0F7K
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: (1) conjugacy of d inverse preserves the evaluation/counit normalization.
(2) Conjugate the difference of the two compositors, using contravariant composition.
(3) Change from the compact-support adjunctions to the sum/evaluation adjunctions;
mate pasting identifies the resulting conjugate with b and the left map with delta inverse.
(4) Expand both composite counits by Adjunction.comp to obtain the first equality.
(5) Apply lem-pur-etale-horizontal-support-mate at G K and use counit naturality.
(6) Cancel the inverse hom bijection for the sum adjunction, obtaining the second
identity. The hom bijection for adj' gives the unique adjunct assertion.
(7) Refinement comparisons preserve d and the compositors; conjugacy preserves their
counits, so the identities transport under refinement.
(8) Exchange pasting and lem-pur-etale-support-map-compatibility identify the two
restricted mates; the sum/evaluation adjunction is the same after open restriction.
No evaluation counit is cancelled as an isomorphism. -/
theorem etaleHorizontalDoubleCounit :
    ∀ K : DerivedCategoryModule A Y,
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
              ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
            adj'.counit.app
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).counit.app K =
      (etaleHorizontalSupportMateDelta A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) N).inv.app
          ((upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory.obj (G.obj K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e' inferInstance).counit.app (G.obj K)) ≫
        adj.counit.app K) ∧
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
          ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
        adj'.counit.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) =
      (etaleHorizontalSupportBaseChangeIso A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd)).inv.app (G.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map (adj.counit.app K)) ∧
      (adj'.homEquiv _ _
        ((etaleHorizontalSupportBaseChangeIso A
          (IsPullback.of_iso_pullback sq.toCommSq
            sq.isoPullback sq.hom_fst sq.hom_snd)).inv.app (G.obj K) ≫
          (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
            (adj.counit.app K)) =
        (etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) := by
  intro K
  let ae := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance
  let ae' := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e' inferInstance
  let p := IsPullback.of_iso_pullback sq.toCommSq
    sq.isoPullback sq.hom_fst sq.hom_snd
  have hd : ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
              ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
            adj'.counit.app
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).counit.app K =
      (etaleHorizontalSupportMateDelta A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) N).inv.app
          ((upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory.obj (G.obj K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e' inferInstance).counit.app (G.obj K)) ≫
        adj.counit.app K) := by
    simpa only [etaleHorizontalDoubleCounitIso, conjugateIsoEquiv_apply_hom,
      ae, ae', p, Iso.symm_hom, Adjunction.comp_counit_app, Functor.comp_obj,
      Functor.comp_map,
      Functor.map_comp, Category.assoc] using
      conjugateEquiv_counit (ae'.comp adj) (adj'.comp ae)
        (etaleHorizontalSupportMateDelta A p N).inv K
  have hs : ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
          ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
        adj'.counit.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) =
      (etaleHorizontalSupportBaseChangeIso A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd)).inv.app (G.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map (adj.counit.app K)) := by
    apply (ae.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hd]
    rw [← Category.assoc, etaleHorizontalSupportMate A p N (G.obj K)]
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    exact (ae.counit.naturality (adj.counit.app K)).symm
  refine ⟨hd, hs, ?_⟩
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact hs.symm

set_option linter.unusedSectionVars false in
/-- The explicit formula rho inverse, inverse first conjugate compositor, second
conjugate compositor, and rho. A common right adjoint for the equal composites is
arbitrary, and both occurrences use the same adjunction.
Source: Stacks 0037 and 0DV0, blueprint co-smooth etale locality Step 1
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: conjugate alpha for each composite adjunction. Contravariance identifies the
middle two factors with the conjugate of alpha_h inverse after alpha_e. Mate pasting
moves d_e inverse and d_e' across the composite adjunctions. These are exactly rho_e
and rho_e' inverse, respectively, giving the defining conjugate of delta inverse. -/
theorem etaleHorizontalDoubleCounit_compositors
    {Ge : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A Y'}
    {Ge' : DerivedCategoryModule A X ⥤ DerivedCategoryModule A X'}
    {Gd : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X'}
    (ae : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ Ge)
    (ae' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e' ⊣ Ge')
    (ad : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e' ≫ h) ⊣ Gd) :
    etaleHorizontalDoubleCounitIso A sq N adj adj' =
      Functor.isoWhiskerLeft G
        (conjugateIsoEquiv ae'
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e' inferInstance)
          (etaleCanonicalCompactSupportComparison A e' N).symm).symm ≪≫
      (conjugateIsoEquiv ad (ae'.comp adj)
        (unboundedEtaleLowerShriekCompIso A e' h)).symm ≪≫
      conjugateIsoEquiv ad (adj'.comp ae)
        (unboundedEtaleLowerShriekCompIso A h' e ≪≫
          (unboundedEtaleLowerShriekCongr A sq.toCommSq.w).symm) ≪≫
      Functor.isoWhiskerRight
        (conjugateIsoEquiv ae
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance)
          (etaleCanonicalCompactSupportComparison A e N).symm) G' := by
  apply Iso.ext
  simp only [etaleHorizontalDoubleCounitIso, Iso.trans_hom, Iso.symm_hom,
    conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_whiskerRight _ _ adj,
    ← conjugateEquiv_whiskerLeft _ _ adj', conjugateEquiv_comp,
    conjugateEquiv_comp, conjugateEquiv_comp]
  congr 1
  simp only [etaleHorizontalSupportMateDelta, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc]

/-- Equality of natural transformations, making naturality in K explicit.
Source: blueprint co-smooth etale locality Step 1 and Stacks 0037
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: the single-counit identity identifies the two transformations under the
adjunction hom bijection, component by component; injectivity gives equality. -/
theorem etaleHorizontalDoubleCounit_exchange :
    (etaleHorizontalDoubleCounitIso A sq N adj adj').hom =
      etaleHorizontalCounitRightExchange A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) adj adj' := by
  ext K
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  exact (etaleHorizontalDoubleCounit A sq N adj adj' K).2.1.trans
    (mateEquiv_counit adj adj'
      (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A
        (IsPullback.of_iso_pullback sq.toCommSq
          sq.isoPullback sq.hom_fst sq.hom_snd)).inv) K).symm

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility with proper-refinement comparisons for both vertical arrows.
The fixed-compactification adjunctions are transported to the shared compact-support
functor, and the right comparisons are conjugates of the inverse refinement maps.
Source: Stacks 0F7I, 0F7J, 0F7K and 0GKM
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: the comparison cocycle identifies the common-refinement isomorphism with the
specified refinement map. Its conjugate preserves the counit. Substitute the refinement
identities for d and alpha into delta; adjacent comparison inverses cancel. Conjugacy
then gives the displayed square, independently of either normalization family. -/
theorem etaleHorizontalDoubleCounit_refinement
    (M : EtaleCompactSupportNormalization A)
    (c d : Compactification h) (_r : c.Refinement d)
    (c' d' : Compactification h') (_r' : c'.Refinement d')
    {H : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
    {H' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X'}
    (ac : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (ad : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H)
    (ac' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c' ⊣ G')
    (ad' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d' ⊣ H') :
    Functor.whiskerRight
        (conjugateIsoEquiv ac ad
          (rightDerivedLowerShriekOfCompactificationIso A d c)).hom
        (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ≫
      (etaleHorizontalDoubleCounitIso A sq M
        (ad.ofNatIsoLeft (rightDerivedLowerShriekIso A d))
        (ad'.ofNatIsoLeft (rightDerivedLowerShriekIso A d'))).hom =
    (etaleHorizontalDoubleCounitIso A sq N
        (ac.ofNatIsoLeft (rightDerivedLowerShriekIso A c))
        (ac'.ofNatIsoLeft (rightDerivedLowerShriekIso A c'))).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
        (conjugateIsoEquiv ac' ad'
          (rightDerivedLowerShriekOfCompactificationIso A d' c')).hom := by
  rw [etaleHorizontalDoubleCounit_exchange, etaleHorizontalDoubleCounit_exchange]
  let ic := rightDerivedLowerShriekIso A c
  let id := rightDerivedLowerShriekIso A d
  let ic' := rightDerivedLowerShriekIso A c'
  let id' := rightDerivedLowerShriekIso A d'
  have ht := (unboundedEtaleCompactSupport_comparison_coherence A h).2
    d c (HasCompactification.compactification h)
  have ht' := (unboundedEtaleCompactSupport_comparison_coherence A h').2
    d' c' (HasCompactification.compactification h')
  have hc := conjugate_transport ac ad ic id
    (rightDerivedLowerShriekOfCompactificationIso A d c) (by
      simpa only [Iso.trans_hom, ic, id, rightDerivedLowerShriekIso] using
        congrArg Iso.hom ht)
  have hc' := conjugate_transport ac' ad' ic' id'
    (rightDerivedLowerShriekOfCompactificationIso A d' c') (by
      simpa only [Iso.trans_hom, ic', id', rightDerivedLowerShriekIso] using
        congrArg Iso.hom ht')
  simp only [conjugateIsoEquiv_apply_hom]
  rw [hc, hc']
  exact mate_change_right_adjoints
    (ac.ofNatIsoLeft ic) (ad.ofNatIsoLeft id)
    (ac'.ofNatIsoLeft ic') (ad'.ofNatIsoLeft id')
    (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A
      (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd)).inv)

/-- The comparison square for a further compatible Cartesian open restriction.
The vertical restriction maps on right adjoints are exactly the mates of inverse
compact-support exchange, with the same evaluation normalization as the original b.
Source: Stacks 0F7L and 03S6, blueprint co-smooth etale locality Step 1
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: write the two pasted inverse-exchange squares for the Cartesian cube. They agree
by compatibility of compact-support exchange with successive changes of base. Apply mate
pasting to their equality. The single-counit identity identifies the horizontal mates
with b and its restriction, while the vertical mates are the specified restriction maps.
The canonical inverse-image square isomorphisms give the two remaining factors. The
sum/evaluation normalization is preserved by degreewise open restriction, since both
operations evaluate the same restricted lift; support-map compatibility identifies d.
Thus the double and single counit identities transport along this comparison square. -/
theorem etaleHorizontalDoubleCounit_openRestriction
    {V V' W W' : Scheme.{u}}
    [IsNoetherian V] [IsNoetherian V'] [IsNoetherian W] [IsNoetherian W']
    {k : V ⟶ W} {k' : V' ⟶ W'} {v : W' ⟶ W} {v' : V' ⟶ V}
    [IsSeparated k] [IsSeparated k'] [IsSeparated v] [IsSeparated v']
    [Etale v] [Etale v'] [LocallyOfFiniteType k] [LocallyOfFiniteType k']
    [QuasiCompact k] [QuasiCompact k'] [QuasiCompact v] [QuasiCompact v']
    [HasCompactification k] [HasCompactification k']
    [HasCompactification v] [HasCompactification v']
    [HasCompactification (v' ≫ k)] [HasCompactification (k' ≫ v)]
    (barsq : ChosenCartesianSquare v' k' k v)
    (jX : V ⟶ X) (jX' : V' ⟶ X') (jY : W ⟶ Y) (jY' : W' ⟶ Y')
    [IsOpenImmersion jX] [IsOpenImmersion jX']
    [IsOpenImmersion jY] [IsOpenImmersion jY']
    (leftsq : IsPullback jX k h jY) (rightsq : IsPullback jX' k' h' jY')
    (topsq : CommSq v' jX' jX e') (bottomsq : CommSq v jY' jY e)
    {H : DerivedCategoryModule A W ⥤ DerivedCategoryModule A V}
    {H' : DerivedCategoryModule A W' ⥤ DerivedCategoryModule A V'}
    (a : rightDerivedLowerShriek (ModuleCat.{u + 1} A) k ⊣ H)
    (a' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) k' ⊣ H') :
    Functor.whiskerRight (etaleHorizontalDoubleCounitIso A sq N adj adj').hom
        (upperStar (ModuleCat.{u + 1} A) jX').mapDerivedCategory ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
        (etaleHorizontalCounitRightExchange A rightsq adj' a') =
    Functor.whiskerLeft G
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) topsq).hom ≫
      Functor.whiskerRight (etaleHorizontalCounitRightExchange A leftsq adj a)
        (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) jY).mapDerivedCategory
        (etaleHorizontalDoubleCounitIso A barsq N a a').hom ≫
      Functor.whiskerRight
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) bottomsq).inv H' := by
  rw [etaleHorizontalDoubleCounit_exchange, etaleHorizontalDoubleCounit_exchange]
  let p := IsPullback.of_iso_pullback sq.toCommSq
    sq.isoPullback sq.hom_fst sq.hom_snd
  let q := IsPullback.of_iso_pullback barsq.toCommSq
    barsq.isoPullback barsq.hom_fst barsq.hom_snd
  let α := TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A p).inv
  let β := TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A rightsq).inv
  let γ := TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A leftsq).inv
  let δ := TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A q).inv
  let s := exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) topsq
  let t := exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) bottomsq
  let sx := pullComp A jX' e' (v' ≫ jX) topsq.w
  let sy := pullComp A v' jX (v' ≫ jX) rfl
  let tx := pullComp A jY' e (v ≫ jY) bottomsq.w
  let ty := pullComp A v jY (v ≫ jY) rfl
  have hs : s = sx.symm ≪≫ sy := by
    apply Iso.ext
    simp [s, sx, sy, exactDerivedSquareUpperStarIso, squareUpperStarIso,
      pullComp, Functor.mapDerivedCategoryTriangleIso,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm]
  have ht : t = tx.symm ≪≫ ty := by
    apply Iso.ext
    simp [t, tx, ty, exactDerivedSquareUpperStarIso, squareUpperStarIso,
      pullComp, Functor.mapDerivedCategoryTriangleIso,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm]
  have hc : α.hComp β = ((γ.hComp δ).whiskerTop s.hom).whiskerBottom t.inv := by
    ext M
    have h₁ := support_paste_inv A p rightsq topsq.w bottomsq.w
      (q.paste_horiz leftsq) M
    have h₂ := support_paste_inv A leftsq q rfl rfl (q.paste_horiz leftsq) M
    simp only [TwoSquare.hComp_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerTop_app, α, β, γ, δ, TwoSquare.mk, TwoSquare.natTrans]
    apply (cancel_epi ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) k').map
      (sx.hom.app M))).1
    apply (cancel_mono (tx.inv.app
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).obj M))).1
    simp only [hs, ht, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id_app, Category.comp_id]
    simpa only [sx, sy, tx, ty, Category.assoc] using h₁.symm.trans h₂
  exact mate_cube adj adj' a a' α β γ δ s t hc

end Square

end AlgebraicGeometry.Etale
