/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactCompositionProjection.CompositionProjectionData
public import WeilConjectures.AlgebraicGeometry.FiniteSiteTower.FiniteSiteTowerPaste
import all WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientExactClopenComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerNormalization
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteRefinementAmbientNormalization
import WeilConjectures.AlgebraicGeometry.Finite.FiniteSiteWordRefinement
import all WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientOrdinaryClopenLocalization
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization

/-! # Inclusion of a Cartesian proper/open tower into the ambient derived category

Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sf-cartesian-tower-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] properOpenAlpha properOpenBeta
  AmbientClopen.derivedAlpha AmbientClopen.alpha AmbientClopen.beta
  upperStarLowerStarAdjunction openImmersionLowerShriekUpperStarAdjunction
  lowerStar properOpenMate properOpenShriekComp properOpenAdj
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarComp
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  leftDerivedUpperStarIsoMapDerivedCategory AmbientClopen.localizeSquare
  AmbientClopen.localize AmbientClopen.sheafAlpha AmbientClopen.sheafBeta
namespace CartesianTower

variable (A : Type (u + 1)) [CommRing A]

/-- The specified inclusion comparison for the four-factor source word.
Source: the canonical D+ inclusion compatibilities (Stacks 0F7J)
(blueprint: lem-sf-cartesian-tower-restriction). -/
@[irreducible] def sourceInclusion {X V Y B Z : Scheme.{u}}
    (j : X ⟶ V) (q : V ⟶ Y) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i]
    (M : FiniteSiteTower.DP A X) :=
  (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctorPlusCompatibility.app
      ((FiniteSiteTower.JP A i).obj ((FiniteSiteTower.PP A q).obj
        ((FiniteSiteTower.JP A j).obj M))) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.mapIso
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlusCompatibility.app
          ((FiniteSiteTower.PP A q).obj ((FiniteSiteTower.JP A j).obj M)) ≪≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategory.mapIso
          ((lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctorPlusCompatibility.app
              ((FiniteSiteTower.JP A j).obj M) ≪≫
            (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.mapIso
              ((openImmersionLowerShriek
                (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusCompatibility.app M)))

/-- The specified inclusion comparison for the two-factor output word.
Source: the canonical D+ inclusion compatibilities (Stacks 0F7J)
(blueprint: lem-sf-cartesian-tower-restriction). -/
@[irreducible] def targetInclusion {X W Z : Scheme.{u}}
    (j : X ⟶ W) (p : W ⟶ Z) [IsOpenImmersion j]
    (M : FiniteSiteTower.DP A X) :=
  (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app
      ((FiniteSiteTower.JP A j).obj M) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.mapIso
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusCompatibility.app M)

end CartesianTower

private theorem cartesian_mate_adjunct
    {C D H T : Type*} [Category C] [Category D] [Category H] [Category T]
    {Lr : C ⥤ D} {Rr : D ⥤ C} {Lp : H ⥤ T} {Rp : T ⥤ H}
    {Ji : C ⥤ H} {Ki : H ⥤ C} {Jb : D ⥤ T} {Kb : T ⥤ D}
    (ar : Lr ⊣ Rr) (ap : Lp ⊣ Rp) (ai : Ji ⊣ Ki) (ab : Jb ⊣ Kb)
    (a : Ji ⋙ Lp ≅ Lr ⋙ Jb) (σ : Ki ⋙ Lr ≅ Lp ⋙ Kb)
    (hs : (mateEquiv ai ab (TwoSquare.mk _ _ _ _ a.inv)).natTrans = σ.hom)
    (N : D) [IsIso (ab.unit.app N)] :
    ai.homEquiv _ _ ((mateEquiv ar ap (TwoSquare.mk _ _ _ _ a.hom)).natTrans.app N) ≫
      ((mateEquiv ap ar (TwoSquare.mk _ _ _ _ σ.hom)).natTrans.app (Jb.obj N) ≫
        Rr.map (inv (ab.unit.app N))) = 𝟙 _ := by
  let δ := (mateEquiv ab ai (mateEquiv ar ap (TwoSquare.mk _ _ _ _ a.hom))).natTrans
  have hd : δ = (conjugateIsoEquiv (ar.comp ab) (ai.comp ap) a).hom :=
    iterated_mateEquiv_conjugateEquiv ar ap ai ab _
  have he : (mateEquiv ap ar (TwoSquare.mk _ _ _ _ σ.hom)).natTrans =
      (conjugateIsoEquiv (ar.comp ab) (ai.comp ap) a).inv := by
    have ht := iterated_mateEquiv_conjugateEquiv ai ab ar ap
      (TwoSquare.mk _ _ _ _ a.inv)
    have hs' : mateEquiv ai ab (TwoSquare.mk _ _ _ _ a.inv) =
        TwoSquare.mk _ _ _ _ σ.hom := by
      ext M
      exact congr_app hs M
    rw [hs'] at ht
    exact ht
  have hu := unit_mateEquiv ab ai
    (mateEquiv ar ap (TwoSquare.mk _ _ _ _ a.hom)) N
  change Rr.map (ab.unit.app N) ≫ δ.app (Jb.obj N) =
    ai.unit.app (Rr.obj N) ≫ Ki.map
      ((mateEquiv ar ap (TwoSquare.mk _ _ _ _ a.hom)).natTrans.app N) at hu
  rw [Adjunction.homEquiv_unit, ← hu, hd, he]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Rr.map_comp,
    IsIso.hom_inv_id, Rr.map_id]
  rfl

private theorem beta_unit_copy
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (sq : IsPullback k r p i) (M : Sheaf (Scheme.ProEt.topology W) A) :
    (openImmersionLowerShriekUpperStarAdjunction A k).unit.app
        ((upperStar A r).obj M) ≫
      (upperStar A k).map ((AmbientClopen.sheafBeta A r k i p sq.flip).inv.app M) =
    (upperStar A r).map
        ((openImmersionLowerShriekUpperStarAdjunction A i).unit.app M) ≫
      (upperStarCompIso A sq.flip.w).hom.app ((openImmersionLowerShriek A i).obj M) :=
  AmbientClopen.sheaf_beta_inverse_unit A r k i p sq.flip M

private theorem beta_inverse_map
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (sq : IsPullback k r p i) (M : Sheaf (Scheme.ProEt.topology W) A) :
    (upperStar A k).map ((AmbientClopen.sheafBeta A r k i p sq.flip).inv.app M) ≫
      (upperStar A k).map ((AmbientClopen.sheafBeta A r k i p sq.flip).hom.app M) =
        𝟙 ((upperStar A k).obj
          ((openImmersionLowerShriek A k).obj ((upperStar A r).obj M))) := by
  rw [← (upperStar A k).map_comp,
    (AmbientClopen.sheafBeta A r k i p sq.flip).inv_hom_id_app M]
  exact (upperStar A k).map_id _

private theorem cancel_pair
    {C : Type*} [Category C] {X Y Z T : C}
    (f : X ⟶ Y) (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y)
    (v : Z ⟶ Y) (a : Z ⟶ T) (b : T ⟶ X) (h : v ≫ g = a ≫ b) :
    a ≫ b ≫ f = v := by
  rw [← Category.assoc, ← h, Category.assoc, hg, Category.comp_id]

private theorem sheaf_beta_normalized
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (sq : IsPullback k r p i) :
    AmbientClopen.sheafNormalized A k r p i sq.flip.w
      (AmbientClopen.sheafBeta A r k i p sq.flip).hom := by
  intro M
  exact cancel_pair
    ((upperStar A k).map ((AmbientClopen.sheafBeta A r k i p sq.flip).hom.app M))
    ((upperStar A k).map ((AmbientClopen.sheafBeta A r k i p sq.flip).inv.app M))
    (beta_inverse_map A k r p i sq M)
    ((openImmersionLowerShriekUpperStarAdjunction A k).unit.app ((upperStar A r).obj M))
    ((upperStar A r).map ((openImmersionLowerShriekUpperStarAdjunction A i).unit.app M))
    ((upperStarCompIso A sq.flip.w).hom.app ((openImmersionLowerShriek A i).obj M))
    (beta_unit_copy A k r p i sq M)

private theorem sheaf_alpha_cartesian (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (sq : IsPullback k r p i) :
    AmbientClopen.alpha A k r p i h =
      (AmbientClopen.beta A r k i p sq.flip).hom := by
  apply AmbientClopen.ordinary_normalized_unique A k r p i h
  · exact AmbientClopen.ordinary_alpha_normalized A k r p i h
  · unfold AmbientClopen.beta
    exact sheaf_beta_normalized (ModuleCat.{u + 1} A) k r p i sq

private theorem alpha_cartesian (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (sq : IsPullback k r p i) :
    properOpenAlpha A k r p i h = (properOpenBeta A r k i p sq.flip).hom := by
  rw [← AmbientClopen.ordinary_alpha_localized, AmbientClopen.derivedAlpha,
    sheaf_alpha_cartesian A k r p i h sq]
  exact AmbientClopen.ordinary_beta_localizes A r k i p sq.flip

private theorem mate_ofNatIsoLeft
    {C D H T : Type*} [Category C] [Category D] [Category H] [Category T]
    {Lr Lr' : C ⥤ D} {Rr : D ⥤ C} {Lp Lp' : H ⥤ T} {Rp : T ⥤ H}
    {Ji : C ⥤ H} {Jb : D ⥤ T}
    (ar : Lr ⊣ Rr) (ap : Lp ⊣ Rp) (e : Lr ≅ Lr') (f : Lp ≅ Lp')
    (β : Ji ⋙ Lp' ⟶ Lr' ⋙ Jb) :
    (mateEquiv ar ap (TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft Ji f.hom ≫ β ≫ Functor.whiskerRight e.inv Jb))).natTrans =
    (mateEquiv (ar.ofNatIsoLeft e) (ap.ofNatIsoLeft f)
      (TwoSquare.mk _ _ _ _ β)).natTrans := by
  have he : (conjugateIsoEquiv ar (ar.ofNatIsoLeft e) e.symm).hom = 𝟙 Rr := by
    ext X
    simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
      ← Functor.map_comp, Category.assoc]
  have hf : (conjugateIsoEquiv ap (ap.ofNatIsoLeft f) f.symm).hom = 𝟙 Rp := by
    ext X
    simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
      ← Functor.map_comp, Category.assoc]
  ext X
  have h := AmbientClopen.mate_transport ar (ar.ofNatIsoLeft e) ap
    (ap.ofNatIsoLeft f) e f (Iso.refl Ji) (Iso.refl Jb) β X
  simp only [he, hf, NatTrans.id_app, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp,
    Category.comp_id, Ji.map_id, Rp.map_id] at h
  simp_all

private theorem exact_beta_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (sq : IsPullback a b i p) :
    ordinaryOpenExtensionBaseChangeIso A a b i p sq =
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq).symm := by
  let := isIso_baseChangeMap_of_isPullback (ModuleCat.{u + 1} A) sq
  unfold ordinaryOpenExtensionBaseChangeIso derivedOpenImmersionLowerShriekBaseChangeIso
  have he : (conjugateIsoEquiv
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).comp
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b))).symm
      (asIso (baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)) =
        openImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq := by
    apply Iso.ext
    rfl
  rw [he]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_symm, Iso.symm_inv, Category.assoc]

private theorem beta_mate_exact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S) (r : H ⟶ V) (p : T ⟶ S)
    [IsOpenImmersion b] [IsOpenImmersion i] (sq : IsPullback b r p i) :
    (mateEquiv
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b)
      (TwoSquare.mk _ _ _ _ (ordinaryOpenExtensionBaseChangeIso A r b i p sq.flip).inv)
        ).natTrans = (towerPullSquare A b i r p sq.w).hom := by
  rw [exact_beta_eq]
  have h := mateEquiv_eq_of_unit
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b)
    (TwoSquare.mk _ _ _ _
      (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq.flip).hom)
    (TwoSquare.mk _ _ _ _ (towerPullSquare A b i r p sq.w).hom)
    (fun N ↦ (unit_map_derivedOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) sq.flip N).symm)
  exact congrArg TwoSquare.natTrans h

private theorem raw_mate_exact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S) (r : H ⟶ V) (p : T ⟶ S)
    [IsOpenImmersion b] [IsOpenImmersion i] [QuasiCompact b] [QuasiCompact i]
    [IsProper r] [IsProper p] (w : b ≫ p = r ≫ i) (sq : IsPullback b r p i) :
    properOpenMate A b r p i w =
      (mateEquiv (towerPullPushAdjunction A r) (towerPullPushAdjunction A p)
        (TwoSquare.mk _ _ _ _
          (ordinaryOpenExtensionBaseChangeIso A r b i p sq.flip).hom)).natTrans := by
  unfold properOpenMate
  rw [alpha_cartesian A b r p i w sq]
  unfold properOpenBeta
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom]
  simpa only [leftDerivedUpperStarIsoMapDerivedCategory, towerPullPushAdjunction,
    ProperOpenShriek, TwoSquare.natTrans] using mate_ofNatIsoLeft
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p)
    (ordinaryOpenExtensionBaseChangeIso A r b i p sq.flip).hom

private theorem raw_mate_gamma
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {H T V S : Scheme.{u}} (b : H ⟶ T) (i : V ⟶ S) (r : H ⟶ V) (p : T ⟶ S)
    [IsOpenImmersion b] [IsOpenImmersion i] [QuasiCompact b] [QuasiCompact i]
    [IsProper r] [IsProper p] (sq : IsPullback b r p i)
    (N : ProperOpenDerived A H) (hN : IsIso (towerLambda A b i r p sq.w N)) :
    (properOpenMate A b r p i sq.w).app N = towerGamma A b i r p sq.w N hN := by
  have := hN
  have hu := tower_open_unit A b
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) b).unit := by
    change IsIso (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) b).mapDerivedCategoryAdjunction.unit
    rw [← hu]
    infer_instance
  apply (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i).homEquiv _ _ |>.injective
  change ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i).mapDerivedCategoryAdjunction.homEquiv _ _) _ = _
  dsimp only [towerGamma, derivedOpenImmersionLowerShriekUpperStarAdjunction]
  change ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i).mapDerivedCategoryAdjunction.homEquiv
        ((towerP A r).obj N) ((towerP A p).obj ((towerJ A b).obj N))) _ =
    ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) i).mapDerivedCategoryAdjunction.homEquiv
        ((towerP A r).obj N) ((towerP A p).obj ((towerJ A b).obj N)))
      (((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) i).mapDerivedCategoryAdjunction.homEquiv
          ((towerP A r).obj N) ((towerP A p).obj ((towerJ A b).obj N))).symm _)
  rw [Equiv.apply_symm_apply]
  apply (cancel_mono (towerLambda A b i r p sq.w N)).mp
  rw [IsIso.inv_hom_id]
  rw [raw_mate_exact A b i r p sq.w sq]
  have hh := cartesian_mate_adjunct
    (towerPullPushAdjunction A r) (towerPullPushAdjunction A p)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b)
    (ordinaryOpenExtensionBaseChangeIso A r b i p sq.flip)
    (towerPullSquare A b i r p sq.w) (beta_mate_exact A b i r p sq) N
  have hx : (mateEquiv (towerPullPushAdjunction A p) (towerPullPushAdjunction A r)
      (TwoSquare.mk _ _ _ _ (towerPullSquare A b i r p sq.w).hom)).natTrans.app
        ((towerJ A b).obj N) = towerExchange A b i r p sq.w ((towerJ A b).obj N) := by
    simp only [mateEquiv_apply, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.comp_obj, Functor.comp_map, Category.id_comp, towerExchange, Functor.map_comp]
    erw [Category.comp_id]
  rw [hx] at hh
  have hu' : inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) b).unit.app N) = (towerOpenUnit A b).inv.app N := by
    change inv ((openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) b).mapDerivedCategoryAdjunction.unit.app N) = _
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← hu]
    exact (towerOpenUnit A b).hom_inv_id_app N
  rw [hu'] at hh
  exact hh

private theorem site_interchange_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {H T V S : Scheme.{u}}
    [IsNoetherian H] [IsNoetherian T] [IsNoetherian V] [IsNoetherian S]
    (b : H ⟶ T) (i : V ⟶ S) (r : H ⟶ V) (p : T ⟶ S)
    [IsOpenImmersion b] [IsOpenImmersion i] [QuasiCompact b] [QuasiCompact i]
    [IsProper r] [IsProper p] (sq : IsPullback b r p i)
    (E : FiniteSiteTower.DE A H) :
    DerivedCategory.Plus.ι.map (properOpenSiteInterchange A sq E) ≫
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
          ((FiniteSiteTower.JP A b).obj ((FiniteSiteTower.N A H).obj E)) =
      (towerJ A i).map
          ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlusCompatibility.hom.app
            ((FiniteSiteTower.N A H).obj E)) ≫
        (properOpenMate A b r p i sq.w).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) H).mapDerivedCategory.obj E.obj) := by
  have hN := tower_lambda_model_isIso A sq E
  rw [raw_mate_gamma A b i r p sq _ hN]
  exact tower_gamma_plus A sq E hN

private theorem GP_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X H T V S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian H] [IsNoetherian T]
    [IsNoetherian V] [IsNoetherian S]
    (j : X ⟶ H) (b : H ⟶ T) (i : V ⟶ S) (r : H ⟶ V) (p : T ⟶ S)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    [QuasiCompact b] [QuasiCompact i] [IsProper r] [IsProper p]
    (sq : IsPullback b r p i) (E : FiniteSiteTower.DE A X) :
    DerivedCategory.Plus.ι.map (FiniteSiteTower.GP A j b p i r sq E) ≫
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
          ((FiniteSiteTower.JP A b).obj
            ((FiniteSiteTower.JP A j).obj ((FiniteSiteTower.N A X).obj E))) =
      (towerJ A i).map
          ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlusCompatibility.hom.app
            ((FiniteSiteTower.JP A j).obj ((FiniteSiteTower.N A X).obj E))) ≫
        (properOpenMate A b r p i sq.w).app
          (((FiniteSiteTower.JP A j).obj ((FiniteSiteTower.N A X).obj E)).obj) := by
  let e := (properOpenSiteExtensionIso A j).app E
  have hs := site_interchange_restriction A b i r p sq ((FiniteSiteTower.JE A j).obj E)
  have hp := (lowerStar (ModuleCat.{u + 1} A) p
    ).rightDerivedFunctorPlusCompatibility.hom.naturality ((FiniteSiteTower.JP A b).map e.hom)
  have hr := (lowerStar (ModuleCat.{u + 1} A) r
    ).rightDerivedFunctorPlusCompatibility.hom.naturality e.inv
  have hn := (properOpenMate A b r p i sq.w).naturality
    (DerivedCategory.Plus.ι.map e.hom)
  dsimp only [Functor.comp_map, e, Iso.app_hom, Iso.app_inv] at hp hr hn
  simp only [FiniteSiteTower.GP, Functor.map_comp, Category.assoc]
  erw [hp]
  erw [reassoc_of% hs]
  change (towerJ A i).map
      (DerivedCategory.Plus.ι.map ((FiniteSiteTower.PP A r).map e.inv)) ≫
    ((towerJ A i).map
      ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlusCompatibility.hom.app
        ((FiniteSiteTower.N A H).obj ((FiniteSiteTower.JE A j).obj E))) ≫
      (properOpenMate A b r p i sq.w).app _ ≫
        (towerP A p).map ((towerJ A b).map (DerivedCategory.Plus.ι.map e.hom))) = _
  erw [← hn]
  rw [← Functor.map_comp_assoc]
  erw [hr]
  simp only [Functor.map_comp, Category.assoc]
  have he : (towerJ A i).map ((towerP A r).map (DerivedCategory.Plus.ι.map e.inv)) ≫
      (towerJ A i).map ((towerP A r).map (DerivedCategory.Plus.ι.map e.hom)) = 𝟙 _ := by
    rw [← (towerJ A i).map_comp, ← (towerP A r).map_comp,
      ← DerivedCategory.Plus.ι.map_comp, e.inv_hom_id,
      DerivedCategory.Plus.ι.map_id, (towerP A r).map_id, (towerJ A i).map_id]
  change (towerJ A i).map
      ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlusCompatibility.hom.app
        ((FiniteSiteTower.JP A j).obj ((FiniteSiteTower.N A X).obj E))) ≫
    (towerJ A i).map ((towerP A r).map (DerivedCategory.Plus.ι.map e.inv)) ≫
    (towerJ A i).map ((towerP A r).map (DerivedCategory.Plus.ι.map e.hom)) ≫
    (properOpenMate A b r p i sq.w).app _ = _
  rw [reassoc_of% he]
  rfl

private theorem proper_compositor_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (p : X ⟶ Y) (s : Y ⟶ Z) [IsProper p] [IsProper s]
    (M : FiniteSiteTower.DP A X) :
    DerivedCategory.Plus.ι.map ((FiniteSiteTower.kP A p s).hom.app M) ≫
      (lowerStar (ModuleCat.{u + 1} A) (p ≫ s)).rightDerivedFunctorPlusCompatibility.hom.app M =
    (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctorPlusCompatibility.hom.app
        ((FiniteSiteTower.PP A p).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.map
        ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app M) ≫
      (finiteDirectImageComposition A p s).inv.app M.obj := by
  have he : proEtaleComparisonDirectImageCompIso A p s = FiniteSiteTower.kP A p s := by
    rw [(finiteSiteWordRefinement A).2.2.2.2.1 p s |>.2, FiniteSiteTower.kP,
      conjugateIsoEquiv_iso_symm]
    rfl
  rw [← he]
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
  let := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).preservesKInjectiveComplexes
  simpa only [proEtaleComparisonDirectImageCompIso, finiteDirectImageComposition,
    Iso.symm_inv, FiniteSiteTower.PP, ObjectProperty.ι_obj, Functor.comp_obj]
    using Etale.right_derived_comp_prime_plus
      (lowerStar (ModuleCat.{u + 1} A) p) (lowerStar (ModuleCat.{u + 1} A) s)
      (lowerStarComp (ModuleCat.{u + 1} A) p s) M

private theorem open_compositor_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    (proEtaleOpenExtensionComp A j b).symm = AmbientClopen.openComp A j b := by
  rw [proEtaleOpenExtensionComp, AmbientClopen.openComp, AmbientClopen.sheafOpenComp,
    ← WeilConjectures.AmbientCompositor.left_comp_unique]
  rfl

private theorem open_compositor_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (b : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] (M : FiniteSiteTower.DP A X) :
    DerivedCategory.Plus.ι.map ((FiniteSiteTower.mP A j b).hom.app M) =
      (properOpenShriekComp A j b).hom.app M.obj := by
  rw [← AmbientClopen.ordinary_open_comp_localized, ← open_compositor_eq A j b]
  have hc : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusCompIso
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) b)).app M) =
      (Functor.mapDerivedCategoryCompIso
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) b)).app M.obj := by
    apply Iso.ext
    exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ M
  simp only [FiniteSiteTower.mP, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app]
  exact congrArg (fun t ↦ t ≫ _) (congrArg Iso.inv hc)

private theorem AP_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X H T V S Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian H] [IsNoetherian T]
    [IsNoetherian V] [IsNoetherian S] [IsNoetherian Z]
    (j : X ⟶ H) (b : H ⟶ T) (p : T ⟶ S) (s : S ⟶ Z) (i : V ⟶ S) (r : H ⟶ V)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    [QuasiCompact b] [QuasiCompact i] [IsProper r] [IsProper p] [IsProper s]
    (sq : IsPullback b r p i) (E : FiniteSiteTower.DE A X) :
    DerivedCategory.Plus.ι.map (FiniteSiteTower.AP A j b p s i r sq E) ≫
      (CartesianTower.targetInclusion A (j ≫ b) (p ≫ s)
        ((FiniteSiteTower.N A X).obj E)).hom =
    (CartesianTower.sourceInclusion A j r i s ((FiniteSiteTower.N A X).obj E)).hom ≫
      (towerP A s).map ((properOpenMate A b r p i sq.w).app
        (((FiniteSiteTower.JP A j).obj ((FiniteSiteTower.N A X).obj E)).obj)) ≫
      (finiteDirectImageComposition A p s).inv.app
        (((FiniteSiteTower.JP A b).obj
          ((FiniteSiteTower.JP A j).obj ((FiniteSiteTower.N A X).obj E))).obj) ≫
      (towerP A (p ≫ s)).map ((properOpenShriekComp A j b).hom.app
        (((FiniteSiteTower.N A X).obj E).obj)) := by
  have hk := proper_compositor_restriction A p s
    ((FiniteSiteTower.JP A b).obj ((FiniteSiteTower.JP A j).obj
      ((FiniteSiteTower.N A X).obj E)))
  have hm := open_compositor_restriction A j b ((FiniteSiteTower.N A X).obj E)
  have hg := GP_restriction A j b i r p sq E
  have hn := (lowerStar (ModuleCat.{u + 1} A) (p ≫ s)
    ).rightDerivedFunctorPlusCompatibility.hom.naturality
      ((FiniteSiteTower.mP A j b).hom.app ((FiniteSiteTower.N A X).obj E))
  have hq := (lowerStar (ModuleCat.{u + 1} A) s
    ).rightDerivedFunctorPlusCompatibility.hom.naturality
      (FiniteSiteTower.GP A j b p i r sq E)
  dsimp only [Functor.comp_map] at hn hq
  simp only [FiniteSiteTower.AP, CartesianTower.targetInclusion,
    CartesianTower.sourceInclusion, Functor.map_comp, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom,
    NatTrans.id_app]
  erw [reassoc_of% hn, reassoc_of% hk, reassoc_of% hq]
  rw [← Functor.map_comp_assoc, hg, Functor.map_comp, hm]
  erw [(lowerStar (ModuleCat.{u + 1} A) (p ≫ s)).rightDerivedFunctor.map_id,
    (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor.map_id,
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategory.map_id,
    (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.map_id]
  erw [(lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.map_id]
  simp only [Category.assoc, Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

private theorem alpha_component
    {G : Type*} [Category G] {geo : G ⥤ Scheme.{u}} (c : Calculus G geo)
    {X V W Y B Z : G}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion (geo.map j)] [IsOpenImmersion (geo.map b)]
    [IsOpenImmersion (geo.map i)] [QuasiCompact (geo.map b)]
    [QuasiCompact (geo.map i)] [IsProper (geo.map q)] [IsProper (geo.map p)]
    (hb : b ≫ p = q ≫ i) (M : c.D X) :
    (alpha c j b q p i s hb).app M =
      (c.S s).map ((c.gamma b q p i hb).app ((c.J j).obj M)) ≫
        (c.sComp p s).hom.app ((c.J b).obj ((c.J j).obj M)) ≫
          (c.S (p ≫ s)).map ((c.jComp j b).hom.app M) := by
  simp only [alpha, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp]
  erw [Category.id_comp]

private theorem ordinary_gamma_eq
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W Y B : Spaces F} (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B)
    [IsOpenImmersion ((geometry F).map b)] [IsOpenImmersion ((geometry F).map i)]
    [QuasiCompact ((geometry F).map b)] [QuasiCompact ((geometry F).map i)]
    [IsProper ((geometry F).map q)] [IsProper ((geometry F).map p)]
    [IsOpenImmersion b.hom.left] [IsOpenImmersion i.hom.left]
    [QuasiCompact b.hom.left] [QuasiCompact i.hom.left]
    [IsProper q.hom.left] [IsProper p.hom.left]
    (hb : b ≫ p = q ≫ i) :
    (ordinary F A).gamma b q p i hb =
      properOpenMate A b.hom.left q.hom.left p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) hb) := by
  unfold Calculus.gamma properOpenMate
  rfl

private theorem ordinary_sComp_eq
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W B Z : Spaces F} (p : W ⟶ B) (s : B ⟶ Z) :
    (ordinary F A).sComp p s =
      conjugateIsoEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s.hom.left).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p.hom.left))
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (p.hom.left ≫ s.hom.left))
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p.hom.left s.hom.left) := by
  unfold Calculus.sComp
  rfl

private theorem ordinary_jComp_eq
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W : Spaces F} (j : X ⟶ V) (b : V ⟶ W)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)] :
    letI : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
    letI : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
    (ordinary F A).jComp j b = properOpenShriekComp A j.hom.left b.hom.left := by
  unfold Calculus.jComp properOpenShriekComp
  rfl

private theorem ordinary_tower_component
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W Y B Z : Spaces F}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
    [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
    [QuasiCompact ((geometry F).map i)]
    [IsProper ((geometry F).map q)] [IsProper ((geometry F).map p)]
    [IsProper ((geometry F).map s)]
    (hb : b ≫ p = q ≫ i)
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (E : FiniteSiteTower.DE A X.obj.left) :
    letI : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
    letI : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
    letI : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
    letI : QuasiCompact b.hom.left := ‹QuasiCompact ((geometry F).map b)›
    letI : QuasiCompact i.hom.left := ‹QuasiCompact ((geometry F).map i)›
    letI : IsProper q.hom.left := ‹IsProper ((geometry F).map q)›
    letI : IsProper p.hom.left := ‹IsProper ((geometry F).map p)›
    letI : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
    letI : IsOpenImmersion (j ≫ b).hom.left :=
      mappedCompositeOpen (geo := geometry F) j b
    letI : IsProper (p ≫ s).hom.left := mappedCompositeProper (geo := geometry F) p s
    (towerP A s.hom.left).map
        ((properOpenMate A b.hom.left q.hom.left p.hom.left i.hom.left sq.w).app
          ((towerJ A j.hom.left).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory.obj
              E.obj))) ≫
      (finiteDirectImageComposition A p.hom.left s.hom.left).inv.app
        ((towerJ A b.hom.left).obj ((towerJ A j.hom.left).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory.obj
            E.obj))) ≫
      (towerP A (p.hom.left ≫ s.hom.left)).map
        ((properOpenShriekComp A j.hom.left b.hom.left).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory.obj
            E.obj)) =
      (alpha (ordinary F A) j b q p i s hb).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory.obj
          E.obj) := by
  let : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
  let : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
  let : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
  let : QuasiCompact b.hom.left := ‹QuasiCompact ((geometry F).map b)›
  let : QuasiCompact i.hom.left := ‹QuasiCompact ((geometry F).map i)›
  let : IsProper q.hom.left := ‹IsProper ((geometry F).map q)›
  let : IsProper p.hom.left := ‹IsProper ((geometry F).map p)›
  let : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
  let : IsOpenImmersion (j ≫ b).hom.left := mappedCompositeOpen (geo := geometry F) j b
  let : IsProper (p ≫ s).hom.left := mappedCompositeProper (geo := geometry F) p s
  have hm : properOpenMate A b.hom.left q.hom.left p.hom.left i.hom.left sq.w =
      properOpenMate A b.hom.left q.hom.left p.hom.left i.hom.left
        (congrArg (fun f ↦ f.hom.left) hb) :=
    congrArg (properOpenMate A b.hom.left q.hom.left p.hom.left i.hom.left)
      (Subsingleton.elim _ _)
  have ha := alpha_component (ordinary F A) j b q p i s hb
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory.obj E.obj)
  simp only [ordinary_gamma_eq, ordinary_sComp_eq, ordinary_jComp_eq] at ha
  rw [← hm, ← WeilConjectures.CompactSupportFiniteProjection.derived_compositor_conjugate_iso]
    at ha
  exact ha.symm

/-- The raw Cartesian mate tower restricts to the specified site-interchange tower.
This contains no compactification comparison or canonical compact-support compositor.
Source: Stacks 0F7B, proper/open interchange, and 0F7J, compatible triangle
(blueprint: lem-sf-cartesian-tower-restriction).

Proof: The map from V into the fibre product W x_B Y is an isomorphism because the
square is Cartesian. Therefore the clopen projector in properOpenAlpha is the identity.
Take its two proper adjunction mates and then its open adjunction mate. The open unit
normalization of beta and the proper triangle identity show that this adjunct is the
inverse of restriction exchange followed by the inverse open unit. The specified
properOpenSiteInterchange has precisely this adjunct by properOpen_site_mate and the
canonical site/open comparison, so injectivity of the open Hom equivalence
identifies the maps. At J_j nu^*E use the canonical open site comparison to change the
witness, which gives GP. Transport the proper compositor through the D+ inclusion by
adjunction conjugacy, and the open compositor by the exact-derived comparison. Expand
alpha and AP, paste the three squares, and cancel the intermediate inclusion
isomorphisms. The two surviving boundary isomorphisms are sourceInclusion and
targetInclusion, by their displayed definitions. This argument also covers empty opens:
the same units and triangle identities hold for the zero extension functor. -/
theorem cartesianTowerRestriction
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W Y B Z : Spaces F}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
    [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
    [QuasiCompact ((geometry F).map i)]
    [IsProper ((geometry F).map q)] [IsProper ((geometry F).map p)]
    [IsProper ((geometry F).map s)]
    (hb : b ≫ p = q ≫ i)
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (E : FiniteSiteTower.DE A X.obj.left) :
    letI : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
    letI : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
    letI : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
    letI : QuasiCompact b.hom.left := ‹QuasiCompact ((geometry F).map b)›
    letI : QuasiCompact i.hom.left := ‹QuasiCompact ((geometry F).map i)›
    letI : IsProper q.hom.left := ‹IsProper ((geometry F).map q)›
    letI : IsProper p.hom.left := ‹IsProper ((geometry F).map p)›
    letI : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
    letI : IsOpenImmersion (j ≫ b).hom.left :=
      mappedCompositeOpen (geo := geometry F) j b
    letI : IsProper (p ≫ s).hom.left := mappedCompositeProper (geo := geometry F) p s
    DerivedCategory.Plus.ι.map
        (FiniteSiteTower.AP A j.hom.left b.hom.left p.hom.left s.hom.left i.hom.left
          q.hom.left sq E) ≫
      (CartesianTower.targetInclusion A (j ≫ b).hom.left (p ≫ s).hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom =
    (CartesianTower.sourceInclusion A j.hom.left q.hom.left i.hom.left s.hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom ≫
      (alpha (ordinary F A) j b q p i s hb).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory.obj
          E.obj) := by
  let : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
  let : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
  let : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
  let : QuasiCompact b.hom.left := ‹QuasiCompact ((geometry F).map b)›
  let : QuasiCompact i.hom.left := ‹QuasiCompact ((geometry F).map i)›
  let : IsProper q.hom.left := ‹IsProper ((geometry F).map q)›
  let : IsProper p.hom.left := ‹IsProper ((geometry F).map p)›
  let : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
  let : IsOpenImmersion (j ≫ b).hom.left := mappedCompositeOpen (geo := geometry F) j b
  let : IsProper (p ≫ s).hom.left := mappedCompositeProper (geo := geometry F) p s
  have h := AP_restriction A j.hom.left b.hom.left p.hom.left s.hom.left i.hom.left
    q.hom.left sq E
  refine h.trans ?_
  exact congrArg (fun t ↦
    (CartesianTower.sourceInclusion A j.hom.left q.hom.left i.hom.left s.hom.left
      ((FiniteSiteTower.N A X.obj.left).obj E)).hom ≫ t)
    (ordinary_tower_component F A j b q p i s hb sq E)

end AlgebraicGeometry.ProEtale
