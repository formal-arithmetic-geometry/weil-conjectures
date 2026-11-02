/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData

/-! The sectionwise ordinary mate identity for the finite restriction square.
(blueprint: lem-sf-finite-base-change-restriction-ordinary-pin-mate)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- The site-level identity behind the fixed-scalar open-square mate: the corner
counit followed by the canonical pullback pasting is the site-square inverse followed
by base change of the open counit. Source: Stacks 04J0 (blueprint:
lem-sf-finite-base-change-restriction-ordinary-pin-mate). -/
private theorem siteSquare_counit
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (t : SiteSquare (finiteInput A gU j' j g sq)) (V : X.ProEt) :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j')).map
        ((MorphismProperty.Over.pullbackComp gU j).inv.app V ≫
          (MorphismProperty.Over.pullbackCongr sq.toCommSq.w.symm).inv.app V ≫
          (MorphismProperty.Over.pullbackComp j' g).hom.app V) ≫
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j' (inferInstance : WeaklyEtale j')
        trivial).counit.app ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V) =
    t.iso.inv.app ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V) ≫
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
        ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j (inferInstance : WeaklyEtale j)
          trivial).counit.app V) := by
  have w1 : ∀ {P Q : X'.ProEt} (f : P ⟶ Q), f.left ≫ Q.hom = P.hom := fun f ↦ by
    simpa using f.w
  have ht : (t.iso.inv.app ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V)).left ≫
      pullback.fst ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V)).hom g =
      pullback.fst ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V).hom gU :=
    eq_of_heq (t.first ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V))
  ext1
  apply pullback.hom_ext
  · have hc0 := MorphismProperty.Over.pullbackCongr_hom_app_left_fst (P := @WeaklyEtale) (Q := ⊤)
      sq.toCommSq.w.symm V
    have hc : ((MorphismProperty.Over.pullbackCongr sq.toCommSq.w.symm).inv.app V).left ≫
        pullback.fst V.hom (j' ≫ g) = pullback.fst V.hom (gU ≫ j) := by
      rw [← hc0, ← Category.assoc, ← MorphismProperty.Comma.comp_left, Iso.inv_hom_id_app]
      simp
    have e1 : (pullbackLeftPullbackSndIso V.hom g j').inv ≫
        pullback.fst (pullback.snd V.hom g) j' ≫ pullback.fst V.hom g =
        pullback.fst V.hom (j' ≫ g) := by simp
    have e2 : (pullbackLeftPullbackSndIso V.hom j gU).hom ≫ pullback.fst V.hom (gU ≫ j) =
        pullback.fst (pullback.snd V.hom j) gU ≫ pullback.fst V.hom j := by simp
    have eR : (t.iso.inv.app ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V) ≫
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
          ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j (inferInstance : WeaklyEtale j)
            trivial).counit.app V)).left ≫ pullback.fst V.hom g =
        (t.iso.inv.app ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V)).left ≫
          pullback.fst ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V)).hom g ≫
          pullback.fst V.hom j := by
      rw [MorphismProperty.Comma.comp_left, Category.assoc,
        MorphismProperty.Over.pullback_map_left]
      erw [pullback.lift_fst]
      rfl
    calc _ = pullback.fst (pullback.snd V.hom j) gU ≫ pullback.fst V.hom j := by
          simp
          erw [e1, hc, e2]
      _ = _ := by
          erw [eR, reassoc_of% ht]
          rfl
  · rw [show pullback.snd V.hom g = ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V).hom
      from rfl]
    erw [w1, w1]

/-- The canonical restriction comparison of the finite open square, induced by the
site-square inverse. Source: Stacks 04J0 (blueprint:
lem-sf-finite-base-change-restriction-ordinary-pin-mate). -/
private def finiteSquareRestriction
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (t : SiteSquare (finiteInput A gU j' j g sq)) :
    ProEtale.lowerStar (ModuleCat.{u + 1} A) g ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⟶
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j' ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} A) gU :=
  haveI := Functor.isContinuous_comp (openInclusion .ordinary j) (baseChange .ordinary g)
    (topology .ordinary U) (topology .ordinary X) (topology .ordinary X')
  haveI := Functor.isContinuous_comp (baseChange .ordinary gU) (openInclusion .ordinary j')
    (topology .ordinary U) (topology .ordinary U') (topology .ordinary X')
  Functor.sheafPushforwardContinuousNatTrans t.iso.inv (ModuleCat.{u + 1} A)
    (topology .ordinary U) (topology .ordinary X')

/-- Sections of the restriction comparison are restrictions along the site square.
Source: Stacks 04J0 (blueprint: lem-sf-finite-base-change-restriction-ordinary-pin-mate). -/
private theorem finiteSquareRestriction_app
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (t : SiteSquare (finiteInput A gU j' j g sq))
    (K : Sheaf (ProEt.topology X') (ModuleCat.{u + 1} A)) (W : U.ProEtᵒᵖ) :
    ((finiteSquareRestriction A gU j' j g sq t).app K).hom.app W =
      K.obj.map (t.iso.inv.app W.unop).op := rfl


/-- The restriction comparison is the conjugate of the inverse-image square, pinned by
the open restriction identification. Source: Stacks 04J0 and 09AE (blueprint:
lem-sf-finite-base-change-restriction-ordinary-pin-mate). -/
private theorem conjugateEquiv_upperStarCompIso
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j'] :
    conjugateEquiv ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (ProEtale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j'))
      ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU))
      ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom ≫
        Functor.whiskerLeft (ProEtale.upperStar (ModuleCat.{u + 1} A) g)
          (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j').hom) =
    (ProEtale.lowerStarComp (ModuleCat.{u + 1} A) j' g).hom ≫
      (ProEtale.lowerStarCongr (ModuleCat.{u + 1} A) sq.toCommSq.w.symm).hom ≫
      (ProEtale.lowerStarComp (ModuleCat.{u + 1} A) gU j).inv := by
  let A' := ModuleCat.{u + 1} A
  have hι : conjugateEquiv (ProEtale.openImmersionRestrictionLowerStarAdjunction A' j')
      (ProEtale.upperStarLowerStarAdjunction A' j')
      (ProEtale.upperStarIsoOpenImmersionRestriction A' j').hom = 𝟙 _ :=
    congrArg Iso.inv ((conjugateIsoEquiv (ProEtale.upperStarLowerStarAdjunction A' j')
      (ProEtale.openImmersionRestrictionLowerStarAdjunction A' j')).apply_symm_apply
        (Iso.refl _))
  rw [← conjugateEquiv_comp _ ((ProEtale.upperStarLowerStarAdjunction A' g).comp
      (ProEtale.upperStarLowerStarAdjunction A' j')) _, conjugateEquiv_whiskerLeft, hι,
    Functor.whiskerRight_id', Category.id_comp]
  have hc : (ProEtale.upperStarCompIso A' sq.toCommSq.w).hom =
      (ProEtale.upperStarComp A' gU j).inv ≫ (ProEtale.upperStarCongr A' sq.toCommSq.w.symm).inv ≫
        (ProEtale.upperStarComp A' j' g).hom := rfl
  rw [hc, ← conjugateEquiv_comp _ (ProEtale.upperStarLowerStarAdjunction A' (gU ≫ j)) _,
    ← conjugateEquiv_comp _ (ProEtale.upperStarLowerStarAdjunction A' (j' ≫ g)) _,
    ProEtale.conjugateEquiv_upperStarComp_hom, ProEtale.conjugateEquiv_upperStarCongr_inv,
    ProEtale.conjugateEquiv_upperStarComp_inv, Category.assoc]


/-- The section identity of the two pushforward routes around the finite open square.
Source: Stacks 04J0 (blueprint: lem-sf-finite-base-change-restriction-ordinary-pin-mate). -/
private theorem finiteSquare_unit_restriction
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (t : SiteSquare (finiteInput A gU j' j g sq))
    (K : Sheaf (ProEt.topology X') (ModuleCat.{u + 1} A)) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).map
        ((ProEtale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j').unit.app
          K) ≫
      ((ProEtale.lowerStarComp (ModuleCat.{u + 1} A) j' g).hom ≫
        (ProEtale.lowerStarCongr (ModuleCat.{u + 1} A) sq.toCommSq.w.symm).hom ≫
        (ProEtale.lowerStarComp (ModuleCat.{u + 1} A) gU j).inv).app
          ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j').obj K) =
    (ProEtale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj K) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) j).map
        ((finiteSquareRestriction A gU j' j g sq t).app K) := by
  have hs := siteSquare_counit A gU j' j g sq t
  ext1
  apply NatTrans.ext
  funext V
  induction V with | op V => ?_
  have h2 := congrArg (fun f ↦ K.obj.map f.op) (hs V)
  simp only [Functor.map_comp, op_comp] at h2
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ProEtale.lowerStar_map_hom_app',
    ProEtale.lowerStarComp_hom_app_hom_app, ProEtale.lowerStarComp_inv_app_hom_app,
    ProEtale.lowerStarCongr_hom_app_hom_app, finiteSquareRestriction_app]
  simp [ProEtale.openImmersionRestrictionLowerStarAdjunction,
    ProEtale.localizationRestrictionLowerStarAdjunction] at h2 ⊢
  exact h2


/-- The fixed-scalar open-square mate: the two transports of a pulled-back section to
the corner agree. Source: Stacks 04J0 and 09AE (blueprint:
lem-sf-finite-base-change-restriction-ordinary-pin-mate). -/
private theorem finiteSquare_mate
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (t : SiteSquare (finiteInput A gU j' j g sq))
    (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU).unit.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) gU).map
        ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom.app N ≫
          (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j').hom.app
            ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N)) =
    (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app N ≫
      (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).unit.app N) ≫
      (finiteSquareRestriction A gU j' j g sq t).app
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N) := by
  apply ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  -- the unit equation of the conjugate
  have hα := unit_conjugateEquiv
    ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
      (ProEtale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j'))
    ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU))
    ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom ≫
      Functor.whiskerLeft (ProEtale.upperStar (ModuleCat.{u + 1} A) g)
        (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j').hom) N
  rw [conjugateEquiv_upperStarCompIso A gU j' j g sq] at hα
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp] at hα
  have hs := finiteSquare_unit_restriction A gU j' j g sq t
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N)
  simp only [NatTrans.comp_app] at hs
  have hι : (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app N ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) j).map
        ((ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app N) =
      (ProEtale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app N :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ N
  have hn := (ProEtale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.naturality
    ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).unit.app N)
  simp only [Functor.id_map, Functor.comp_map] at hn
  dsimp only [Functor.comp_obj] at hα
  simp only [Functor.map_comp, Category.assoc]
  rw [← hα, hs, reassoc_of% hι, ← reassoc_of% hn]


private theorem FiniteRealization.underlying_map_apply {A : Type (u + 1)} [CommRing A]
    {X : Scheme.{u}} {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) {M M' : FiniteModules A X} (φ : M ⟶ M')
    (V : X.ProEtᵒᵖ) (y : (e.equivalence.functor.obj M).val.obj V) :
    (e.underlying.hom.app M').hom.app V ((e.equivalence.functor.map φ).val.app V y) =
      φ.hom.app V ((e.underlying.hom.app M).hom.app V y) := by
  have h := congrArg (fun f ↦ f.hom.app V y) (e.underlying.hom.naturality φ)
  exact h

private theorem FiniteRealization.underlying_restrict {A : Type (u + 1)} [CommRing A]
    {X : Scheme.{u}} {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (M : FiniteModules A X) {V V' : X.ProEtᵒᵖ} (ρ : V ⟶ V')
    (y : (e.equivalence.functor.obj M).val.obj V) :
    (e.underlying.hom.app M).hom.app V' ((e.equivalence.functor.obj M).val.map ρ y) =
      M.obj.map ρ ((e.underlying.hom.app M).hom.app V y) := by
  have h := congrArg (fun f ↦ f y) ((e.underlying.hom.app M).hom.naturality ρ)
  exact h

private theorem FiniteRealization.underlying_injective {A : Type (u + 1)} [CommRing A]
    {X : Scheme.{u}} {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i) (M : FiniteModules A X) (V : X.ProEtᵒᵖ) :
    Function.Injective ((e.underlying.hom.app M).hom.app V) := by
  intro a b hab
  have h := congrArg ((e.underlying.inv.app M).hom.app V) hab
  have hi : ∀ z, (e.underlying.inv.app M).hom.app V ((e.underlying.hom.app M).hom.app V z) = z :=
    fun z ↦ by
      have := congrArg (fun f ↦ f.hom.app V z) (e.underlying.hom_inv_id_app M)
      exact this
  rwa [hi, hi] at h

/-- Sections of the corner pullback comparison, in the composite form used below.
Source: Stacks 03D7 (blueprint: lem-sf-finite-base-change-restriction-ordinary-pin-mate). -/
private theorem pullU_right_apply
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) (N : FiniteModules A X) (W : (Site .ordinary U)ᵒᵖ)
    (y : (e.realizeU.equivalence.functor.obj
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) gU ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} A) gU).obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N))).val.obj W) :
    (e.realizeU'.underlying.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) j ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} A) gU).obj N)).hom.app
        (op ((baseChange .ordinary gU).obj W.unop))
        ((e.pullU_pin.right.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) gU).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N))).val.app W y) =
      (e.realizeU.underlying.hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) gU ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} A) gU).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N))).hom.app W y :=
  e.pullU_pin.right_sections _ W y

private theorem pinMate_sections
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) (N : FiniteModules A X) :
    e.open_pin.star.hom.app N ≫
      (restrict .ordinary j (finiteInput A gU j' j g sq).R).map
        (e.realizeX.equivalence.functor.map
          ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).unit.app N)) ≫
      (restrict .ordinary j (finiteInput A gU j' j g sq).R).map
        (e.pull_pin.right.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N)) ≫
      o.rightSquare.hom.app (e.realizeX'.equivalence.functor.obj
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N)) =
      e.realizeU.equivalence.functor.map
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU).unit.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N)) ≫
      e.pullU_pin.right.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) gU).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N)) ≫
      (direct .ordinary gU _ _ (cornerCoefficient t)).map
        (e.realizeU'.equivalence.functor.map
          ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom.app N)) ≫
      (direct .ordinary gU _ _ (cornerCoefficient t)).map
        (e.open'_pin.star.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  apply FiniteRealization.underlying_injective e.realizeX'
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N)
    (op ((openInclusion .ordinary j').obj ((baseChange .ordinary gU).obj W.unop)))
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [o.rightSections]
  erw [FiniteRealization.underlying_restrict, e.pull_pin.right_sections,
    FiniteRealization.underlying_map_apply, e.open_pin.sections]
  change _ = (ConcreteCategory.hom ((e.realizeX'.underlying.hom.app
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N)).hom.app _))
    ((ConcreteCategory.hom ((e.open'_pin.star.hom.app
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N)).val.app
        (op ((baseChange .ordinary gU).obj W.unop))))
      ((ConcreteCategory.hom ((e.realizeU'.equivalence.functor.map
        ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom.app N)).val.app
          (op ((baseChange .ordinary gU).obj W.unop)))) _))
  erw [e.open'_pin.sections, FiniteRealization.underlying_map_apply]
  rw [pullU_right_apply A gU j' j g sq o e]
  erw [FiniteRealization.underlying_map_apply]
  have hF := congrArg (fun f ↦ f.hom.app W
    ((e.realizeU.underlying.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N)).hom.app
      W x)) (finiteSquare_mate A gU j' j g sq t N)
  exact hF.symm

/-- The ordinary restriction square commutes with all four finite comparison pins.

Source: the ordinary representative calculation in
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md`.
Proof: identify the inverse site-square map with the canonical pullback comparison
using its first projection and its structure map to X'. The two pull pins'
right-section equations and the two open pins' section equations then identify
both routes of the right-adjoint square on each section. Faithfulness of the
underlying sheaf functors gives equality of the square maps. Take mates under
the two finite pull adjunctions and the two ringed pull adjunctions, using
`FinitePullPin.mate` and `Operations.ordinaryTheta_mate`. The ordinary
fixed-scalar square has mate `upperStarCompIso`; this gives the displayed
identity between the four pinned left-adjoint comparisons.
(blueprint: lem-sf-finite-base-change-restriction-ordinary-pin-mate) -/
theorem finite_base_change_restriction_ordinary_pin_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) (N : FiniteModules A X) :
    e.pullU_pin.ordinary.hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N) ≫
      o.gUPull.ordinary.map (e.open_pin.star.hom.app N) ≫
      o.ordinaryTheta.inv.app (e.realizeX.equivalence.functor.obj N) =
    e.realizeU'.equivalence.functor.map
        ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom.app N) ≫
      e.open'_pin.star.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N) ≫
      (restrict .ordinary j' (finiteInput A gU j' j g sq).S).map
        (e.pull_pin.ordinary.hom.app N) := by
  rw [← cancel_epi (e.pullU_pin.ordinary.inv.app
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N)), Iso.inv_hom_id_app_assoc]
  apply (o.gUPull.adjunction.homEquiv _ _).injective
  have hθ := o.ordinaryTheta_mate (e.realizeX.equivalence.functor.obj N)
  have hmU := e.pullU_pin.mate ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N)
  dsimp only [Functor.comp_obj] at hθ hmU ⊢
  rw [Adjunction.homEquiv_naturality_left, hθ, Adjunction.homEquiv_unit,
    Functor.map_comp, ← reassoc_of% hmU]
  have hm := e.pull_pin.mate N
  have hunit : o.gPull.adjunction.unit.app (e.realizeX.equivalence.functor.obj N) =
      e.realizeX.equivalence.functor.map
          ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).unit.app N) ≫
        e.pull_pin.right.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N) ≫
        (direct .ordinary g _ _ _).map (e.pull_pin.ordinary.hom.app N) := by
    rw [reassoc_of% hm, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp
  have hr := o.rightSquare.hom.naturality (e.pull_pin.ordinary.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hr
  rw [hunit, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hr]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (pinMate_sections A gU j' j g sq o e N)]


end SheafOfModules.OpenTensorNormalization
