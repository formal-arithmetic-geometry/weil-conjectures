/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.AlgebraicGeometry.HigherDirectImagesLimits
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Smooth base change for limits of smooth schemes

Source: Stacks Project, Tag 0F09, lemma-smooth-base-change-general
(blueprint: lem-kun-0f09).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry



private theorem single_smooth
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F),
      ∃ n : ℕ, 0 < n ∧ n • x = 0 ∧ IsUnit (n : Γ(Y, ⊤))) :
    IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let G := U.objPreimage F
  let eF : U.obj G ≅ F := U.objObjPreimageIso F
  have hsep (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj F) :
      ∃ n : ℕ, 0 < n ∧ n • x = 0 ∧ IsUnit (n : Γ(Y, ⊤)) := by
    let c := Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
    let φ := (Scheme.pointSmallEtalePrecomp s c).sheafFiber.app F
    have : IsIso φ := Scheme.isIso_pointSmallEtalePrecomp_sheafFiber s c F
    obtain ⟨n, hn, hx, hu⟩ := hF (AlgebraicClosure Ω) (c ≫ s) (φ.hom x)
    refine ⟨n, hn, ?_, hu⟩
    apply (ConcreteCategory.bijective_of_isIso φ).1
    change φ.hom (n • x) = φ.hom 0
    simpa only [map_nsmul, map_zero] using hx
  have : Scheme.IsTorsionSheafOfInvertibleOrder Y G := by
    constructor
    intro Ω _ _ s x
    let Φ := Scheme.pointSmallEtale s
    let V := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
    have : LocallySmall.{u + 1} X.Etale :=
      @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
    let φ := (Φ.uliftSheafFiberIso AddCommGrpCat.{u + 1}).symm.app (U.obj G) ≪≫
      ((Φ.ulift.{u + 1}).sheafFiberCompIso V).app G ≪≫
      V.mapIso ((Φ.uliftSheafFiberIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).app G)
    let e := φ.symm ≪≫ Φ.sheafFiber.mapIso eF
    obtain ⟨n, hn, hx, hu⟩ := hsep Ω s (e.hom.hom x)
    refine ⟨n, hn, hu, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    change e.hom.hom (n • x) = e.hom.hom 0
    simpa only [map_nsmul, map_zero] using hx
  let τ := Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq
  apply (NatTrans.isIso_app_iff_of_iso τ
    ((DerivedCategory.Plus.singleFunctor _ 0).mapIso eF)).1
  apply (NatTrans.isIso_app_iff_of_iso τ
    ((U.mapDerivedCategoryPlusSingleFunctor 0).app G)).1
  apply (Etale.isIso_derivedBaseChangeMapPlus_app_forget₂_iff sq.toCommSq
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)).2
  rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus]
  exact Etale.isIso_baseChange_app_singleFunctor_obj_of_smooth _ g sq G

private theorem single_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : Scheme.{u}) (D : Iᵒᵖ ⥤ Scheme.{u})
    (η : D ⟶ (Functor.const Iᵒᵖ).obj S)
    (htrans : ∀ (i j : Iᵒᵖ) (a : i ⟶ j), IsAffineHom (D.map a))
    (c : Cone D) (hc : IsLimit c) (g : c.pt ⟶ S)
    (hη : ∀ i : Iᵒᵖ, c.π.app i ≫ η.app i = g)
    {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {X' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ c.pt}
    (sq : ChosenCartesianSquare g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (hstage : ∀ i : Iᵒᵖ, IsIso
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f (η.app i)).toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :
    IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  classical
  have : IsConnected I := IsFiltered.isConnected I
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  let DS : Iᵒᵖ ⥤ Scheme.{u} := (Functor.const Iᵒᵖ).obj S
  let DT : Iᵒᵖ ⥤ Scheme.{u} := (Functor.const Iᵒᵖ).obj X
  let ηg : DT ⟶ DS := (Functor.const Iᵒᵖ).map f
  let DP : Iᵒᵖ ⥤ Scheme.{u} :=
    { obj i := pullback f (η.app i)
      map {i j} a := pullback.map _ _ _ _ (𝟙 X) (D.map a) (𝟙 S)
        (by simp) (by simp [η.naturality])
      map_id i := by apply pullback.hom_ext <;> simp
      map_comp a b := by apply pullback.hom_ext <;> simp [Category.assoc] }
  let ηe : DP ⟶ DT :=
    { app i := pullback.fst _ _
      naturality i j a := by simp [DP, DT] }
  let ηh : DP ⟶ D :=
    { app i := pullback.snd _ _
      naturality i j a := by simp [DP] }
  let cp : Cone DP :=
    { pt := X'
      π :=
        { app i := pullback.lift g' (f' ≫ c.π.app i)
            (by rw [Category.assoc, hη, sq.w])
          naturality i j a := by
            apply pullback.hom_ext <;> simp [DP, Category.assoc] } }
  let sqp := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have hcp : IsLimit cp := by
    let lX (t : Cone DP) : t.pt ⟶ X := (isLimitConstCone Iᵒᵖ X).lift ((Cone.postcompose ηe).obj t)
    let lD (t : Cone DP) : t.pt ⟶ c.pt := hc.lift ((Cone.postcompose ηh).obj t)
    have hlX (t : Cone DP) (i : Iᵒᵖ) : lX t = t.π.app i ≫ pullback.fst _ _ := by
      have h := (isLimitConstCone Iᵒᵖ X).fac ((Cone.postcompose ηe).obj t) i
      change lX t ≫ 𝟙 X = t.π.app i ≫ pullback.fst f (η.app i) at h
      simpa only [Category.comp_id] using h
    have hlD (t : Cone DP) (i : Iᵒᵖ) :
        lD t ≫ c.π.app i = t.π.app i ≫ pullback.snd _ _ := by
      simpa only [lD, Cone.postcompose_obj_π, NatTrans.comp_app, ηh] using
        hc.fac ((Cone.postcompose ηh).obj t) i
    have hw (t : Cone DP) : lX t ≫ f = lD t ≫ g := by
      let i : Iᵒᵖ := Classical.arbitrary _
      rw [hlX t i, Category.assoc, pullback.condition, ← hη i]
      rw [← Category.assoc (lD t), hlD]
      simp only [Category.assoc]
    refine
      { lift := fun t ↦ sqp.lift (lX t) (lD t) (hw t)
        fac := ?_
        uniq := ?_ }
    · intro t i
      apply pullback.hom_ext
      · simpa [cp] using (sqp.lift_fst (lX t) (lD t) (hw t)).trans (hlX t i)
      · simpa [cp, Category.assoc] using
          congrArg (fun z ↦ z ≫ c.π.app i) (sqp.lift_snd (lX t) (lD t) (hw t))
            |>.trans (hlD t i)
    · intro t m hm
      apply sqp.hom_ext
      · rw [sqp.lift_fst, hlX t (Classical.arbitrary _)]
        simpa [cp, Category.assoc] using
          congrArg (fun z ↦ z ≫ pullback.fst f (η.app (Classical.arbitrary _)))
            (hm (Classical.arbitrary _))
      · rw [sqp.lift_snd]
        apply hc.hom_ext
        intro i
        rw [hlD]
        simpa [cp, Category.assoc] using
          congrArg (fun z ↦ z ≫ pullback.snd f (η.app i)) (hm i)
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a) := fun a ↦ htrans _ _ a
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DP.map a) := by
    intro i j a
    exact MorphismProperty.pullbackMap (P := @IsAffineHom) (by infer_instance)
      (htrans i j a) (by simp) (by simp [η.naturality])
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a) :=
    fun _ ↦ inferInstanceAs (IsAffineHom (𝟙 S))
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a) :=
    fun _ ↦ inferInstanceAs (IsAffineHom (𝟙 X))
  have : ∀ i : Iᵒᵖ, QuasiCompact (ηg.app i) := fun _ ↦ inferInstanceAs (QuasiCompact f)
  have : ∀ i : Iᵒᵖ, QuasiSeparated (ηg.app i) := fun _ ↦ inferInstanceAs (QuasiSeparated f)
  let sqi (i : Iᵒᵖ) :
      ChosenCartesianSquare (ηe.app i) (ηh.app i) (ηg.app i) (η.app i) :=
    { w := pullback.condition
      isoPullback := Iso.refl _
      hom_fst := by simp [ηe, ηg]
      hom_snd := by simp [ηh, ηg] }
  rw [DerivedCategory.Plus.isIso_iff]
  intro q
  by_cases hq : q < 0
  · have hs := Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (Etale.lowerStar AddCommGrpCat.{u + 1} f)
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 hq
    have : (((Etale.upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).IsGE 0 := by
      rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
      intro i hi
      exact ((Etale.upperStar AddCommGrpCat.{u + 1} g').map_isZero
        (DerivedCategory.Plus.isZero_homology_of_isGE
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0 i hi)).of_iso
        (((Etale.upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlusHomologyFunctorIso
          i).app _).symm
    have ht := Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (Etale.lowerStar AddCommGrpCat.{u + 1} f')
      (((Etale.upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) 0 hq
    exact (((Etale.upperStar AddCommGrpCat.{u + 1} g).map_isZero hs).of_iso
      (((Etale.upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso
        q).app _).symm).isIso ht _
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hq)
    apply higherDirectImage_baseChange_of_limit D DP DS DT c hc cp hcp
      (constCone Iᵒᵖ S) (isLimitConstCone Iᵒᵖ S)
      (constCone Iᵒᵖ X) (isLimitConstCone Iᵒᵖ X)
      η ηe ηg ηh g g' f f'
      (by intro i; simpa [DS, constCone] using hη i)
      (by intro i; simp [cp, ηe, constCone])
      (by intro i; simp [ηg, constCone])
      (by intro i; simp [cp, ηh]) sq sqi
      (fun _ ↦ F) (fun _ ↦ hF)
      (fun _ ↦ (Etale.upperStarId AddCommGrpCat.{u + 1} X).hom.app F)
      (by intro i; simp [DT])
      (by
        intro i j k a b
        simp [DT, Etale.upperStarComp_id_right])
      ((Functor.const I).obj F)
      (fun _ ↦ ((Etale.upperStarId AddCommGrpCat.{u + 1} X).app F).symm)
      (by
        intro i j a
        simp [DT, constCone, Etale.upperStarComp_id_right, ← Functor.map_comp])
      (constCocone I F) (isColimitConstCocone I F) q
    intro i
    change IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f (η.app i)).toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    have := hstage i
    infer_instance

/-- Smooth base change along an inverse limit with affine transitions.
Source: Stacks Project, Tag 0F09, lemma-smooth-base-change-general
(blueprint: lem-kun-0f09).

Proof (following Tag 0F09):
1. For each stage form the cartesian base-change square of `f` along `η.app i`.
   The affine-transition permanence statement `lem-weil-pbc-affine-morphism-
   permanence` and the cone universal property identify its inverse limit with
   `sq`'s square, without an absolute quasi-compactness assumption on `S`.
2. Apply `sbc-thm-smooth-base-change` to each stage.  The smooth leg is
   `η.app i`, the quasi-compact and quasi-separated leg is `f`, and the
   coefficient sheaf is on the constant `X` corner.  This gives the degreewise
   finite-stage exchange isomorphisms.
3. Apply `lem-kun-0ezt` to the transposed system.  Its coefficient system on
   the constant corner is `H^q(E)` with identity transitions, so its colimit is
   `H^q(E)`; Step 1 supplies the limits and Step 2 supplies the stage maps.
4. Use `def-weil-pbc-hypercohomology-filtrations` and
   `lem-weil-pbc-truncation-couple-morphism` to obtain the two truncation exact
   couples.  `lem-kun-bc-map-on-cohomology` identifies their first-page map,
   and `lem-sp-couple-morphism` propagates it to every page.  The hypothesis
   `hE` supplies the torsion condition for every cohomology sheaf.
5. By `lemma-weil-pbc-hypercohomology-convergence` and
   `lemma-weil-pbc-exact-couple-abutment`, the page maps stabilize and induce
   maps on finite abutment filtrations.  Page induction and
   `lem-sp-finite-filtration-induction` make every cohomology map invertible,
   including the degrees below the lower bound.
6. Finally `lem-weil-pbc-derived-plus-iso-on-cohomology` turns the
   cohomology isomorphisms into the asserted isomorphism in `D⁺`.

The stalkwise torsion hypothesis is elementwise; no common annihilator is
assumed.  The empty scheme and zero complex satisfy it vacuously, and the
nonempty directed index is retained explicitly. -/
theorem smoothBaseChange_of_inverseLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : Scheme.{u})
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (η : D ⟶ (Functor.const Iᵒᵖ).obj S)
    (htrans : ∀ (i j : Iᵒᵖ) (a : i ⟶ j), IsAffineHom (D.map a))
    (c : Cone D) (hc : IsLimit c)
    (g : c.pt ⟶ S)
    (hη : ∀ (i : Iᵒᵖ), c.π.app i ≫ η.app i = g)
    (hsm : ∀ (i : Iᵒᵖ), Smooth (η.app i))
    (hqc : ∀ (i : Iᵒᵖ), QuasiCompact (η.app i))
    (hqs : ∀ (i : Iᵒᵖ), QuasiSeparated (η.app i))
    {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {X' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ c.pt}
    (sq : ChosenCartesianSquare g' f' f g)
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : ∀ (q : ℤ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ X)
      (x : ((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj E)),
      ∃ n : ℕ, 0 < n ∧ n • x = 0 ∧ IsUnit (n : Γ(S, ⊤))) :
    IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      sq.toCommSq).app E) := by
  classical
  have _ := hqc
  have _ := hqs
  let τ := Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq
  let P : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    fun F ↦ IsIso (τ.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ (NatTrans.isIso_app_iff_of_iso τ
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e)).1 h⟩
  -- The proved truncation comparison packages the complex step of Tag 0F09.
  apply DerivedCategory.Plus.isIso_app_of_forall_homology τ P (fun _ h ↦ h)
  · intro K n _ q hq
    exact ((Etale.upperStar AddCommGrpCat.{u + 1} g).map_isZero
      (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        (Etale.lowerStar AddCommGrpCat.{u + 1} f) K n hq)).of_iso
      (((Etale.upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryPlusHomologyFunctorIso
        q).app _).symm
  · intro K n _ q hq
    have : ((Etale.upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlus.obj K).IsGE n := by
      rw [← DerivedCategory.Plus.isGE_ι_obj_iff, DerivedCategory.isGE_iff]
      intro i hi
      exact ((Etale.upperStar AddCommGrpCat.{u + 1} g').map_isZero
        (DerivedCategory.Plus.isZero_homology_of_isGE K n i hi)).of_iso
        (((Etale.upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategoryPlusHomologyFunctorIso
          i).app _).symm
    exact Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      (Etale.lowerStar AddCommGrpCat.{u + 1} f') _ n hq
  · intro q
    let F := (DerivedCategory.Plus.homologyFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj E
    have htor : F.IsTorsion := by
      refine Sheaf.IsTorsion.of_isAddTorsion_sheafFiber
        (Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale X) ?_
      rintro ⟨_, ⟨x⟩⟩
      have hst : IsAddTorsion
          (((Scheme.pointSmallEtale (X.algClosurePoint x)).sheafFiber
            (A := AddCommGrpCat.{u + 1})).obj F) := by
        intro v
        obtain ⟨n, hn, hv, _⟩ := hE q _ (X.algClosurePoint x) v
        exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hv⟩
      exact IsAddTorsion.of_surjective
        (f := ((((Scheme.pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso
          AddCommGrpCat.{u + 1}).app F).inv).hom)
        (ConcreteCategory.bijective_of_isIso _).2 hst
    apply single_limit S D η htrans c hc g hη f sq F htor
    intro i
    have := hsm i
    exact single_smooth (IsPullback.of_hasPullback f (η.app i)) F (hE q)

end AlgebraicGeometry
