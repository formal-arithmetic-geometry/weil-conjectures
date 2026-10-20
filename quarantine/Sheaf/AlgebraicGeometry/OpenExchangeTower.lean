/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.AlgebraicGeometry.OpenSourceComposition
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
/-! The compactification tower calculation for open composition. -/
@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Etale
universe u
set_option autoImplicit false
open CategoryTheory.Abelian
universe v u₁ u₂
private theorem derived_comp_right_unit
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ D) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : G ≅ 𝟭 D) :
    (Functor.rightDerivedFunctorCompIso' F G
      (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F)).hom =
      Functor.whiskerLeft F.rightDerivedFunctor
        (G.rightDerivedFunctorIsoMapDerivedCategory ≪≫
          Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D).hom ≫
        (Functor.rightUnitor F.rightDerivedFunctor).hom := by
  apply (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).rightDerived_ext
    (Functor.rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (.up ℤ))
  ext K
  have hL : (Functor.rightDerivedFunctorCompUnit F G).app K ≫
      (Functor.rightDerivedFunctorCompIso' F G
        (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F)).hom.app
          (DerivedCategory.Qh.obj K) =
      (F ⋙ G).rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorNatTrans
          (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F).hom).app
          (DerivedCategory.Qh.obj K) := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [hL]
  simp only [Functor.rightDerivedFunctorNatTrans, Functor.rightDerivedNatTrans_app,
    Functor.whiskerRight_app]
  let ei := G.rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso D
  change _ = (Functor.rightDerivedFunctorCompUnit F G).app K ≫
    ei.hom.app (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) ≫ 𝟙 _
  rw [Category.comp_id]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [ei.hom.naturality (F.rightDerivedFunctorUnit.app K)]
  simp only [Functor.id_map]
  simp only [ei, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  have hq := congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((F.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hq
  erw [reassoc_of% hq]
  erw [Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app_assoc
    e ((F.mapHomotopyCategory (.up ℤ)).obj K)]
  erw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← DerivedCategory.Qh.map_comp_assoc]
  congr 1
  have hc := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).hom_inv_id_app K
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at hc
  rw [hc]
  erw [Category.id_comp]
  congr 1
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [NatTrans.mapHomotopyCategory_app]
  congr 1
  ext n
  exact Category.comp_id _
private theorem direct_image_right_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f (𝟙 Y)).hom =
      Functor.whiskerLeft (rightDerivedLowerStar (ModuleCat.{u + 1} A) f)
        (rightDerivedLowerStarIdIso A Y).hom ≫ (Functor.rightUnitor _).hom := by
  let B := ModuleCat.{u + 1} A
  have hc := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction B f) (upperStarLowerStarAdjunction B (𝟙 Y))
    (upperStarLowerStarAdjunction B (f ≫ 𝟙 Y)) (lowerStarComp B f (𝟙 Y))
    (upperStarComp B f (𝟙 Y))
    (congrArg Iso.hom (conjugateIsoEquiv_upperStarComp B f (𝟙 Y))).symm
  have hh : (rightDerivedLowerStarComp B f (𝟙 Y)).hom =
      (Functor.rightDerivedFunctorCompIso' (lowerStar B f) (lowerStar B (𝟙 Y))
        (lowerStarComp B f (𝟙 Y))).hom := hc.symm
  rw [hh]
  have he : lowerStarComp B f (𝟙 Y) =
      Functor.isoWhiskerLeft (lowerStar B f) (lowerStarId B Y) ≪≫
        Functor.rightUnitor (lowerStar B f) := lowerStarComp_id_right B f
  rw [he]
  exact derived_comp_right_unit (lowerStar B f) (lowerStar B (𝟙 Y)) (lowerStarId B Y)
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] CategoryTheory.Abelian.toPreadditive
attribute [local irreducible] lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  rightDerivedLowerShriekIso rightDerivedLowerShriekOfCompactificationIso
  unboundedEtaleLowerShriekCompIso openImmersionLowerShriekLowerStarExchange
private theorem comparison_copy (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f] [QuasiCompact f']
    (c : Compactification f) (h : f' = f) :
    rightDerivedLowerShriekIso A (c.copy h) ≪≫ unboundedEtaleLowerShriekCongr A h =
      rightDerivedLowerShriekIso A c := by
  subst h
  simp only [unboundedEtaleLowerShriekCongr, Iso.trans_refl]
  rfl
private theorem congr_symm (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    (unboundedEtaleLowerShriekCongr A h).inv =
      (unboundedEtaleLowerShriekCongr A h.symm).hom := by
  cases h
  rfl
private theorem open_congr_derived (A : Type (u + 1)) [CommRing A]
    {W Z : Scheme.{u}} {i j : W ⟶ Z}
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i = j) :
    mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h =
      Functor.mapDerivedCategoryNatIso (eqToIso (by congr 1)) := by
  cases h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl.symm
set_option backward.isDefEq.respectTransparency false in
private theorem open_square_derived_comp
    (A : Type (u + 1)) [CommRing A]
    {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Z)
    (c : W ⟶ Y) (d : Y ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b]
    [IsOpenImmersion c] [IsOpenImmersion d] (h : a ≫ b = c ≫ d) :
    (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b).inv ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h).hom ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) c d).hom =
    (Functor.mapDerivedCategorySquareIso
      ((openImmersionLowerShriekComp (ModuleCat.{u + 1} A) a b).symm ≪≫
        eqToIso (by congr 1) ≪≫
        openImmersionLowerShriekComp (ModuleCat.{u + 1} A) c d)).hom := by
  rw [open_congr_derived A h]
  simp only [mapDerivedCategoryOpenImmersionLowerShriekComp,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Category.assoc]
private theorem direct_map_id_right (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : DerivedCategoryModule A X} (k : K ⟶ L) :
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) (f ≫ 𝟙 Y)).map k =
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) f).map k := by
  rfl
set_option backward.isDefEq.respectTransparency false in
private theorem mapped_open_factor_congr
    (A : Type (u + 1)) [CommRing A]
    {W X Z : Scheme.{u}} {E : Type*} [Category E]
    (P : DerivedCategoryModule A Z ⥤ E)
    (j j' : W ⟶ X) (b : X ⟶ Z) (k : W ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion b] [IsOpenImmersion k]
    (h : j ≫ b = k) (h' : j' ≫ b = k) (e : j = j')
    (M : DerivedCategoryModule A W) :
    HEq (P.map
      ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) j b).inv.app M ≫
        (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h).hom.app M))
      (P.map
      ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) j' b).inv.app M ≫
        (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h').hom.app M)) := by
  subst e
  rfl
set_option maxHeartbeats 300000 in
-- The explicit tower and derived-unit rewrites exceed the default cumulative heartbeat bound.
set_option backward.isDefEq.respectTransparency false in
/-- The open composition comparison on a compactification is the proper/open tower
interchange followed by the left-adjoint comparison of the square of inverse images.
This is an equality
on every input `M`, before composing with any evaluation counit or proper exchange.
Source: Stacks Project, more-etale.tex, Tags 0F7B and 0F7J; etale-cohomology.tex,
Tags 03S3, 03S6 and 0F70 (blueprint: lem-amb-shriek-open-tower-counit).
Proof: write the compactification as `f = j ≫ r`, its pullback as `(j_U,r_U)`, and
`b = pullback.fst r u`. Write `J,J',B,V,L` for derived open extension and `P,Q` for
proper derived image. Apply `unboundedEtaleLowerShriekCompIso_open_source` to `(v,f)`
and `c`; it supplies the source-open composition factor with terminal model `c.precomp v`.
For `(f_U,u)`, expand `unboundedEtaleLowerShriekCompIso_tower` using
`(u,id)` and the compactification `(v ≫ j,r)` transported along the pullback equation.
Its restriction is exactly `c_U`, and its square gives the proper/open interchange
`Gamma : Q ⋙ L ⟶ B ⋙ P`. Both composite compactifications have open factor `v ≫ j`
and proper factor `r`. The congruence comparison and their model-to-chosen comparisons
therefore cancel. The identity proper comparisons also cancel with those in the
specified open identifications. The two remaining open composition comparisons combine
to `a : J' ⋙ B ≅ V ⋙ J`, giving
`L(t' inverse) ≫ Gamma ≫ P(a) ≫ t`.
The open factor `a` is the left-adjoint comparison for the square of inverse images:
open composition is defined by uniqueness of left adjoints, so its value on the two
factorizations is the conjugate of the square comparison. Applying the exact open
functors termwise gives the displayed `mapDerivedCategorySquareIso` comparison on
unbounded derived categories. The identity and empty opens use the same unit
normalizations and require no exception. The parent theorem separately proves that
this open square comparison is the inverse mate of open base change. -/
theorem openExchange_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S : Scheme.{u}} {f : X ⟶ S} (u : U ⟶ S)
    [IsOpenImmersion u] [IsNoetherian X] [IsNoetherian U] [IsNoetherian S]
    [IsNoetherian (pullback f u)] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f]
    (c : Compactification f) (M : DerivedCategoryModule A (pullback f u)) :
    let δ :=
      Functor.isoWhiskerRight
            (rightDerivedLowerShriekIsoOfIsOpenImmersion A (pullback.fst f u)).symm
            (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
          unboundedEtaleLowerShriekCompIso A (pullback.fst f u) f ≪≫
          unboundedEtaleLowerShriekCongr A (pullback.condition) ≪≫
          (unboundedEtaleLowerShriekCompIso A (pullback.snd f u) u).symm ≪≫
          Functor.isoWhiskerLeft
            (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f u))
            (rightDerivedLowerShriekIsoOfIsOpenImmersion A u)
    let cs := c.ofIsPullback (IsPullback.of_hasPullback f u)
    let _sq := c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f u)
    let a := (Functor.mapDerivedCategorySquareIso
      ((openImmersionLowerShriekComp (ModuleCat.{u + 1} A)
          cs.i (pullback.fst c.g u)).symm ≪≫
        eqToIso (by
          simp only [cs, Compactification.ofIsPullback_i_fst]) ≪≫
        openImmersionLowerShriekComp (ModuleCat.{u + 1} A)
          (pullback.fst f u) c.i)).hom
    δ.inv.app M =
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory.map
        ((rightDerivedLowerShriekIso A cs).inv.app M) ≫
      (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g u).flip).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) cs.i).mapDerivedCategory.obj M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map (a.app M) ≫
      (rightDerivedLowerShriekIso A c).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
          (pullback.fst f u)).mapDerivedCategory.obj M)  := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : HasCompactification u := (Compactification.ofIsOpenImmersion u).hasCompactification
  have : HasCompactification (pullback.fst f u) :=
    (Compactification.ofIsOpenImmersion (pullback.fst f u)).hasCompactification
  have : HasCompactification (pullback.snd f u) :=
    (c.ofIsPullback (IsPullback.of_hasPullback f u)).hasCompactification
  have : HasCompactification (pullback.fst f u ≫ f) :=
    (c.precomp (pullback.fst f u)).hasCompactification
  have : HasCompactification (pullback.snd f u ≫ u) :=
    ((c.precomp (pullback.fst f u)).copy pullback.condition.symm).hasCompactification
  let e₁ := Compactification.ofIsOpenImmersion (pullback.fst f u ≫ c.i)
  let e₂ : Compactification (pullback.snd f u ≫ u) :=
    (c.precomp (pullback.fst f u)).copy pullback.condition.symm
  have h₂ := unboundedEtaleLowerShriekCompIso_tower A (pullback.snd f u) u
    (Compactification.ofIsOpenImmersion u) e₂
  have hterminal : rightDerivedLowerShriekIso A ((Compactification.ofIsOpenImmersion u).comp e₂) ≪≫
      unboundedEtaleLowerShriekCongr A pullback.condition.symm ≪≫
      (rightDerivedLowerShriekIso A (c.comp e₁)).symm = Iso.refl _ := by
    dsimp only [e₁, e₂]
    change rightDerivedLowerShriekIso A
        ((c.precomp (pullback.fst f u)).copy pullback.condition.symm) ≪≫
      unboundedEtaleLowerShriekCongr A pullback.condition.symm ≪≫
        (rightDerivedLowerShriekIso A (c.precomp (pullback.fst f u))).symm = Iso.refl _
    rw [← Iso.trans_assoc, comparison_copy, Iso.self_symm_id]
  have hpre := unboundedEtaleLowerShriekCompIso_open_source A
    (pullback.fst f u) f c
  dsimp only
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  have hpreM := congrArg (fun e ↦ e.inv.app M) hpre
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] at hpreM
  rw [hpreM]
  have h₂M := congr_app h₂ M
  simp only [NatTrans.comp_app] at h₂M
  rw [h₂M]
  simp only [Category.assoc]
  have hterminalM := congrArg (fun e ↦ e.hom.app M) hterminal
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.refl_hom, NatTrans.id_app] at hterminalM
  rw [congr_symm]
  erw [reassoc_of% hterminalM]
  simp only [NatTrans.hcomp_app, Category.assoc]
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory
  let z := rightDerivedLowerStarIdIso A S
  let io := Functor.isoWhiskerLeft J z ≪≫ Functor.rightUnitor J
  have ht : rightDerivedLowerShriekIsoOfIsOpenImmersion A u =
      (rightDerivedLowerShriekIso A (Compactification.ofIsOpenImmersion u)).symm ≪≫ io := rfl
  change (rightDerivedLowerShriekIsoOfIsOpenImmersion A u).inv.app _ ≫ _ = _
  rw [ht]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]
  erw [← io.inv.naturality_assoc]
  dsimp only [rightDerivedLowerShriekOfCompactificationCompIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.assoc, asIso_hom]
  have hid := direct_image_right_unit A e₂.g
  change (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e₂.g (𝟙 S)).hom = _ at hid
  erw [hid]
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.rightUnitor_hom_app,
    Category.assoc]
  dsimp only [io, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app]
  simp only [Category.id_comp]
  have hn := z.inv.naturality
    ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A)
      e₂.isPullback_restrict).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) e₂.restrict.i).mapDerivedCategory.obj M))
  simp only [Functor.id_map] at hn
  erw [← reassoc_of% hn]
  erw [Iso.inv_hom_id_app_assoc]
  erw [Category.id_comp]
  change J.map ((rightDerivedLowerShriekIso A e₂.restrict).inv.app M) ≫
    (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g u).flip).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) e₂.restrict.i).mapDerivedCategory.obj M) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) (c.g ≫ 𝟙 S)).map
      ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
        e₂.restrict.i (pullback.fst c.g u)).inv.app M ≫
        (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
          e₂.restrict_i_fst).hom.app M) ≫ _ = _
  dsimp only [J]
  change (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategory.map
      ((rightDerivedLowerShriekIso A
        (c.ofIsPullback (IsPullback.of_hasPullback f u))).inv.app M) ≫
    (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g u).flip).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
        (c.ofIsPullback (IsPullback.of_hasPullback f u)).i).mapDerivedCategory.obj M) ≫ _ = _
  congr 2
  rw [direct_map_id_right A c.g]
  have hi : e₂.restrict.i =
      (c.ofIsPullback (IsPullback.of_hasPullback f u)).i := by
    dsimp only [e₂, Compactification.restrict, Compactification.ofIsPullback,
      Compactification.ofIsOpenImmersion, Compactification.precomp, Compactification.copy]
    congr 1
  have hq := mapped_open_factor_congr A
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g)
    e₂.restrict.i (c.ofIsPullback (IsPullback.of_hasPullback f u)).i
    (pullback.fst c.g u) (pullback.fst f u ≫ c.i)
    e₂.restrict_i_fst (by simp only [Compactification.ofIsPullback_i_fst]) hi M
  have hq' := eq_of_heq hq
  rw [hq']
  have hf := congr_app (open_square_derived_comp A
    (c.ofIsPullback (IsPullback.of_hasPullback f u)).i (pullback.fst c.g u)
    (pullback.fst f u) c.i (by
      simp only [Compactification.ofIsPullback_i_fst])) M
  simp only [NatTrans.comp_app] at hf
  have hp := congrArg (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map hf
  simpa only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc] using
    ((reassoc_of% hp) ((rightDerivedLowerShriekIso A c).hom.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
        (pullback.fst f u)).mapDerivedCategory.obj M)))
end AlgebraicGeometry.Etale
