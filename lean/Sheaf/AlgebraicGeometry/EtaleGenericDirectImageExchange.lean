/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.ModuleExchangeCompositeBaseChange
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.AlgebraicGeometry.FieldExtensionExchange
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Generic direct-image exchange with finite constant coefficients

Source: Stacks Project, Tags 0F09 and 0F1C, geometric-generic specialization;
blueprint sec-six-functors, sk-prop-sf-biduality-general
(blueprint: lem-sf-etale-generic-direct-image-exchange).

The helpers describe the two canonical squares on the chosen corners `W ×_B Spec L`,
not iterated pullbacks. In the outer square the projection to W is written as the
composite through `W ×_B Spec Q`; the pullback equations identify it with `pullback.fst`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor


namespace AlgebraicGeometry.Etale

set_option linter.defProp false in
/-- The ordinary generic base-change square (also used for the outer base change).
Only the commutativity proof is packaged: all four maps are the canonical maps of the
chosen pullbacks. Source: Stacks Tags 01JX, 0F09
(blueprint: lem-sf-etale-generic-direct-image-exchange). -/
noncomputable def genericDirectImageFirstSquare {B S : Scheme.{u}}
    {T Y : Over B} (h : T ⟶ Y) (q : S ⟶ B) :
    CommSq (pullback.fst T.hom q) (((Over.pullback q).map h).left)
      h.left (pullback.fst Y.hom q) :=
  ⟨by simp [Over.pullback_map_left]⟩

set_option linter.defProp false in
/-- The field-extension square on the chosen corners `T ×_B S'`, `Y ×_B S'`.
Its horizontal maps are the existing `AlgebraicGeometry.baseChangeMap`, not freely chosen morphisms.
Source: Stacks Tags 01JX, 0F1C; base-change pasting
(blueprint: lem-sf-etale-generic-direct-image-exchange). -/
noncomputable def genericDirectImageSecondSquare {B S S' : Scheme.{u}}
    {T Y : Over B} (h : T ⟶ Y) (q : S ⟶ B) (l : S' ⟶ S) :
    CommSq (AlgebraicGeometry.baseChangeMap T.hom (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q))
      (((Over.pullback (l ≫ q)).map h).left) (((Over.pullback q).map h).left)
      (AlgebraicGeometry.baseChangeMap Y.hom (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q)) :=
  ⟨by
    apply pullback.hom_ext <;>
      simp [AlgebraicGeometry.baseChangeMap, Over.pullback_map_left, Category.assoc]⟩

/-- Both conclusions of the generic-exchange lemma, written on the unbounded module
categories. The outer rectangle has corners `W ×_B S'`; its horizontal projection is
`AlgebraicGeometry.baseChangeMap W.hom l ≫ pullback.fst W.hom q = pullback.fst W.hom (l ≫ q)`.
The displayed equality includes both canonical inverse-image composition comparisons.
Source: Stacks Tags 0F09 and 0F1C, successive base changes
(blueprint: lem-sf-etale-generic-direct-image-exchange). -/
def genericDirectImageExchangeConclusion (A : Type (u + 1)) [CommRing A]
    {B S S' : Scheme.{u}} {T Y : Over B} (h : T ⟶ Y)
    (q : S ⟶ B) (l : S' ⟶ S) (E : DerivedCategoryModule A T.left) : Prop :=
  IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
    ((genericDirectImageSecondSquare h q l).horiz_comp
      (genericDirectImageFirstSquare h q))).app E) ∧
  (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
    ((genericDirectImageSecondSquare h q l).horiz_comp
      (genericDirectImageFirstSquare h q))).app E =
    (moduleInverseImageCompIso A (pullback.fst Y.hom q)
      (AlgebraicGeometry.baseChangeMap Y.hom
        (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q))).inv.app
        ((R(lowerStar (ModuleCat.{u + 1} A) h.left)).obj E) ≫
    D(upperStar (ModuleCat.{u + 1} A)
      (AlgebraicGeometry.baseChangeMap Y.hom (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q))).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
          (genericDirectImageFirstSquare h q)).app E) ≫
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (genericDirectImageSecondSquare h q l)).app
        ((D(upperStar (ModuleCat.{u + 1} A) (pullback.fst T.hom q))).obj E) ≫
    (R(lowerStar (ModuleCat.{u + 1} A) (((Over.pullback (l ≫ q)).map h).left))).map
      ((moduleInverseImageCompIso A (pullback.fst T.hom q)
        (AlgebraicGeometry.baseChangeMap T.hom
          (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q))).hom.app E)

private theorem overPullbackSquare {B S : Scheme.{u}} {T Y : Over B}
    (h : T ⟶ Y) (q : S ⟶ B) :
    IsPullback (pullback.fst T.hom q) ((Over.pullback q).map h).left h.left
      (pullback.fst Y.hom q) := by
  have outer : IsPullback (((Over.pullback q).map h).left ≫ pullback.snd Y.hom q)
      (pullback.fst T.hom q) q (h.left ≫ Y.hom) := by
    simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback T.hom q).flip
  exact (outer.of_right (by simp [Over.pullback_map_left])
    (IsPullback.of_hasPullback Y.hom q).flip).flip

private noncomputable def chosenSquare {X X' Y Y' : Scheme.{u}}
    {p : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) : ChosenCartesianSquare p f' f q :=
  { toCommSq := sq.toCommSq
    isoPullback := sq.isoPullback
    hom_fst := by simp
    hom_snd := by simp }

private theorem moduleExchange_of_abelianPlus (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {p : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {q : Y' ⟶ Y}
    (sq : ChosenCartesianSquare p f' f q)
    (E : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hE : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((moduleAbelianForget A X).mapDerivedCategoryPlus.obj E))) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E.obj) := by
  let K := (moduleAbelianForget A X).mapDerivedCategoryPlus.obj E
  have hab : IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
      K.obj) := by
    rw [exactDerivedBaseChangeMap_agrees_plus sq K]
    infer_instance
  obtain ⟨hforget, hlower, hex⟩ := unbounded_abelian_exchange_comparison A sq
  have := (hforget Y').2.2.2.1
  have := (hlower f).1
  have := (hlower f').1
  have heq := hex E.obj
  have hr : IsIso ((moduleAbelianUnboundedUpperStarIso A q).hom.app
      ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj E.obj) ≫
      (D(upperStar AddCommGrpCat.{u + 1} q)).map
        ((moduleAbelianUnboundedLowerStarComparison A f).app E.obj) ≫
      (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((D(moduleAbelianForget A X)).obj E.obj)) := by
    change IsIso (_ ≫ _ ≫ (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      sq.toCommSq).app K.obj)
    infer_instance
  rw [← heq] at hr
  have hm : IsIso ((D(moduleAbelianForget A Y')).map
      ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E.obj)) :=
    (isIso_comp_right_iff _ _).mp hr
  exact isIso_of_reflects_iso _ (D(moduleAbelianForget A Y'))

private theorem forgottenStalk_annihilated (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hNA : ∀ a : A, N • a = 0) (X : Scheme.{u})
    (E : DerivedCategoryModule A X) (q : ℤ)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (x : ((Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((D(moduleAbelianForget A X)).obj E))) : N • x = 0 := by
  have hN : (N : A) = 0 := by simpa using hNA 1
  let H := D(moduleAbelianForget A X) ⋙ _root_.DerivedCategory.homologyFunctor _ q ⋙
    (Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})
  have := (Scheme.pointSmallEtale t).sheafFiber_additive (A := AddCommGrpCat.{u + 1})
  have : H.Additive := by
    dsimp [H]
    infer_instance
  have he := congrArg H.map (nsmul_id_eq_zero_of_natCast_eq_zero hN E)
  rw [H.map_nsmul, H.map_id, H.map_zero] at he
  exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom he) x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Giving the stalk its explicit unbounded type avoids expensive implicit conversions.
set_option linter.unusedTactic false in
private theorem genericAbelianExchange
    (F : Type u) [Field F] (N : ℕ) (hN : 1 ≤ N) (hNF : IsUnit (N : F))
    (A : Type (u + 1)) [CommRing A] (hNA : ∀ a : A, N • a = 0)
    (B : Scheme.{u}) [B.Over (Spec (.of F))] [IsIntegral B] [IsLocallyNoetherian B]
    (U : B.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (Q : Type u) [Field Q] [Algebra (B.presheaf.obj (op U)) Q]
    [IsFractionRing (B.presheaf.obj (op U)) Q]
    (T Y : Over B) (h : T ⟶ Y) [QuasiCompact h.left] [QuasiSeparated h.left]
    (E : _root_.DerivedCategory.Plus
      (Sheaf T.left.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (genericDirectImageFirstSquare h
        (Spec.map (CommRingCat.ofHom (algebraMap (B.presheaf.obj (op U)) Q)) ≫
          hU.fromSpec))).app ((moduleAbelianForget A T.left).mapDerivedCategoryPlus.obj E)) := by
  classical
  let x := genericPoint B
  let J := {W : B.Opens // IsAffineOpen W ∧ x ∈ W}
  have hlim := Scheme.fromSpecStalk_limit_affine_neighbourhoods B x
  have hne := hlim.2.1
  have hdir := hlim.2.2.1
  have hcompat := hlim.2.2.2.2.2.2.2.2.1
  have huniv := hlim.2.2.2.2.2.2.2.2.2
  let : Nonempty J := hne
  let I := OrderDual J
  let : IsDirectedOrder I := ⟨fun W V ↦ by
    obtain ⟨Z, hZ⟩ := hdir W V
    exact ⟨Z, hZ.trans inf_le_left, hZ.trans inf_le_right⟩⟩
  let : IsFiltered I := isFiltered_of_directed_le_nonempty I
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  let D₀ : Iᵒᵖ ⥤ Scheme.{u} :=
    { obj i := i.unop.1.toScheme
      map f := B.homOfLE (leOfHom f.unop)
      map_id i := B.homOfLE_rfl _
      map_comp f g := (B.homOfLE_homOfLE _ _).symm }
  let η₀ : D₀ ⟶ (Functor.const Iᵒᵖ).obj B :=
    { app i := i.unop.1.ι
      naturality i j f := by simp [D₀] }
  let c₀ : Cone D₀ :=
    { pt := Spec (B.presheaf.stalk x)
      π := { app i := i.unop.1.fromSpecStalkOfMem x i.unop.2.2
             naturality i j f := (hcompat j.unop i.unop (leOfHom f.unop)).symm } }
  have hc₀ : IsLimit c₀ := IsLimit.ofExistsUnique (by
    intro s
    obtain ⟨k, hk, hu⟩ := huniv s.pt (fun W ↦ s.π.app (op W))
      (fun W V hVW ↦ by exact s.w (@homOfLE I _ W V hVW).op)
    refine ⟨k, ?_, ?_⟩
    · intro i
      exact hk i.unop
    · intro f hf
      apply hu f
      intro W
      exact hf (op W))
  have hp₀ (i : Iᵒᵖ) : c₀.π.app i ≫ η₀.app i = B.fromSpecStalk x :=
    i.unop.1.fromSpecStalkOfMem_ι x i.unop.2.2
  let D₁ := Over.lift D₀ η₀
  have : IsFractionRing Γ(B, U) B.functionField :=
    functionField_isFractionRing_of_isAffineOpen B U hU
  let e := IsLocalization.algEquiv (nonZeroDivisors Γ(B, U)) B.functionField Q
  let eR : B.presheaf.stalk x ≅ CommRingCat.of Q :=
    { hom := CommRingCat.ofHom e.toRingHom
      inv := CommRingCat.ofHom e.symm.toRingHom
      hom_inv_id := by ext z; exact e.symm_apply_apply z
      inv_hom_id := by ext z; exact e.apply_symm_apply z }
  let a : Spec (.of Q) ≅ Spec (B.presheaf.stalk x) := Scheme.Spec.mapIso eR.op
  let q := Spec.map (CommRingCat.ofHom (algebraMap Γ(B, U) Q)) ≫ hU.fromSpec
  have he : B.germToFunctionField U ≫ eR.hom =
      CommRingCat.ofHom (algebraMap Γ(B, U) Q) := by
    apply CommRingCat.hom_ext
    ext z
    exact e.commutes z
  have ha : a.hom ≫ B.fromSpecStalk x = q := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk
      (((genericPoint_spec B).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))]
    dsimp only [IsAffineOpen.fromSpecStalk, q]
    rw [← Category.assoc]
    change (Spec.map eR.hom ≫ Spec.map (B.germToFunctionField U)) ≫ _ = _
    rw [← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map f ≫ hU.fromSpec) he
  let cQ : Cone D₀ := c₀.extend a.hom
  have hcQ : IsLimit cQ := IsLimit.extendIso (s := c₀) a.hom hc₀
  have hpQ (i : Iᵒᵖ) : cQ.π.app i ≫ η₀.app i = q := by
    change (a.hom ≫ c₀.π.app i) ≫ η₀.app i = q
    rw [Category.assoc, hp₀, ha]
  let cQ₁ : Cone D₁ := Over.liftCone D₀ η₀ cQ q hpQ
  have hcQ₁ := Over.isLimitLiftCone D₀ η₀ cQ q hpQ hcQ
  let P := Over.pullback Y.hom
  let D₂ := D₁ ⋙ P
  let c₂ := P.mapCone cQ₁
  let D := D₂ ⋙ Over.forget Y.left
  let c₃ := (Over.forget Y.left).mapCone c₂
  let c := c₃.extend (pullbackSymmetry Y.hom q).hom
  have hc : IsLimit c :=
    IsLimit.extendIso (s := c₃) (pullbackSymmetry Y.hom q).hom
      (isLimitOfPreserves (Over.forget Y.left) (isLimitOfPreserves P hcQ₁))
  let η : D ⟶ (Functor.const Iᵒᵖ).obj Y.left :=
    { app i := (D₂.obj i).hom
      naturality i j f := (D₂.map f).w }
  have hη (i : Iᵒᵖ) : c.π.app i ≫ η.app i = pullback.fst Y.hom q := by
    have hw := (P.map (cQ₁.π.app i)).w
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ (pullbackSymmetry Y.hom q).hom ≫ k) hw).trans
        (pullbackSymmetry_hom_comp_snd Y.hom q))
  have hsm (i : Iᵒᵖ) : Smooth (η.app i) := by
    change Smooth (pullback.snd i.unop.1.ι Y.hom)
    infer_instance
  have hqc (i : Iᵒᵖ) : QuasiCompact (η.app i) := by
    have : CompactSpace i.unop.1.toScheme := by
      let : IsAffine i.unop.1.toScheme := i.unop.2.1
      infer_instance
    have : QuasiCompact i.unop.1.ι := inferInstance
    change QuasiCompact (pullback.snd i.unop.1.ι Y.hom)
    infer_instance
  have hqs (i : Iᵒᵖ) : QuasiSeparated (η.app i) := by
    change QuasiSeparated (pullback.snd i.unop.1.ι Y.hom)
    infer_instance
  have htrans (i j : Iᵒᵖ) (f : i ⟶ j) : IsAffineHom (D.map f) := by
    have : IsAffineHom (D₁.map f).left := by
      change IsAffineHom (B.homOfLE (leOfHom f.unop))
      let : IsAffine i.unop.1.toScheme := i.unop.2.1
      let : IsAffine j.unop.1.toScheme := j.unop.2.1
      infer_instance
    exact MorphismProperty.of_isPullback (P := @IsAffineHom)
      (overPullbackSquare (D₁.map f) Y.hom) inferInstance
  apply smoothBaseChange_of_inverseLimit Y.left D η htrans c hc
    (pullback.fst Y.hom q) hη hsm hqc hqs h.left
    (chosenSquare (overPullbackSquare h q))
    ((moduleAbelianForget A T.left).mapDerivedCategoryPlus.obj E)
  intro r Ω _ _ t z
  refine ⟨N, hN, ?_, ?_⟩
  · change N • (z : ((Scheme.pointSmallEtale t).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
        ((_root_.DerivedCategory.homologyFunctor _ r).obj
          ((D(moduleAbelianForget A T.left)).obj E.obj))) = 0
    exact forgottenStalk_annihilated A N hNA T.left E.obj r Ω t z
  · let φ := (Scheme.ΓSpecIso (.of F)).inv ≫ Scheme.Γ.map
      (Y.hom ≫ B ↘ Spec (.of F)).op
    simpa only [map_natCast] using hNF.map φ.hom

set_option backward.isDefEq.respectTransparency false in
private theorem genericSecondPullback {B S S' : Scheme.{u}}
    {T Y : Over B} (h : T ⟶ Y) (q : S ⟶ B) (l : S' ⟶ S) :
    IsPullback
      (AlgebraicGeometry.baseChangeMap T.hom
        (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q))
      (((Over.pullback (l ≫ q)).map h).left) (((Over.pullback q).map h).left)
      (AlgebraicGeometry.baseChangeMap Y.hom
        (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q)) := by
  have outer : IsPullback
      (AlgebraicGeometry.baseChangeMap T.hom
        (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q) ≫ pullback.fst T.hom q)
      (((Over.pullback (l ≫ q)).map h).left) h.left
      (AlgebraicGeometry.baseChangeMap Y.hom
        (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q) ≫ pullback.fst Y.hom q) := by
    have hT : AlgebraicGeometry.baseChangeMap T.hom
        (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q) ≫ pullback.fst T.hom q =
        pullback.fst T.hom (l ≫ q) := by
      simp [AlgebraicGeometry.baseChangeMap]
    have hY : AlgebraicGeometry.baseChangeMap Y.hom
        (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q) ≫ pullback.fst Y.hom q =
        pullback.fst Y.hom (l ≫ q) := by
      simp [AlgebraicGeometry.baseChangeMap]
    rw [hT, hY]
    exact overPullbackSquare h (l ≫ q)
  exact outer.of_right (genericDirectImageSecondSquare h q l).w (overPullbackSquare h q)

private noncomputable def genericIteratedIso {B S S' : Scheme.{u}}
    (W : Over B) (q : S ⟶ B) (l : S' ⟶ S) :
    pullback W.hom (l ≫ q) ≅ pullback (pullback.snd W.hom q) l :=
  (isPullback_baseChangeMap W.hom
    (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q)).isoPullback

set_option backward.isDefEq.respectTransparency false in
private theorem genericIteratedIso_naturality {B S S' : Scheme.{u}}
    {T Y : Over B} (h : T ⟶ Y) (q : S ⟶ B) (l : S' ⟶ S) :
    CommSq (genericIteratedIso T q l).hom (((Over.pullback (l ≫ q)).map h).left)
      (((Over.pullback l).map ((Over.pullback q).map h)).left)
      (genericIteratedIso Y q l).hom := by
  have hf (W : Over B) : (genericIteratedIso W q l).hom ≫
      pullback.fst (pullback.snd W.hom q) l = AlgebraicGeometry.baseChangeMap W.hom
        (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q) :=
    (isPullback_baseChangeMap W.hom
      (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q)).isoPullback_hom_fst
  have hs (W : Over B) : (genericIteratedIso W q l).hom ≫
      pullback.snd (pullback.snd W.hom q) l = pullback.snd W.hom (l ≫ q) :=
    (isPullback_baseChangeMap W.hom
      (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q)).isoPullback_hom_snd
  constructor
  apply pullback.hom_ext
  · simp only [Category.assoc]
    change (genericIteratedIso T q l).hom ≫ _ ≫
      pullback.fst (pullback.snd Y.hom q) l =
      _ ≫ (genericIteratedIso Y q l).hom ≫ pullback.fst (pullback.snd Y.hom q) l
    rw [hf Y]
    change (genericIteratedIso T q l).hom ≫
      pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst, ← Category.assoc]
    change ((genericIteratedIso T q l).hom ≫
      pullback.fst (pullback.snd T.hom q) l) ≫ _ = _
    rw [hf T]
    exact (genericDirectImageSecondSquare h q l).w
  · simp only [Category.assoc]
    change (genericIteratedIso T q l).hom ≫ _ ≫
      pullback.snd (pullback.snd Y.hom q) l =
      _ ≫ (genericIteratedIso Y q l).hom ≫ pullback.snd (pullback.snd Y.hom q) l
    rw [hs Y]
    change (genericIteratedIso T q l).hom ≫
      pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd]
    change (genericIteratedIso T q l).hom ≫
      pullback.snd (pullback.snd T.hom q) l = _
    rw [hs T]
    exact (pullback.lift_snd _ _ _).symm

private theorem moduleExchange_along_isos (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {p : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {q : Y' ⟶ Y}
    (sq : CommSq p f' f q) [IsIso p] [IsIso q] :
    IsIso (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq) := by
  have : (upperStar (ModuleCat.{u + 1} A) p).IsEquivalence :=
    inferInstance
  have : (upperStar (ModuleCat.{u + 1} A) q).IsEquivalence :=
    inferInstance
  exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f')
    D(upperStar (ModuleCat.{u + 1} A) q) D(upperStar (ModuleCat.{u + 1} A) p)
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq)

private theorem moduleExchange_congr (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {p p' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {q q' : Y' ⟶ Y}
    (hp : p = p') (hq : q = q') (sq : CommSq p f' f q) (sq' : CommSq p' f' f q')
    (E : DerivedCategoryModule A X) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app E) ↔
      IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq').app E) := by
  subst p'
  subst q'
  rfl

private theorem moduleFieldExchange
    (Q L : Type u) [Field Q] [Field L] [Algebra Q L]
    (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 1 ≤ N) (hNA : ∀ a : A, N • a = 0) (hNQ : IsUnit (N : Q))
    (T Y : Over (Spec (.of Q))) (h : T ⟶ Y)
    [QuasiCompact h.left] [QuasiSeparated h.left]
    (E : _root_.DerivedCategory.Plus
      (Sheaf T.left.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (genericDirectImageFirstSquare h
        (Spec.map (CommRingCat.ofHom (algebraMap Q L))))).app E.obj) := by
  apply moduleExchange_of_abelianPlus A
    (chosenSquare (overPullbackSquare h (Spec.map (CommRingCat.ofHom (algebraMap Q L))))) E
  apply isIso_derivedBaseChangeMapPlus_fieldExtension Q L T Y h
    ((moduleAbelianForget A T.left).mapDerivedCategoryPlus.obj E)
  intro r Ω _ _ t x
  exact ⟨N, ⟨hN, hNQ.ne_zero⟩, forgottenStalk_annihilated A N hNA T.left E.obj r Ω t x⟩

private theorem moduleSecondExchange
    (Q L : Type u) [Field Q] [Field L] [Algebra Q L]
    (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 1 ≤ N) (hNA : ∀ a : A, N • a = 0) (hNQ : IsUnit (N : Q))
    {B : Scheme.{u}} {T Y : Over B} (h : T ⟶ Y)
    [QuasiCompact h.left] [QuasiSeparated h.left] (q : Spec (.of Q) ⟶ B)
    (E : _root_.DerivedCategory.Plus
      (Sheaf (pullback T.hom q).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (genericDirectImageSecondSquare h q
        (Spec.map (CommRingCat.ofHom (algebraMap Q L))))).app E.obj) := by
  let l := Spec.map (CommRingCat.ofHom (algebraMap Q L))
  let hQ := (Over.pullback q).map h
  have : QuasiCompact hQ.left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (overPullbackSquare h q) inferInstance
  have : QuasiSeparated hQ.left :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (overPullbackSquare h q) inferInstance
  let sqF := chosenSquare (overPullbackSquare hQ l)
  let sqI := chosenSquare (IsPullback.of_horiz_isIso (genericIteratedIso_naturality h q l))
  have := moduleFieldExchange Q L A N hN hNA hNQ
    ((Over.pullback q).obj T) ((Over.pullback q).obj Y) hQ E
  have := moduleExchange_along_isos A sqI.toCommSq
  have hcomp : IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (sqI.toCommSq.horiz_comp sqF.toCommSq)).app E.obj) := by
    apply ((moduleExchange_composite_baseChange A sqF sqI).2 E.obj).mpr
    infer_instance
  apply (moduleExchange_congr A
    (isPullback_baseChangeMap T.hom
      (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q)).isoPullback_hom_fst
    (isPullback_baseChangeMap Y.hom
      (Over.homMk l rfl : Over.mk (l ≫ q) ⟶ Over.mk q)).isoPullback_hom_fst
    (sqI.toCommSq.horiz_comp sqF.toCommSq) (genericDirectImageSecondSquare h q l) E.obj).mp
  exact hcomp

set_option linter.unusedVariables false in
/-- Generic direct-image exchange is invertible and equals the two successive exchanges.
Source: Stacks Project, Tags 0F09 and 0F1C, geometric-generic specialization
(blueprint: lem-sf-etale-generic-direct-image-exchange).

Proof plan (the five steps of the node):
1. By lem-sc-integral-function-field-affine-fraction identify Q with the generic stalk.
   Lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods expresses Spec Q over B as
   the directed limit of its nonempty affine generic neighbourhoods, with affine transitions.
2. The field F is Noetherian. Lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-locally-noetherian-quasi-separated make B Noetherian and quasi-separated.
   Lem-weil-pbc-qcqs-morphism-permanence makes the affine neighbourhood inclusions qcqs.
   They are smooth by lem-pc-open-immersion-smooth-composition. Base change preserves
   smoothness (lem-pc-proper-base-change, clause 2) and qcqs. The constant Y and B systems
   and lem-weil-pbc-limit-fibre-products identify Y_Q with the limit of Y ×_B U_i.
3. Forget coefficients using lem-kun-unbounded-abelian-exchange-comparison. Since NA=0,
   all cohomology stalks are N-torsion, and the inverse of N in F remains an inverse on
   Y and all its base changes. The underlying object is bounded below. Apply lem-kun-0f09
   to h with stages Y ×_B U_i and limit Y_Q. Lem-kun-unbounded-exchange-agrees identifies
   the bounded-below and unbounded abelian mates. The endpoint comparison isomorphisms
   and conservativity in lem-kun-unbounded-abelian-exchange-comparison give invertibility
   of the actual module exchange to Q.
4. The base change h_Q is qcqs by lem-weil-pbc-qcqs-morphism-permanence. Exact inverse
   image (prop-weil-pbc-inverse-image-modules-exact) preserves bounded belowness. Apply
   lem-kun-0f1c-exchange to L/Q, including its inseparable case. The same forgetting and
   bounded-below comparison gives the unbounded module exchange on iterated corners.
   By def-pc-base-change and lem-weil-pbc-cartesian-square-pasting the canonical maps
   from W_L to (W_Q)_L are isomorphisms respecting both projections. Their inverse images
   are equivalences by lem-weil-pbc-inverse-image-composition (2),(3); hence their mate
   is invertible by lem-weil-mate-iso-along-equivalences. Apply
   lem-fin-module-exchange-composite-base-change to obtain the exchange for the chosen
   second square on W_L itself.
5. Paste these two squares. By def-pc-base-change their horizontal composite is the
   geometric-generic square. Lem-fin-module-exchange-composite-base-change gives exactly
   the four-arrow equality in genericDirectImageExchangeConclusion, including the two
   moduleInverseImageCompIso comparisons. Its middle arrows are isomorphisms by steps
   3 and 4; functors preserve inverses and composites of isomorphisms are isomorphisms.
   This proves both invertibility of the specified mate and the compatibility clause. -/
theorem genericDirectImageExchange
    (F : Type u) [Field F] [IsAlgClosed F]
    (N : ℕ) (hN : 1 ≤ N) (hNF : IsUnit (N : F))
    (A : Type (u + 1)) [CommRing A] [Finite A] (hNA : ∀ a : A, N • a = 0)
    (B : Scheme.{u}) [B.Over (Spec (.of F))]
    [Smooth (B ↘ Spec (.of F))] [IsIntegral B]
    [LocallyOfFiniteType (B ↘ Spec (.of F))] [QuasiCompact (B ↘ Spec (.of F))]
    (hBdim : topologicalKrullDim B = 1)
    (U : B.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (Q : Type u) [Field Q] [Algebra (B.presheaf.obj (op U)) Q]
    [IsFractionRing (B.presheaf.obj (op U)) Q]
    (L : Type u) [Field L] [Algebra Q L] [IsAlgClosed L] [Algebra.IsAlgebraic Q L]
    (T Y : Over B) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (h : T ⟶ Y) [QuasiCompact h.left] [QuasiSeparated h.left]
    (E : _root_.DerivedCategory.Plus (Sheaf T.left.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    genericDirectImageExchangeConclusion A h
      (Spec.map (CommRingCat.ofHom (algebraMap (B.presheaf.obj (op U)) Q)) ≫ hU.fromSpec)
      (Spec.map (CommRingCat.ofHom (algebraMap Q L))) E.obj := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap (B.presheaf.obj (op U)) Q)) ≫
    hU.fromSpec
  let l := Spec.map (CommRingCat.ofHom (algebraMap Q L))
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian
    (B ↘ Spec (.of F))
  let sq₁ := chosenSquare (overPullbackSquare h q)
  let sq₂ := chosenSquare (genericSecondPullback h q l)
  have hfirst := genericAbelianExchange F N hN hNF A hNA B U hU Q T Y h E
  have := moduleExchange_of_abelianPlus A sq₁ E hfirst
  let EQ := (upperStar (ModuleCat.{u + 1} A) (pullback.fst T.hom q)).mapDerivedCategoryPlus.obj E
  have hNQ : IsUnit (N : Q) := by
    let φ := (Scheme.ΓSpecIso (.of F)).inv ≫ Scheme.Γ.map
      (q ≫ B ↘ Spec (.of F)).op ≫ (Scheme.ΓSpecIso (.of Q)).hom
    simpa only [map_natCast] using hNF.map φ.hom
  have := moduleSecondExchange Q L A N hN hNA hNQ h q EQ
  obtain ⟨heq, hiso⟩ := moduleExchange_composite_baseChange A sq₁ sq₂
  constructor
  · apply (hiso E.obj).mpr
    change IsIso (_ ≫ (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (genericDirectImageSecondSquare h q l)).app EQ.obj)
    infer_instance
  · simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] using
      congrArg (fun α ↦ α.app E.obj) heq

end AlgebraicGeometry.Etale
