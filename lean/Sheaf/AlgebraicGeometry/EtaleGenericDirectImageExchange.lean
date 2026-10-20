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
import WeilConjectures.AlgebraicGeometry.FunctionFieldLimit
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.AlgebraicGeometry.FieldExtensionExchange
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.CategoryTheory.MateIsoAlongEquivalences

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

private theorem over_pullback_isPullback {B S : Scheme.{u}}
    {T Y : Over B} (h : T ⟶ Y) (q : S ⟶ B) :
    IsPullback (pullback.fst T.hom q) (((Over.pullback q).map h).left)
      h.left (pullback.fst Y.hom q) := by
  have outer : IsPullback
      ((((Over.pullback q).map h).left) ≫ pullback.snd Y.hom q)
      (pullback.fst T.hom q) q (h.left ≫ Y.hom) := by
    simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback T.hom q).flip
  exact (outer.of_right (by simp [Over.pullback_map_left])
    (IsPullback.of_hasPullback Y.hom q).flip).flip

private noncomputable def chooseSquare
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) :
    ChosenCartesianSquare g' f' f g :=
  { toCommSq := sq.toCommSq
    isoPullback := sq.isoPullback
    hom_fst := by simp
    hom_snd := by simp }

private theorem isIso_moduleExchange_of_plus
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (E : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hE : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((moduleAbelianForget A X).mapDerivedCategoryPlus.obj E))) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E.obj) := by
  let K := (moduleAbelianForget A X).mapDerivedCategoryPlus.obj E
  have hab : IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
      sq.toCommSq).app K.obj) := by
    rw [exactDerivedBaseChangeMap_agrees_plus sq K]
    infer_instance
  have hc := unbounded_abelian_exchange_comparison A sq
  have := (hc.1 Y').2.2.2.1
  have := (hc.2.1 f).1
  have := (hc.2.1 f').1
  have hi : IsIso (D(moduleAbelianForget A Y').map
      ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E.obj) ≫
      (moduleAbelianUnboundedLowerStarComparison A f').app
        (D((g')^*[ModuleCat.{u + 1} A]).obj E.obj) ≫
      R((f')_*[AddCommGrpCat.{u + 1}]).map
        ((moduleAbelianUnboundedUpperStarIso A g').hom.app E.obj)) := by
    rw [hc.2.2 E.obj]
    exact inferInstanceAs (IsIso (_ ≫ _ ≫
      (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app K.obj))
  have : IsIso (D(moduleAbelianForget A Y').map
      ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E.obj)) :=
    (isIso_comp_right_iff _ _).mp hi
  exact isIso_of_reflects_iso _ D(moduleAbelianForget A Y')

private theorem module_nsmul_id
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hNA : ∀ a : A, N • a = 0)
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    N • 𝟙 F = 0 := by
  have hN : (N : A) = 0 := by simpa only [nsmul_eq_mul, mul_one] using hNA 1
  ext W x
  change N • x = 0
  rw [← Nat.cast_smul_eq_nsmul A, hN, zero_smul]

private theorem module_stalk_annihilated
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hNA : ∀ a : A, N • a = 0)
    {X : Scheme.{u}}
    (E : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) (q : ℤ)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        ((moduleAbelianForget A X).mapDerivedCategoryPlus.obj E))) :
    N • x = 0 := by
  let H := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  have : H.Additive := (Scheme.pointSmallEtale s).sheafFiber_additive
  let F := (_root_.DerivedCategory.Plus.homologyFunctor _ q).obj E
  let j := H.mapIso
    (((moduleAbelianForget A X).mapDerivedCategoryPlusHomologyFunctorIso q).app E).symm
  have hz : N • 𝟙 ((moduleAbelianForget A X ⋙ H).obj F) = 0 := by
    rw [← (moduleAbelianForget A X ⋙ H).map_id,
      ← Functor.map_nsmul, module_nsmul_id A N hNA F, Functor.map_zero]
  apply (ConcreteCategory.bijective_of_isIso j.hom).1
  change j.hom.hom (N • x) = j.hom.hom 0
  rw [map_nsmul, map_zero]
  exact ConcreteCategory.congr_hom hz (j.hom.hom x)

private theorem generic_plus_exchange
    (B : Scheme.{u}) [IsIntegral B] [IsLocallyNoetherian B]
    (U : B.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (Q : Type u) [Field Q] [Algebra Γ(B, U) Q] [IsFractionRing Γ(B, U) Q]
    (T Y : Over B) (h : T ⟶ Y) [QuasiCompact h.left] [QuasiSeparated h.left]
    (E : _root_.DerivedCategory.Plus
      (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : ∀ (q : ℤ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ T.left)
      (x : ((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj E)),
      ∃ n : ℕ, 0 < n ∧ n • x = 0 ∧ IsUnit (n : Γ(Y.left, ⊤))) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (genericDirectImageFirstSquare h
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(B, U) Q)) ≫ hU.fromSpec))).app E) := by
  classical
  have := functionField_isFractionRing_of_isAffineOpen B U hU
  let eR : B.functionField ≃ₐ[Γ(B, U)] Q :=
    IsLocalization.algEquiv (nonZeroDivisors Γ(B, U)) B.functionField Q
  let e : Spec (.of Q) ≅ Spec B.functionField :=
    Scheme.Spec.mapIso eR.toRingEquiv.toCommRingCatIso.op
  let r := Spec.map (CommRingCat.ofHom (algebraMap Γ(B, U) Q)) ≫ hU.fromSpec
  have he : e.hom ≫ B.fromSpecFunctionField = r := by
    rw [B.fromSpecFunctionField_eq_functionFieldCone_comp ⟨U, hU, by
      simpa using (show Nonempty U from inferInstance)⟩]
    dsimp [e, Scheme.functionFieldCone, Scheme.affineOpensRingCocone,
      Scheme.affineOpensDiagramι, Scheme.affineOpensRingDiagram, r]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact eR.commutes a
  let I := OrderDual B.NonemptyAffineOpens
  have : Nonempty I := inferInstanceAs (Nonempty B.NonemptyAffineOpens)
  have : IsDirected I (· ≤ ·) := inferInstanceAs
    (IsDirected B.NonemptyAffineOpens (· ≥ ·))
  let J : Iᵒᵖ ⥤ B.NonemptyAffineOpens := (orderDualEquivalence I).inverse
  have : J.IsEquivalence := (orderDualEquivalence I).isEquivalence_inverse
  let D₀ := J ⋙ B.affineOpensDiagram
  let η₀ := Functor.whiskerLeft J B.affineOpensDiagramι
  let c₀ := (B.functionFieldCone.whisker J).extend e.hom
  have hc₀' : IsLimit (B.functionFieldCone.whisker J) :=
    B.isLimitFunctionFieldCone.whiskerEquivalence (orderDualEquivalence I).symm
  have hc₀ : IsLimit c₀ := IsLimit.ofIsoLimit hc₀'
    (Cone.ext e.symm (by intro i; simp [c₀]))
  have hp₀ (i : Iᵒᵖ) : c₀.π.app i ≫ η₀.app i = r := by
    change (e.hom ≫ B.functionFieldCone.π.app (J.obj i)) ≫
      B.affineOpensDiagramι.app (J.obj i) = r
    rw [Category.assoc, ← B.fromSpecFunctionField_eq_functionFieldCone_comp]
    exact he
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  let D₁ := Over.lift D₀ η₀
  let c₁ := Over.liftCone D₀ η₀ c₀ r hp₀
  have hc₁ : IsLimit c₁ := Over.isLimitLiftCone D₀ η₀ c₀ r hp₀ hc₀
  let P := Over.pullback Y.hom
  let D₂ := D₁ ⋙ P
  let D := D₂ ⋙ Over.forget Y.left
  let c₂ := (Over.forget Y.left).mapCone (P.mapCone c₁)
  let c := c₂.extend (pullbackSymmetry Y.hom r).hom
  have hc : IsLimit c :=
    (isLimitOfPreserves (Over.forget Y.left) (isLimitOfPreserves P hc₁)).extendIso _
  let η : D ⟶ (Functor.const Iᵒᵖ).obj Y.left :=
    { app i := (D₂.obj i).hom
      naturality := by intro i j a; exact (D₂.map a).w }
  have hη (i : Iᵒᵖ) : c.π.app i ≫ η.app i = pullback.fst Y.hom r := by
    simp [c, c₂, c₁, P, D₂, D₁, η, Over.liftCone]
  have hsm (i : Iᵒᵖ) : Smooth (η.app i) := by
    have : IsOpenImmersion (η₀.app i) := by
      change IsOpenImmersion (J.obj i).2.1.fromSpec
      infer_instance
    change Smooth (pullback.snd (η₀.app i) Y.hom)
    infer_instance
  have hqc (i : Iᵒᵖ) : QuasiCompact (η.app i) := by
    have : IsAffine (D₀.obj i) := by
      change IsAffine (Spec _)
      infer_instance
    have : QuasiSeparatedSpace ((J ⋙ (Functor.const B.NonemptyAffineOpens).obj B).obj i) :=
      inferInstanceAs (QuasiSeparatedSpace B)
    have : QuasiCompact (η₀.app i) := quasiCompact_of_compactSpace (η₀.app i)
    change QuasiCompact (pullback.snd (η₀.app i) Y.hom)
    infer_instance
  have hqs (i : Iᵒᵖ) : QuasiSeparated (η.app i) := by
    have : IsOpenImmersion (η₀.app i) := by
      change IsOpenImmersion (J.obj i).2.1.fromSpec
      infer_instance
    change QuasiSeparated (pullback.snd (η₀.app i) Y.hom)
    infer_instance
  have htrans (i j : Iᵒᵖ) (a : i ⟶ j) : IsAffineHom (D.map a) := by
    have : IsAffineHom (D₁.map a).left := by
      change IsAffineHom (D₀.map a)
      change IsAffineHom (Spec.map _)
      infer_instance
    exact MorphismProperty.of_isPullback (P := @IsAffineHom)
      (over_pullback_isPullback (D₁.map a) Y.hom) inferInstance
  exact smoothBaseChange_of_inverseLimit Y.left D η htrans c hc
    (pullback.fst Y.hom r) hη hsm hqc hqs h.left
    (chooseSquare (over_pullback_isPullback h r)) E hE

private theorem field_module_exchange
    (Q L : Type u) [Field Q] [Field L] [Algebra Q L]
    (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hNQ : IsUnit (N : Q)) (hNA : ∀ a : A, N • a = 0)
    (T Y : Over (Spec (.of Q))) (h : T ⟶ Y)
    [QuasiCompact h.left] [QuasiSeparated h.left]
    (E : _root_.DerivedCategory.Plus
      (Sheaf T.left.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (genericDirectImageFirstSquare h
        (Spec.map (CommRingCat.ofHom (algebraMap Q L))))).app E.obj) := by
  apply isIso_moduleExchange_of_plus A
    (chooseSquare (over_pullback_isPullback h _)) E
  apply isIso_derivedBaseChangeMapPlus_fieldExtension Q L T Y h
  intro q Ω _ _ s x
  exact ⟨N, ⟨hN, isUnit_iff_ne_zero.mp hNQ⟩,
    module_stalk_annihilated A N hNA E q Ω s x⟩

private theorem iso_horizontal_exchange
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} [IsIso g'] [IsIso g]
    (sq : CommSq g' f' f g) (E : DerivedCategoryModule A X) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app E) := by
  have := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f')
    D(upperStar (ModuleCat.{u + 1} A) g) D(upperStar (ModuleCat.{u + 1} A) g')
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq)
  exact inferInstanceAs (IsIso ((mateEquiv
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f')
    (TwoSquare.mk _ _ _ _
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom)).natTrans.app E))

private theorem exchange_iso_congr
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {p p' : X' ⟶ X} {q q' : Y' ⟶ Y} (hp : p = p') (hq : q = q')
    (sq : CommSq p f' f q) (sq' : CommSq p' f' f q') (E : DerivedCategoryModule A X) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app E) ↔
      IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq').app E) := by
  subst p'
  subst q'
  rfl

private theorem second_module_exchange
    (Q L : Type u) [Field Q] [Field L] [Algebra Q L]
    (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hNQ : IsUnit (N : Q)) (hNA : ∀ a : A, N • a = 0)
    {B : Scheme.{u}} (q : Spec (.of Q) ⟶ B)
    (T Y : Over B) (h : T ⟶ Y) [QuasiCompact h.left] [QuasiSeparated h.left]
    (E : _root_.DerivedCategory.Plus
      (Sheaf (pullback T.hom q).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (genericDirectImageSecondSquare h q
        (Spec.map (CommRingCat.ofHom (algebraMap Q L))))).app E.obj) := by
  let l := Spec.map (CommRingCat.ofHom (algebraMap Q L))
  let v : Over.mk (l ≫ q) ⟶ Over.mk q := Over.homMk l rfl
  let TQ := (Over.pullback q).obj T
  let YQ := (Over.pullback q).obj Y
  let hQ := (Over.pullback q).map h
  let hL := (Over.pullback (l ≫ q)).map h
  let hQL := (Over.pullback l).map hQ
  have : QuasiCompact hQ.left := MorphismProperty.of_isPullback
    (P := @QuasiCompact) (over_pullback_isPullback h q) inferInstance
  have : QuasiSeparated hQ.left := MorphismProperty.of_isPullback
    (P := @QuasiSeparated) (over_pullback_isPullback h q) inferInstance
  have hcan := field_module_exchange Q L A N hN hNQ hNA TQ YQ hQ E
  let eT : pullback T.hom (l ≫ q) ≅ pullback TQ.hom l :=
    (isPullback_baseChangeMap T.hom v).isoPullback
  let eY : pullback Y.hom (l ≫ q) ≅ pullback YQ.hom l :=
    (isPullback_baseChangeMap Y.hom v).isoPullback
  have heT : eT.hom ≫ pullback.fst TQ.hom l = AlgebraicGeometry.baseChangeMap T.hom v :=
    (isPullback_baseChangeMap T.hom v).isoPullback_hom_fst
  have heY : eY.hom ≫ pullback.fst YQ.hom l = AlgebraicGeometry.baseChangeMap Y.hom v :=
    (isPullback_baseChangeMap Y.hom v).isoPullback_hom_fst
  have heT₂ : eT.hom ≫ pullback.snd TQ.hom l = pullback.snd T.hom (l ≫ q) :=
    (isPullback_baseChangeMap T.hom v).isoPullback_hom_snd
  have heY₂ : eY.hom ≫ pullback.snd YQ.hom l = pullback.snd Y.hom (l ≫ q) :=
    (isPullback_baseChangeMap Y.hom v).isoPullback_hom_snd
  let sqe : CommSq eT.hom hL.left hQL.left eY.hom := ⟨by
    apply pullback.hom_ext
    · simp only [Category.assoc, hQL, Over.pullback_map_left, pullback.lift_fst]
      rw [← Category.assoc, heT, heY]
      exact (genericDirectImageSecondSquare h q l).w
    · simp only [Category.assoc, hQL, Over.pullback_map_left, pullback.lift_snd]
      rw [heT₂, heY₂]
      simp [hL, Over.pullback_map_left]⟩
  let sq₁ := chooseSquare (over_pullback_isPullback hQ l)
  let sq₂ := chooseSquare (IsPullback.of_horiz_isIso sqe)
  have hiso := iso_horizontal_exchange A sqe
    (D(upperStar (ModuleCat.{u + 1} A) (pullback.fst TQ.hom l)).obj E.obj)
  have hi : IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (sq₂.toCommSq.horiz_comp sq₁.toCommSq)).app E.obj) :=
    (moduleExchange_composite_baseChange A sq₁ sq₂).2 E.obj |>.mpr (by infer_instance)
  have hp : eT.hom ≫ pullback.fst TQ.hom l = AlgebraicGeometry.baseChangeMap T.hom v := heT
  have hr : eY.hom ≫ pullback.fst YQ.hom l = AlgebraicGeometry.baseChangeMap Y.hom v := heY
  change IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
    (show CommSq _ _ _ _ from genericDirectImageSecondSquare h q l)).app E.obj)
  change IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
    (sqe.horiz_comp (genericDirectImageFirstSquare hQ l))).app E.obj) at hi
  exact (exchange_iso_congr A hp hr _ (genericDirectImageSecondSquare h q l) E.obj).mp hi

/-- Generic direct-image exchange is invertible and equals the two successive exchanges.
Source: Stacks Project, Tags 0F09 and 0F1C, geometric-generic specialization
(blueprint: lem-sf-etale-generic-direct-image-exchange).

Proof plan (the five steps of the node):
1. By lem-sc-integral-function-field-affine-fraction identify Q with the generic stalk.
   The proved Scheme.isLimitFunctionFieldCone specializes
   lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods to the generic point and
   expresses Spec Q as the inverse limit of nonempty affine opens, with affine transitions.
2. The field F is Noetherian. Lem-weil-pbc-finite-type-over-noetherian and
   lem-weil-pbc-locally-noetherian-quasi-separated make B Noetherian and quasi-separated.
   Lem-weil-pbc-qcqs-morphism-permanence makes the affine neighbourhood inclusions qcqs.
   They are smooth by lem-pc-open-immersion-smooth-composition. Base change preserves
   smoothness (lem-pc-proper-base-change, clause 2) and qcqs. Lift the cone to Over B;
   pullback to Over Y and then forget to schemes. Preservation of connected limits
   identifies Y_Q with the limit of Y ×_B U_i.
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
  have _ := hBdim
  let q := Spec.map (CommRingCat.ofHom (algebraMap Γ(B, U) Q)) ≫ hU.fromSpec
  let l := Spec.map (CommRingCat.ofHom (algebraMap Q L))
  have : IsLocallyNoetherian B :=
    LocallyOfFiniteType.isLocallyNoetherian (B ↘ Spec (.of F))
  have hNY : IsUnit (N : Γ(Y.left, ⊤)) := by
    let φ := (Scheme.ΓSpecIso (.of F)).inv ≫
      Scheme.Γ.map (Y.hom ≫ (B ↘ Spec (.of F))).op
    simpa only [map_natCast] using hNF.map φ.hom
  have hNQ : IsUnit (N : Q) := by
    let φ := (Scheme.ΓSpecIso (.of F)).inv ≫
      Scheme.Γ.map (q ≫ (B ↘ Spec (.of F))).op ≫ (Scheme.ΓSpecIso (.of Q)).hom
    simpa only [map_natCast] using hNF.map φ.hom
  let sq₁ := chooseSquare (over_pullback_isPullback h q)
  have hfirst : IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      sq₁.toCommSq).app E.obj) := by
    apply isIso_moduleExchange_of_plus A sq₁ E
    apply generic_plus_exchange B U hU Q T Y h
    intro i Ω _ _ s x
    exact ⟨N, hN, module_stalk_annihilated A N hNA E i Ω s x, hNY⟩
  let EQ := (upperStar (ModuleCat.{u + 1} A) (pullback.fst T.hom q)).mapDerivedCategoryPlus.obj E
  have hsecond := second_module_exchange Q L A N hN hNQ hNA q T Y h EQ
  have sq₂pb : IsPullback
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
      simpa [AlgebraicGeometry.baseChangeMap] using over_pullback_isPullback h (l ≫ q)
    exact outer.of_right (genericDirectImageSecondSquare h q l).w
      (over_pullback_isPullback h q)
  let sq₂ := chooseSquare sq₂pb
  have : IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq₂.toCommSq).app
      (D(upperStar (ModuleCat.{u + 1} A) (pullback.fst T.hom q)).obj E.obj)) := hsecond
  have hp := moduleExchange_composite_baseChange A sq₁ sq₂
  constructor
  · exact (hp.2 E.obj).mpr (by infer_instance)
  · simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
      Functor.comp_obj, Category.assoc] using NatTrans.congr_app hp.1 E.obj

end AlgebraicGeometry.Etale
