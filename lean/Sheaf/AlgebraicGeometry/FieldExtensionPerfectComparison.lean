/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal
import Sheaf.CategoryTheory.MateIsoAlongEquivalences

/-! # Purely inseparable comparison of field-extension exchanges

Source: Stacks Project, Tag 0F1C, perfect-closure reduction.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem plusEquivalence
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence] :
    F.mapDerivedCategoryPlus.IsEquivalence := by
  let e := F.asEquivalence
  let : e.functor.Additive := inferInstanceAs F.Additive
  let : e.inverse.Additive := e.inverse_additive
  let G := e.inverse
  let η := (Functor.mapDerivedCategoryPlusIdIso C).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso e.unitIso ≪≫
    Functor.mapDerivedCategoryPlusCompIso F G
  let ε := (Functor.mapDerivedCategoryPlusCompIso G F).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso e.counitIso ≪≫
    Functor.mapDerivedCategoryPlusIdIso D
  exact inferInstanceAs
    (CategoryTheory.Equivalence.mk F.mapDerivedCategoryPlus
      G.mapDerivedCategoryPlus η ε).functor.IsEquivalence

private theorem universalExchange
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {p : X' ⟶ X} {q : Y' ⟶ Y} (sq : CommSq p f' f q)
    [IsUniversalHomeomorphism p] [IsUniversalHomeomorphism q]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app E) := by
  let A := AddCommGrpCat.{u + 1}
  have : (Etale.upperStar A p).IsEquivalence := Etale.isEquivalence_upperStar A p
  have : (Etale.upperStar A q).IsEquivalence := Etale.isEquivalence_upperStar A q
  have : (Etale.upperStar A p).mapDerivedCategoryPlus.IsEquivalence := plusEquivalence _
  have : (Etale.upperStar A q).mapDerivedCategoryPlus.IsEquivalence := plusEquivalence _
  have hm : (mateEquiv (Etale.upperStarLowerStarAdjunction A f).derivedPlus
      (Etale.upperStarLowerStarAdjunction A f').derivedPlus
      (TwoSquare.mk _ _ _ _ (Etale.pullbackSquareComparison A sq).hom)).natTrans =
      Etale.derivedBaseChangeMapPlus A sq := by
    apply Etale.derivedBaseChangeMapPlus_ext A sq
    intro N
    exact Adjunction.derivedPlus_mateEquiv_app_fac
      (Etale.upperStarLowerStarAdjunction A f)
      (Etale.upperStarLowerStarAdjunction A f')
      (TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq).hom)
      (TwoSquare.mk _ _ _ _ (Etale.pullbackSquareComparison A sq).hom)
      (Etale.pullbackSquareComparison_hom_app_factorsh A sq) N
  rw [← hm]
  have := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (Etale.upperStarLowerStarAdjunction A f).derivedPlus
    (Etale.upperStarLowerStarAdjunction A f').derivedPlus
    (Etale.upperStar A q).mapDerivedCategoryPlus (Etale.upperStar A p).mapDerivedCategoryPlus
    (Etale.pullbackSquareComparison A sq)
  infer_instance

private theorem exchange_congr
    {X XM Y YM : Scheme.{u}} {f : X ⟶ Y} {fM : XM ⟶ YM}
    {p p' : XM ⟶ X} {q q' : YM ⟶ Y}
    (hp : p = p') (hq : q = q') (sq : CommSq p fM f q) (sq' : CommSq p' fM f q')
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app E) ↔
      IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq').app E) := by
  subst p'
  subst q'
  rfl

private theorem exchange_diamond
    {X XA XR XM Y YA YR YM : Scheme.{u}}
    {f : X ⟶ Y} {fA : XA ⟶ YA} {fR : XR ⟶ YR} {fM : XM ⟶ YM}
    {aX : XA ⟶ X} {aY : YA ⟶ Y} {bX : XM ⟶ XA} {bY : YM ⟶ YA}
    {rX : XR ⟶ X} {rY : YR ⟶ Y} {cX : XM ⟶ XR} {cY : YM ⟶ YR}
    (sqA : CommSq aX fA f aY) (sqB : CommSq bX fM fA bY)
    (sqR : CommSq rX fR f rY) (sqC : CommSq cX fM fR cY)
    (hX : bX ≫ aX = cX ≫ rX) (hY : bY ≫ aY = cY ≫ rY)
    [IsUniversalHomeomorphism aX] [IsUniversalHomeomorphism aY]
    [IsUniversalHomeomorphism cX] [IsUniversalHomeomorphism cY]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqR).app E) ↔
      IsIso ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sqB).app
        ((Etale.upperStar AddCommGrpCat.{u + 1} aX).mapDerivedCategoryPlus.obj E)) := by
  let A := AddCommGrpCat.{u + 1}
  have := universalExchange sqA E
  have := universalExchange sqC ((Etale.upperStar A rX).mapDerivedCategoryPlus.obj E)
  have : (Etale.upperStar A cY).IsEquivalence := Etale.isEquivalence_upperStar A cY
  have : (Etale.upperStar A cY).mapDerivedCategoryPlus.IsEquivalence := plusEquivalence _
  have hAB := Etale.derivedBaseChangeMapPlus_paste_horiz A sqA sqB
    (sqB.horiz_comp sqA)
  have hRC := Etale.derivedBaseChangeMapPlus_paste_horiz A sqR sqC
    (sqC.horiz_comp sqR)
  have htotal : IsIso ((Etale.derivedBaseChangeMapPlus A
      (sqB.horiz_comp sqA)).app E) ↔
      IsIso ((Etale.derivedBaseChangeMapPlus A (sqC.horiz_comp sqR)).app E) := by
    exact exchange_congr hX hY _ _ E
  rw [hAB, hRC] at htotal
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at htotal
  simp only [isIso_comp_left_iff, isIso_comp_right_iff] at htotal
  rw [isIso_iff_of_reflects_iso] at htotal
  exact htotal.symm

private noncomputable def towerMap {B R P M : Scheme.{u}}
    (a : P ⟶ B) (b : M ⟶ P) (r : R ⟶ B) (c : M ⟶ R)
    (h : b ≫ a = c ≫ r) (W : Over B) :
    ((Over.pullback b).obj ((Over.pullback a).obj W)).left ⟶
      ((Over.pullback r).obj W).left :=
  pullback.lift
    (pullback.fst (pullback.snd W.hom a) b ≫ pullback.fst W.hom a)
    (pullback.snd (pullback.snd W.hom a) b ≫ c) (by
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc, pullback.condition, Category.assoc, h])

private theorem towerMap_square {B R P M : Scheme.{u}}
    (a : P ⟶ B) (b : M ⟶ P) (r : R ⟶ B) (c : M ⟶ R)
    (h : b ≫ a = c ≫ r) (W : Over B) :
    IsPullback (towerMap a b r c h W)
      (pullback.snd (pullback.snd W.hom a) b) (pullback.snd W.hom r) c := by
  have outer := (IsPullback.of_hasPullback (pullback.snd W.hom a) b).paste_horiz
    (IsPullback.of_hasPullback W.hom a)
  have outer' : IsPullback
      (towerMap a b r c h W ≫ pullback.fst W.hom r)
      (pullback.snd (pullback.snd W.hom a) b) W.hom (c ≫ r) := by
    simpa only [towerMap, pullback.lift_fst, h] using outer
  exact outer'.of_right (by simp [towerMap]) (IsPullback.of_hasPullback W.hom r)

private theorem towerMap_naturality {B R P M : Scheme.{u}}
    (a : P ⟶ B) (b : M ⟶ P) (r : R ⟶ B) (c : M ⟶ R)
    (h : b ≫ a = c ≫ r) {T S : Over B} (g : T ⟶ S) :
    towerMap a b r c h T ≫ ((Over.pullback r).map g).left =
      ((Over.pullback b).map ((Over.pullback a).map g)).left ≫
        towerMap a b r c h S := by
  apply pullback.hom_ext <;>
    simp [towerMap, Over.pullback_map_left, Category.assoc]

/-- Invertibility of the canonical field-extension exchange is unchanged by a compatible
purely inseparable extension of both ground fields. No coefficient condition is required.
Source: Stacks Project, Tags 0F1C and 03SI; horizontal pasting Tag 0E47.
(blueprint: lem-kun-purely-inseparable-exchange-comparison)

Proof: The scalar extensions P/K and M/L give universal homeomorphisms on T and S.
Their inverse images are exact equivalences, hence induce equivalences on D+.
The exchange for either purely inseparable square is invertible: it is the mate of
the inverse-image square isomorphism along these equivalences. Paste first along
K to P to M and then along K to L to M. The two outer exchanges agree by the tower
identities. In the horizontal pasting equations all composition comparisons and
both purely inseparable exchanges are invertible. Cancel these factors; this identifies
invertibility of the P-to-M exchange at the pullback of E with invertibility of the
pullback of the K-to-L exchange. The inverse-image equivalence for M/L reflects
isomorphisms, giving both implications. This uses no algebraicity assumption on L/K,
no torsion assumption on E, and applies also to the empty scheme and the zero complex. -/
theorem isIso_fieldExtension_iff_of_purelyInseparable
    (K L P M : Type u) [Field K] [Field L] [Field P] [Field M]
    [Algebra K L] [Algebra K P] [Algebra L M] [Algebra P M] [Algebra K M]
    [IsScalarTower K L M] [IsScalarTower K P M]
    [IsPurelyInseparable K P] [IsPurelyInseparable L M]
    (T S : Over (Spec (.of K))) (g : T ⟶ S)
    (E : DerivedCategory.Plus
      (Sheaf T.left.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    let r := Spec.map (CommRingCat.ofHom (algebraMap K L))
    let a := Spec.map (CommRingCat.ofHom (algebraMap K P))
    let b := Spec.map (CommRingCat.ofHom (algebraMap P M))
    let TP := (Over.pullback a).obj T
    let SP := (Over.pullback a).obj S
    let gP := (Over.pullback a).map g
    let EP := (upperStar AddCommGrpCat.{u + 1} (pullback.fst T.hom a)).mapDerivedCategoryPlus.obj E
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (⟨by simp [Over.pullback_map_left]⟩ : CommSq (pullback.fst T.hom r)
        ((Over.pullback r).map g).left g.left (pullback.fst S.hom r))).app E) ↔
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (⟨by dsimp only [TP, SP]; simp only [Over.pullback_map_left, pullback.lift_fst]⟩ :
        CommSq (pullback.fst TP.hom b)
        ((Over.pullback b).map gP).left gP.left (pullback.fst SP.hom b))).app EP) := by
  classical
  dsimp only
  let a := Spec.map (CommRingCat.ofHom (algebraMap K P))
  let b := Spec.map (CommRingCat.ofHom (algebraMap P M))
  let r := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let c := Spec.map (CommRingCat.ofHom (algebraMap L M))
  have h : b ≫ a = c ≫ r := by
    dsimp only [a, b, r, c]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (IsScalarTower.algebraMap_apply K P M x).symm.trans
      (IsScalarTower.algebraMap_apply K L M x)
  have (W : Over (Spec (.of K))) : IsUniversalHomeomorphism (towerMap a b r c h W) :=
    MorphismProperty.of_isPullback (P := @IsUniversalHomeomorphism)
      (towerMap_square a b r c h W).flip inferInstance
  exact exchange_diamond
    (⟨by simp [Over.pullback_map_left]⟩ :
      CommSq (pullback.fst T.hom a) ((Over.pullback a).map g).left g.left
        (pullback.fst S.hom a))
    (⟨by simp [Over.pullback_map_left]⟩ :
      CommSq (pullback.fst ((Over.pullback a).obj T).hom b)
        ((Over.pullback b).map ((Over.pullback a).map g)).left
        ((Over.pullback a).map g).left
        (pullback.fst ((Over.pullback a).obj S).hom b))
    (⟨by simp [Over.pullback_map_left]⟩ :
      CommSq (pullback.fst T.hom r) ((Over.pullback r).map g).left g.left
        (pullback.fst S.hom r))
    (⟨towerMap_naturality a b r c h g⟩ :
      CommSq (towerMap a b r c h T)
        ((Over.pullback b).map ((Over.pullback a).map g)).left
        ((Over.pullback r).map g).left (towerMap a b r c h S))
    (by simp [towerMap]) (by simp [towerMap]) E

end AlgebraicGeometry.Etale
