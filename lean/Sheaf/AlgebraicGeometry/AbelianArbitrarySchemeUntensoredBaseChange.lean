/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
import Sheaf.Targets.BaseChangeTowardsFields
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.AlgebraicGeometry.HigherDirectImagesLimits
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import WeilConjectures.AlgebraicGeometry.AffineFibreProductTransition
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion

/-! Abelian-coefficient untensored base change for arbitrary affine schemes.

Source: Stacks Project, Tags 0F1I and 0EZT, arbitrary-scheme reduction in Tag 0F1J.
(blueprint: lem-kun-0f1j-abelian-arbitrary-scheme-untensored-base-change)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true


private theorem bounded_exchange_iso
    {X X' Y Y' : Scheme.{u}} {e : X' ⟶ X} {h : X' ⟶ Y'}
    {g : X ⟶ Y} {f : Y' ⟶ Y} (sq : ChosenCartesianSquare e h g f)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ha : IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj A))) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A)) := by
  have ha' := (NatTrans.isIso_app_iff_of_iso
    (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)
    ((_root_.DerivedCategory.Plus.singleFunctorιIso _ 0).app A)).2 ha
  change IsIso ((exactDerivedBaseChangeMap AddCommGrpCat.{u + 1}
    sq.toCommSq).app (_root_.DerivedCategory.Plus.ι.obj
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A))) at ha'
  have heq := exactDerivedBaseChangeMap_agrees_plus sq
    ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A)
  have hcomp := heq ▸ ha'
  have hi := (isIso_comp_left_iff _ _).1 hcomp
  have hj := (isIso_comp_right_iff _ _).1 hi
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ _ hj inferInstance

private theorem exchange_isIso_of_nonnegative
    {X X' Y Y' : Scheme.{u}} {e : X' ⟶ X} {h : X' ⟶ Y'}
    {g : X ⟶ Y} {f : Y' ⟶ Y} (sq : CommSq e h g f)
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hn : ∀ q : ℕ, IsIso ((_root_.DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A)))) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A)) := by
  let P := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A
  let U := upperStar AddCommGrpCat.{u + 1} f
  let V := upperStar AddCommGrpCat.{u + 1} e
  let L := lowerStar AddCommGrpCat.{u + 1} g
  let L' := lowerStar AddCommGrpCat.{u + 1} h
  apply (_root_.DerivedCategory.Plus.isIso_iff _).2
  intro q
  by_cases hq : q < 0
  · have hz₁ : IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj
        (U.mapDerivedCategoryPlus.obj (L.rightDerivedFunctorPlus.obj P))) := by
      refine IsZero.of_iso ?_
        (U.mapDerivedCategoryPlusHomologyFunctorIso q |>.app _).symm
      exact U.map_isZero
        (L.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE P 0 hq)
    have : (V.mapDerivedCategoryPlus.obj P).IsGE 0 := by
      rw [← _root_.DerivedCategory.Plus.isGE_ι_obj_iff,
        _root_.DerivedCategory.isGE_iff]
      intro i hi
      refine IsZero.of_iso ?_
        (V.mapDerivedCategoryPlusHomologyFunctorIso i |>.app _).symm
      exact V.map_isZero (_root_.DerivedCategory.Plus.isZero_homology_of_isGE P 0 i hi)
    exact hz₁.isIso
      (L'.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        (V.mapDerivedCategoryPlus.obj P) 0 hq) _
  · have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
    rw [← he]
    exact hn q.toNat

private theorem constant_limit_homology
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {S T : Scheme.{u}} (g : T ⟶ S) [QuasiCompact g] [QuasiSeparated g]
    (DX DY : Iᵒᵖ ⥤ Scheme.{u})
    (cX : Cone DX) (hcX : IsLimit cX) (cY : Cone DY) (hcY : IsLimit cY)
    (ηf : DX ⟶ (Functor.const Iᵒᵖ).obj S)
    (ηe : DY ⟶ (Functor.const Iᵒᵖ).obj T) (ηh : DY ⟶ DX)
    (f : cX.pt ⟶ S) (e : cY.pt ⟶ T) (h : cY.pt ⟶ cX.pt)
    (hf : ∀ i, cX.π.app i ≫ ηf.app i = f)
    (he : ∀ i, cY.π.app i ≫ ηe.app i = e)
    (hh : ∀ i, cY.π.app i ≫ ηh.app i = h ≫ cX.π.app i)
    (sq : ChosenCartesianSquare e h g f)
    (sqi : ∀ i, ChosenCartesianSquare (ηe.app i) (ηh.app i) g (ηf.app i))
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
    (A : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (hA : Sheaf.IsTorsion A)
    (q : ℕ)
    (hs : ∀ i, IsIso ((_root_.DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} (sqi i).toCommSq).app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A)))) :
    IsIso ((_root_.DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A))) := by
  have : IsDirectedOrder I := ⟨IsDirected.directed⟩
  have : IsConnected I := IsFiltered.isConnected I
  let DS := (Functor.const Iᵒᵖ).obj S
  let DT := (Functor.const Iᵒᵖ).obj T
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a) :=
    fun _ ↦ inferInstanceAs (IsAffineHom (𝟙 S))
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a) :=
    fun _ ↦ inferInstanceAs (IsAffineHom (𝟙 T))
  let ηg : DT ⟶ DS := (Functor.const Iᵒᵖ).map g
  have : ∀ i, QuasiCompact (ηg.app i) := fun _ ↦ inferInstanceAs (QuasiCompact g)
  have : ∀ i, QuasiSeparated (ηg.app i) := fun _ ↦ inferInstanceAs (QuasiSeparated g)
  let E := upperStarId AddCommGrpCat.{u + 1} T
  have hunit : (upperStarComp AddCommGrpCat.{u + 1} (𝟙 T) (𝟙 T) (𝟙 T)
      (Category.id_comp (𝟙 T)).symm).hom.app A ≫
      (upperStar AddCommGrpCat.{u + 1} (𝟙 T)).map (E.hom.app A) = 𝟙 _ := by
    rw [upperStarComp_id_right AddCommGrpCat.{u + 1} (𝟙 T)]
    simp [E, ← Functor.map_comp]
  let φ {i j : I} (_ : i ⟶ j) := E.hom.app A
  let D := (Functor.const I).obj A
  apply higherDirectImage_baseChange_of_limit DX DY DS DT cX hcX cY hcY
    (constCone Iᵒᵖ S) (isLimitConstCone Iᵒᵖ S)
    (constCone Iᵒᵖ T) (isLimitConstCone Iᵒᵖ T) ηf ηe ηg ηh f e g h
    (fun i ↦ by simpa using hf i) (fun i ↦ by simpa using he i)
    (fun _ ↦ by simp [ηg]) hh sq sqi (fun _ ↦ A) (fun _ ↦ hA) @φ
    (fun _ ↦ by simp [φ, DT, E]) ?_ D (fun _ ↦ E.symm.app A) ?_
    (constCocone I A) (isColimitConstCocone I A) q hs
  · intro i j k a b
    change E.hom.app A =
      (upperStarComp AddCommGrpCat.{u + 1} (𝟙 T) (𝟙 T) (𝟙 T)
        (Category.id_comp (𝟙 T)).symm).hom.app A ≫
        (upperStar AddCommGrpCat.{u + 1} (𝟙 T)).map (E.hom.app A) ≫ E.hom.app A
    simpa only [Category.id_comp, Category.assoc] using
      (congrArg (fun m ↦ m ≫ E.hom.app A) hunit).symm
  · intro i j a
    change 𝟙 A ≫ E.inv.app A = E.inv.app A ≫
      (upperStarComp AddCommGrpCat.{u + 1} (𝟙 T) (𝟙 T) (𝟙 T)
        (Category.id_comp (𝟙 T)).symm).hom.app A ≫
        (upperStar AddCommGrpCat.{u + 1} (𝟙 T)).map (E.hom.app A)
    simpa only [Category.id_comp, Category.comp_id, Category.assoc] using
      (congrArg (fun m ↦ E.inv.app A ≫ m) hunit).symm

private noncomputable def pbSystem
    {I : Type u} [Category I] (X S T : I ⥤ Scheme.{u}) (f : X ⟶ S) (g : T ⟶ S) :=
  PullbackCone.combine f g (fun i ↦ pullback.cone (f.app i) (g.app i))
    (fun i ↦ pullback.isLimit (f.app i) (g.app i))

private theorem pbSystem_map
    {I : Type u} [Category I] (X S T : I ⥤ Scheme.{u}) (f : X ⟶ S) (g : T ⟶ S)
    {i j : I} (a : i ⟶ j) :
    (pbSystem X S T f g).pt.map a =
      pullback.map (f.app i) (g.app i) (f.app j) (g.app j)
        (X.map a) (T.map a) (S.map a) (f.naturality a).symm (g.naturality a).symm := by
  have ha (i) : (pbSystem X S T f g).fst.app i = pullback.fst (f.app i) (g.app i) := rfl
  have hb (i) : (pbSystem X S T f g).snd.app i = pullback.snd (f.app i) (g.app i) := rfl
  apply pullback.hom_ext
  · simpa only [ha, pullback.map, pullback.lift_fst] using
      (pbSystem X S T f g).fst.naturality a
  · simpa only [hb, pullback.map, pullback.lift_snd] using
      (pbSystem X S T f g).snd.naturality a

private noncomputable def pbLimitCone
    {I : Type u} [Category I] (X S T : I ⥤ Scheme.{u}) (f : X ⟶ S) (g : T ⟶ S)
    (cX : Cone X) (cS : Cone S) (cT : Cone T)
    (F : cX.pt ⟶ cS.pt) (G : cT.pt ⟶ cS.pt)
    (hF : ∀ i, F ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hG : ∀ i, G ≫ cS.π.app i = cT.π.app i ≫ g.app i) :
    Cone (pbSystem X S T f g).pt where
  pt := pullback F G
  π := {
    app i := pullback.lift (pullback.fst F G ≫ cX.π.app i)
      (pullback.snd F G ≫ cT.π.app i) (by
        rw [Category.assoc, ← hF, ← Category.assoc, pullback.condition,
          Category.assoc, hG, Category.assoc])
    naturality i j a := by
      dsimp
      apply pullback.hom_ext
      · simp [pbSystem_map, Category.assoc]
      · simp [pbSystem_map, Category.assoc] }

private noncomputable def pbLimitIsLimit
    {I : Type u} [Category I] (X S T : I ⥤ Scheme.{u}) (f : X ⟶ S) (g : T ⟶ S)
    (cX : Cone X) (hcX : IsLimit cX) (cS : Cone S) (hcS : IsLimit cS)
    (cT : Cone T) (hcT : IsLimit cT)
    (F : cX.pt ⟶ cS.pt) (G : cT.pt ⟶ cS.pt)
    (hF : ∀ i, F ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hG : ∀ i, G ≫ cS.π.app i = cT.π.app i ≫ g.app i) :
    IsLimit (pbLimitCone X S T f g cX cS cT F G hF hG) where
  lift q := pullback.lift (hcX.map q (pbSystem X S T f g).fst)
    (hcT.map q (pbSystem X S T f g).snd) (by
      apply hcS.hom_ext
      intro i
      simp only [Category.assoc, hF, hG, IsLimit.map_π_assoc]
      exact congrArg (q.π.app i ≫ ·) (pullback.condition (f := f.app i) (g := g.app i)))
  fac q i := by
    apply pullback.hom_ext <;> simp [pbLimitCone, Category.assoc]
    <;> rfl
  uniq q m hm := by
    apply pullback.hom_ext
    · apply hcX.hom_ext
      intro i
      have hh := congrArg (· ≫ (pbSystem X S T f g).fst.app i) (hm i)
      simpa [pbLimitCone, pbSystem, Category.assoc] using hh
    · apply hcT.hom_ext
      intro i
      have hh := congrArg (· ≫ (pbSystem X S T f g).snd.app i) (hm i)
      simpa [pbLimitCone, pbSystem, Category.assoc] using hh

private noncomputable def chosenFlipPullback {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    ChosenCartesianSquare (pullback.snd f g) (pullback.fst f g) g f :=
  let p := (IsPullback.of_hasPullback f g).flip
  { toCommSq := p.toCommSq
    isoPullback := p.isoPullback
    hom_fst := p.isoPullback_hom_fst
    hom_snd := p.isoPullback_hom_snd }

private theorem finiteType_product_exchange
    {K : Type u} [Field K] {Z S' T : Scheme.{u}}
    (z : Z ⟶ Spec (.of K)) [LocallyOfFiniteType z] [QuasiCompact z]
    [S'.Over (Spec (.of K))] (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    (A : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : IsTorsionOfInvertibleOrder K (Over.mk (g ≫ (S' ↘ Spec (.of K)))) A) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (chosenFlipPullback (pullback.snd z (S' ↘ Spec (.of K))) g).toCommSq).app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A)) := by
  let : T.Over (Spec (.of K)) := ⟨g ≫ (S' ↘ Spec (.of K))⟩
  let : g.IsOver (Spec (.of K)) := ⟨rfl⟩
  exact bounded_exchange_iso
    (chosenFlipPullback (pullback.snd z (S' ↘ Spec (.of K))) g) A
    (baseChange_towardsSpecField z g A hA)

private theorem product_limit_exchange
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {B S T : Scheme.{u}} (s : S ⟶ B) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (DZ : Iᵒᵖ ⥤ Scheme.{u}) (cZ : Cone DZ) (hcZ : IsLimit cZ)
    (ηz : DZ ⟶ (Functor.const Iᵒᵖ).obj B) (z : cZ.pt ⟶ B)
    (hz : ∀ i, cZ.π.app i ≫ ηz.app i = z)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DZ.map a)]
    (A : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (hA : A.IsTorsion)
    (hs : ∀ i, IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (chosenFlipPullback (pullback.snd (ηz.app i) s) g).toCommSq).app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A))) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (chosenFlipPullback (pullback.snd z s) g).toCommSq).app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A)) := by
  have : IsDirectedOrder I := ⟨IsDirected.directed⟩
  have : IsConnected I := IsFiltered.isConnected I
  let DB := (Functor.const Iᵒᵖ).obj B
  let DS := (Functor.const Iᵒᵖ).obj S
  let DT := (Functor.const Iᵒᵖ).obj T
  let ηs : DS ⟶ DB := (Functor.const Iᵒᵖ).map s
  let ηg : DT ⟶ DS := (Functor.const Iᵒᵖ).map g
  let b := constCone Iᵒᵖ B
  let c := constCone Iᵒᵖ S
  let t := constCone Iᵒᵖ T
  let p := pbSystem DZ DB DS ηz ηs
  let cx := pbLimitCone DZ DB DS ηz ηs cZ b c z s
    (fun i ↦ (Category.comp_id z).trans (hz i).symm) (fun _ ↦ by simp [b, c, ηs])
  have hcx : IsLimit cx := pbLimitIsLimit DZ DB DS ηz ηs cZ hcZ b
    (isLimitConstCone _ _) c (isLimitConstCone _ _) z s _ _
  let r := pbSystem p.pt DS DT p.snd ηg
  let cy := pbLimitCone p.pt DS DT p.snd ηg cx c t (pullback.snd z s) g
    (fun i ↦ by simp [cx, pbLimitCone, p, pbSystem, c])
    (fun _ ↦ by simp [c, t, ηg])
  have hcy : IsLimit cy := pbLimitIsLimit p.pt DS DT p.snd ηg cx hcx c
    (isLimitConstCone _ _) t (isLimitConstCone _ _) (pullback.snd z s) g _ _
  have hp {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (p.pt.map a) := by
    rw [pbSystem_map]
    have : IsAffineHom (DB.map a) := inferInstanceAs (IsAffineHom (𝟙 B))
    have : IsAffineHom (DS.map a) := inferInstanceAs (IsAffineHom (𝟙 S))
    exact isAffineHom_pullback_map _ _ _ _ _ _ _ _ _
  have hr {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (r.pt.map a) := by
    rw [pbSystem_map]
    have : IsAffineHom (DS.map a) := inferInstanceAs (IsAffineHom (𝟙 S))
    have : IsAffineHom (DT.map a) := inferInstanceAs (IsAffineHom (𝟙 T))
    exact isAffineHom_pullback_map _ _ _ _ _ _ _ _ _
  apply exchange_isIso_of_nonnegative
  intro q
  apply constant_limit_homology g p.pt r.pt cx hcx cy hcy p.snd r.snd r.fst
    (pullback.snd z s) (pullback.snd (pullback.snd z s) g)
    (pullback.fst (pullback.snd z s) g)
    (fun _ ↦ by simp [cx, pbLimitCone, p, pbSystem, c])
    (fun _ ↦ by simp [cy, pbLimitCone, r, pbSystem, t])
    (fun _ ↦ by simp [cy, pbLimitCone, r, pbSystem])
    (chosenFlipPullback (pullback.snd z s) g)
    (fun i ↦ chosenFlipPullback (pullback.snd (ηz.app i) s) g) A hA q
  intro i
  change IsIso ((_root_.DerivedCategory.Plus.homologyFunctor
    (Sheaf (pullback (ηz.app i) s).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (chosenFlipPullback (pullback.snd (ηz.app i) s) g).toCommSq).app
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A)))
  have := hs i
  infer_instance

private theorem affine_product_exchange
    {K : Type u} [Field K] {Z S' T : Scheme.{u}} [IsAffine Z]
    (z : Z ⟶ Spec (.of K)) [S'.Over (Spec (.of K))]
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    (A : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : IsTorsionOfInvertibleOrder K (Over.mk (g ≫ (S' ↘ Spec (.of K)))) A) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (chosenFlipPullback (pullback.snd z (S' ↘ Spec (.of K))) g).toCommSq).app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj A)) := by
  let B := Γ(Z, ⊤)
  let kB : CommRingCat.of K ⟶ B := (Scheme.ΓSpecIso (.of K)).inv ≫ z.appTop
  let : Algebra K B := kB.hom.toAlgebra
  let I := {C : Subalgebra K B // C.FG}
  have : IsDirected I (· ≤ ·) := inferInstance
  let DZ : Iᵒᵖ ⥤ Scheme.{u} :=
    (CommRingCat.fgSubalgebraDiagramOf K B).op ⋙ Scheme.Spec
  let c₀ : Cone DZ := Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCoconeOf K B).op
  have hc₀ : IsLimit c₀ := isLimitOfPreserves Scheme.Spec
    (CommRingCat.isColimitFGSubalgebraCocone K B).op
  let cZ := c₀.extend Z.isoSpec.hom
  have hcZ : IsLimit cZ := hc₀.ofIsoLimit (Cone.extendIso c₀ Z.isoSpec.symm)
  let ηz : DZ ⟶ (Functor.const Iᵒᵖ).obj (Spec (.of K)) := {
    app i := Spec.map (CommRingCat.ofHom (algebraMap K i.unop.1))
    naturality i j a := by
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp]
      rfl }
  have hZ : Z.isoSpec.hom ≫ Spec.map kB = z := by
    dsimp only [kB]
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Category.assoc, ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]
  have hz (i : Iᵒᵖ) : cZ.π.app i ≫ ηz.app i = z := by
    change (Z.isoSpec.hom ≫ Spec.map _) ≫ Spec.map _ = z
    rw [Category.assoc, ← Spec.map_comp]
    exact hZ
  have ht : A.IsTorsion := (Scheme.isTorsion_iff_isAddTorsion_sheafFiber A).2 (by
    intro Ω _ _ s x
    obtain ⟨n, hn, hx⟩ := hA Ω s x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn.1, hx⟩)
  have {i j : Iᵒᵖ} (a : i ⟶ j) : IsAffineHom (DZ.map a) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  apply product_limit_exchange (S' ↘ Spec (.of K)) g DZ cZ hcZ ηz z hz A ht
  intro i
  have : Algebra.FiniteType K i.unop.1 := i.unop.1.fg_iff_finiteType.mp i.unop.2
  have : LocallyOfFiniteType (ηz.app i) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (by
      change (algebraMap K i.unop.1).FiniteType
      exact (RingHom.finiteType_algebraMap (A := K) (B := i.unop.1)).2 inferInstance)
  have : QuasiCompact (ηz.app i) := inferInstanceAs (QuasiCompact (Spec.map _))
  exact finiteType_product_exchange (ηz.app i) g A hA

/-- Abelian-coefficient base change for an arbitrary affine scheme over a field.
Write its coordinate algebra as the filtered union of its finitely generated subalgebras.
The finite-type field theorem proves each stage exchange, and continuity for higher direct
images identifies the exchange at the limit. Negative cohomology vanishes by left exactness.
(blueprint: lem-kun-0f1j-abelian-arbitrary-scheme-untensored-base-change)
-/
theorem abelian_affineScheme_untensored_baseChange
    {K : Type u} [Field K] {Z S' T : Scheme.{u}} [IsAffine Z]
    (z : Z ⟶ Spec (.of K)) [S'.Over (Spec (.of K))]
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    (A : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : IsTorsionOfInvertibleOrder K (Over.mk (g ≫ (S' ↘ Spec (.of K)))) A) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (CommSq.mk (pullback.condition
        (f := pullback.snd z (S' ↘ Spec (.of K))) (g := g)).symm)).app
      ((_root_.DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj A)) := by
  exact affine_product_exchange z g A hA

end AlgebraicGeometry.Etale
