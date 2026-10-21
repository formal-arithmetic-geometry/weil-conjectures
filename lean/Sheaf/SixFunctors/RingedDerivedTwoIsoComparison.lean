/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.SixFunctors.RingedDerivedComparisonData
import Sheaf.SixFunctors.RingedDerivedCompositionComparison
import Sheaf.SixFunctors.RingedDerivedIdentityComparison
import Sheaf.SixFunctors.RingedDerivedAdjointLift
import Sheaf.SixFunctors.RingedDerivedTensorLift
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Geometric 2-isomorphism normalization

Source: Stacks Project, Modules on Sites and Cohomology on Sites,
Tags 03D7, 03D8, 03EL, 07A4 and 07A6.
(blueprint: lem-sfb-ringed-derived-two-iso-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- Representative normalization with the right comparison fixed as the derived
adjunction mate. Hom-bijection compatibility follows formally from that choice.
Source: Stacks Project, Tags 03D7, 03D8 and 07A6.
(blueprint: lem-sfb-ringed-derived-two-iso-comparison). -/
structure TwoIsoCore {X Y : Site.{u, w}} {h k : Morphism X Y}
    (lh : Lift h) (lk : Lift k) (θ : h.inverse ≅ k.inverse) where
  ordinary : lh.edge.pullback ≅ lk.edge.pullback
  ordinary_insertion : ∀ M : Y.modules,
    lh.insertion M ≫ X.sets.map (ordinary.hom.app M) =
      θ.hom.app (Y.sets.obj M) ≫ lk.insertion M
  ordinary_right : lk.edge.pushforward ≅ lh.edge.pushforward
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv lk.edge.moduleAdjunction lh.edge.moduleAdjunction ordinary
  pullback : lh.edge.left ≅ lk.edge.left
  pullback_model : ∀ P : CochainComplex Y.modules ℤ, Y.corner.mateFlat P →
    pullback.hom.app (DerivedCategory.Q.obj P) ≫ lk.alpha P =
      lh.alpha P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)
  pushforward_model : ∀ I : CochainComplex X.modules ℤ,
    lk.eta.app I ≫ (conjugateIsoEquiv lk.edge.derivedAdjunction
      lh.edge.derivedAdjunction pullback).hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary_right.hom (ComplexShape.up ℤ)).app I) ≫
        lh.eta.app I
  tensor : ∀ U V : Y.D,
    pullback.hom.app (Y.closed.tensor.obj (U, V)) ≫ (lk.tensor U V).hom =
      (lh.tensor U V).hom ≫ X.closed.tensor.map
        (X := (lh.edge.left.obj U, lh.edge.left.obj V))
        (Y := (lk.edge.left.obj U, lk.edge.left.obj V))
        (pullback.hom.app U, pullback.hom.app V)
  unit : pullback.hom.app Y.closed.monoidal.tensorUnit ≫ lk.unit.hom = lh.unit.hom

private theorem geometric_identities (X : Site.{u, w}) :
    ∃ (f : Morphism X X) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
      f.ringMap = θ.hom.app ((sheafCompose X.J
        (CategoryTheory.forget CommRingCat.{u})).obj X.A) := by
  let f : Morphism X X := {
    inverse := 𝟭 _
    direct := 𝟭 _
    adj := Adjunction.id
    leftExact := inferInstance
    ringMap := 𝟙 _
    ring_zero := by intro T z hz U t; simpa using hz U t
    ring_one := by intro T z hz U t; simpa using hz U t
    ring_add := by intro T x y z hz U t; simpa using hz U t
    ring_mul := by intro T x y z hz U t; simpa using hz U t
    modules := 𝟭 _
    additive := inferInstance
    underlying := Iso.refl _
    module_linear := by
      intro M T a x y z hz U t
      simpa [Adjunction.homEquiv, Adjunction.id] using hz U t }
  exact ⟨f, Iso.refl _, rfl⟩

private theorem tensor_model (X : Site.{u, w}) :
    ∃ r : RingedTensorModel X.corner, ∀ P Q hP hQ,
      r.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom := by
  let ι : ObjectProperty.FullSubcategory X.corner.mateFlat ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
        (J := X.J) (R := X.A)) := {
    obj := fun P ↦ ⟨P.obj,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
    map := fun a ↦ ObjectProperty.homMk a.hom }
  let r : RingedTensorModel X.corner := {
    representative := Functor.isoWhiskerLeft (ι.prod ι) X.model.comparison }
  exact ⟨r, fun _ _ _ _ ↦ rfl⟩

private theorem normalizedLift_exists {X Y : Site.{u, w}} (f : Morphism X Y) :
    Nonempty (Lift f) := by
  obtain ⟨d⟩ := adjointLift_exists f
  obtain ⟨rY, hY⟩ := tensor_model Y
  obtain ⟨rX, hX⟩ := tensor_model X
  obtain ⟨t⟩ := tensorLift_exists d.edge rY rX hY hX
  exact ⟨{
    edge := d.edge
    inverse_eq := d.inverse_eq
    direct_eq := d.direct_eq
    geometric_adjunction := d.geometric_adjunction
    pushforward_eq := d.pushforward_eq
    structural_map := d.structural_map
    ordinary_adjunction := d.ordinary_adjunction
    right_additive := d.right_additive
    eta := d.eta
    isRightDerived := d.isRightDerived
    eta_injective := d.eta_injective
    epsilon_flat := d.epsilon_flat
    canonical_adjunction := d.canonical_adjunction
    tensorModelY := rY
    tensorModelX := rX
    tensorModelY_eq := hY
    tensorModelX_eq := hX
    monoidal := t.monoidal
    tensor_canonical := t.tensor_canonical
    unit_canonical := t.unit_canonical
    symmetric := t.symmetric }⟩

set_option backward.isDefEq.respectTransparency false in
private theorem edge_preserves_flat_kflat
    {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    (P : CochainComplex (A.mateModules) ℤ)
    (hp : P.IsAcyclicTensorKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) :
    CochainComplex.IsAcyclicTensorKFlat ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ n : ℤ, (((e.pullback.mapHomologicalComplex (.up ℤ)).obj P).X n).IsFlat := by
  have hf' (n : ℤ) : IsFlatOnSite (J := A.topology) (R := A.ring) (P.X n) := by
    let := monoidalCategory A.ring
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso A.ring (P.X n)).symm
      (hf n)
  obtain ⟨hk, ht⟩ := isKFlat_ringedToposPullback e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp) hf'
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro n
  let := monoidalCategory B.ring
  exact ObjectProperty.prop_of_iso (exactFunctor _ _)
    (siteSheafTensorRightIso B.ring _) (ht n)

private theorem conjugate_remove_identity
    {A B : Type*} [Category A] [Category B]
    {L H : A ⥤ B} {R S : B ⥤ A} {F G : B ⥤ B}
    (b : L ⊣ R) (q : H ⊣ S) (a : F ⊣ G)
    (c : H ≅ L ⋙ F) (d : F ≅ 𝟭 B) (I : B) :
    (conjugateEquiv q b
      (c ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L).inv).app I =
      (conjugateEquiv q (b.comp a) c.inv).app I ≫
        R.map ((conjugateEquiv a (Adjunction.id (C := B)) d.inv).app I) := by
  have hu : conjugateEquiv (b.comp (Adjunction.id (C := B))) b
      (Functor.rightUnitor L).inv = (Functor.leftUnitor R).hom := by
    apply (cancel_epi (Functor.leftUnitor R).inv).mp
    rw [← conjugateEquiv_rightUnitor_hom b, conjugateEquiv_comp]
    rw [conjugateEquiv_rightUnitor_hom]
    simp only [Iso.inv_hom_id, conjugateEquiv_id]
  have h := conjugateEquiv_comp q (b.comp a) (b.comp (Adjunction.id (C := B)))
    c.inv (Functor.whiskerLeft L d.inv)
  have h' := conjugateEquiv_comp q (b.comp (Adjunction.id (C := B))) b
    (Functor.whiskerLeft L d.inv ≫ c.inv) (Functor.rightUnitor L).inv
  rw [← h, conjugateEquiv_whiskerLeft, hu] at h'
  have he := (NatTrans.congr_app h' I).symm
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app] at he
  have hf := he.trans (Category.comp_id _)
  simpa only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Category.assoc] using hf

private theorem remove_identity_hom
    {A B : Type*} [Category A] [Category B]
    {L H : A ⥤ B} {F : B ⥤ B}
    (c : H ≅ L ⋙ F) (d : F ≅ 𝟭 B) (U : A) :
    (c ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L).hom.app U =
      c.hom.app U ≫ d.hom.app (L.obj U) := by
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

private theorem inverse_square
    {C : Type*} [Category C] {A B D E : C}
    (r : A ≅ B) (s : D ≅ E) (a : D ⟶ A) (b : E ⟶ B)
    (h : b ≫ r.inv = s.inv ≫ a) : a ≫ r.hom = s.hom ≫ b := by
  apply (cancel_mono r.inv).mp
  simp only [Category.assoc, r.hom_inv_id, Category.comp_id]
  rw [h, s.hom_inv_id_assoc]

set_option maxHeartbeats 800000 in
-- Comparing the recorded corner presentations in representative equations needs extra fuel.
/-- Geometric 2-isomorphism normalization for an already normalized lift.
Source: Stacks Project, Modules on Sites and Cohomology on Sites,
Tags 03D7, 03D8, 03EL, 07A4 and 07A6.
(blueprint: lem-sfb-ringed-derived-two-iso-comparison).

Proof:
1. Construct the identity ringed-topos morphism on X, obtain a normalized lift
from the adjoint and tensor lift declarations, and apply identity normalization.
Apply composition normalization to this identity lift and lk, with composite
lift lh and geometric path theta followed by the inverse identity comparison.
Naturality and the ring-map hypothesis verify the composition hypothesis.
2. Compose the ordinary and derived composition comparisons with the whiskered
identity comparisons and the right unitor. The insertion equation simplifies to
the specified theta. Pullback preserves flat-term K-flat complexes; naturality
and the two representative equations give the derived representative formula.
3. Adjunction conjugation respects composition, whiskering and the unitor. Hence
the inverse right mate factors into the composition right mate followed by the
identity right mate under k's right functor. The composition and identity eta
equations and naturality of k's eta give the formula on every complex. The same
factorization degreewise identifies the ordinary chain map. Cancel the two
isomorphisms to obtain the required forward right-mate formula.
4. Move the identity comparison through the tensorator and unit by naturality.
Substitute the identity and composition tensor and unit equations. Tensor
functoriality combines the comparison components. -/
theorem twoIsoComparison_exists {X Y : Site.{u, w}} {h k : Morphism X Y}
    (lh : Lift h) (lk : Lift k) (θ : h.inverse ≅ k.inverse)
    (hθ : h.ringMap = θ.hom.app
      ((sheafCompose Y.J (CategoryTheory.forget CommRingCat.{u})).obj Y.A) ≫ k.ringMap) :
    Nonempty (TwoIsoCore lh lk θ) := by
  obtain ⟨i, θi, hi⟩ := geometric_identities X
  obtain ⟨li⟩ := normalizedLift_exists i
  obtain ⟨ci⟩ := identityComparison_exists li θi hi
  let Θ : h.inverse ≅ k.inverse ⋙ i.inverse :=
    θ ≪≫ (Functor.rightUnitor k.inverse).symm ≪≫ Functor.isoWhiskerLeft k.inverse θi.symm
  have hΘ : h.ringMap = Θ.hom.app
      ((sheafCompose Y.J (CategoryTheory.forget CommRingCat.{u})).obj Y.A) ≫
      i.inverse.map k.ringMap ≫ i.ringMap := by
    rw [hi, hθ]
    simp only [Θ, Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Iso.symm_hom, Functor.rightUnitor_inv_app,
      Category.id_comp, Category.assoc]
    erw [θi.hom.naturality, Iso.inv_hom_id_app_assoc]
    rfl
  obtain ⟨cc⟩ := compositionCore_exists li lk lh Θ hΘ
  let o : lh.edge.pullback ≅ lk.edge.pullback := cc.ordinary ≪≫
    Functor.isoWhiskerLeft lk.edge.pullback ci.ordinary ≪≫
      Functor.rightUnitor lk.edge.pullback
  let p : lh.edge.left ≅ lk.edge.left := cc.pullback ≪≫
    Functor.isoWhiskerLeft lk.edge.left ci.pullback ≪≫
      Functor.rightUnitor lk.edge.left
  have hp (U : Y.D) : p.hom.app U =
      cc.pullback.hom.app U ≫ ci.pullback.hom.app (lk.edge.left.obj U) :=
    remove_identity_hom cc.pullback ci.pullback U
  refine ⟨{
    ordinary := o
    ordinary_insertion := ?_
    ordinary_right := conjugateIsoEquiv lk.edge.moduleAdjunction lh.edge.moduleAdjunction o
    ordinary_mate := rfl
    pullback := p
    pullback_model := ?_
    pushforward_model := ?_
    tensor := ?_
    unit := ?_ }⟩
  · intro M
    change lh.insertion M ≫ X.sets.map
      (cc.ordinary.hom.app M ≫ ci.ordinary.hom.app (lk.edge.pullback.obj M)) = _
    rw [X.sets.map_comp]
    rw [← Category.assoc, cc.ordinary_insertion]
    rw [Category.assoc, Category.assoc, ci.ordinary_insertion]
    simp only [Θ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Iso.symm_hom, Functor.rightUnitor_inv_app,
      Category.id_comp, Category.assoc]
    erw [θi.hom.naturality, Iso.inv_hom_id_app_assoc]
    rfl
  · intro P hP
    dsimp only [Site.corner] at *
    obtain ⟨hk, hf⟩ := edge_preserves_flat_kflat lk.edge P hP.1 hP.2
    obtain ⟨a, ha, he⟩ := ci.pullback_model
      ((lk.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) ⟨hk, hf⟩
    have hn := ci.pullback.hom.naturality (lk.alpha P)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hp]
    rw [Category.assoc, ← hn, he]
    have hc := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map a)
      (cc.pullback_model P hP)
    simp only [Category.assoc] at hc
    rw [hc]
    simp only [← DerivedCategory.Q.map_comp]
    congr 1
    apply congrArg DerivedCategory.Q.map
    ext n : 1
    simp only [HomologicalComplex.comp_f, ha, NatTrans.mapHomologicalComplex_app_f]
    exact (remove_identity_hom cc.ordinary ci.ordinary (P.X n)).symm
  · intro I
    dsimp only [Site.corner] at *
    let r := conjugateIsoEquiv lk.edge.derivedAdjunction lh.edge.derivedAdjunction p
    let s := conjugateIsoEquiv lk.edge.moduleAdjunction lh.edge.moduleAdjunction o
    let sc := NatIso.mapHomologicalComplex s (ComplexShape.up ℤ)
    obtain ⟨a, ha, he⟩ := ci.pushforward_model I
    have hri : r.inv.app (DerivedCategory.Q.obj I) =
        (conjugateIsoEquiv lh.edge.derivedAdjunction
          (lk.edge.derivedAdjunction.comp li.edge.derivedAdjunction)
          cc.pullback.symm).hom.app (DerivedCategory.Q.obj I) ≫
        lk.edge.right.map ((conjugateIsoEquiv li.edge.derivedAdjunction
          (Adjunction.id (C := X.D)) ci.pullback.symm).hom.app
          (DerivedCategory.Q.obj I)) :=
      conjugate_remove_identity lk.edge.derivedAdjunction lh.edge.derivedAdjunction
        li.edge.derivedAdjunction cc.pullback ci.pullback (DerivedCategory.Q.obj I)
    have hsc : sc.inv.app I =
        (NatTrans.mapHomologicalComplex cc.ordinary_right.hom (.up ℤ)).app I ≫
          (lk.edge.pushforward.mapHomologicalComplex (.up ℤ)).map a := by
      ext n : 1
      change s.inv.app (I.X n) = cc.ordinary_right.hom.app (I.X n) ≫
        lk.edge.pushforward.map (a.f n)
      rw [ha, cc.ordinary_mate, ci.ordinary_mate]
      exact conjugate_remove_identity lk.edge.moduleAdjunction lh.edge.moduleAdjunction
        li.edge.moduleAdjunction cc.ordinary ci.ordinary (I.X n)
    have hforward : lh.eta.app I ≫ r.inv.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map (sc.inv.app I) ≫ lk.eta.app I := by
      rw [hri, ← Category.assoc, cc.kappa_model]
      simp only [Category.assoc]
      rw [← lk.edge.right.map_comp, he]
      have hn := lk.eta.naturality a
      dsimp only [Functor.comp_map] at hn
      rw [← hn]
      simp only [← Category.assoc, ← DerivedCategory.Q.map_comp, hsc]
    change lk.eta.app I ≫ r.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map (sc.hom.app I) ≫ lh.eta.app I
    exact inverse_square (r.app (DerivedCategory.Q.obj I))
      (DerivedCategory.Q.mapIso (sc.app I)) (lk.eta.app I) (lh.eta.app I) hforward
  · intro U V
    dsimp only [Site.corner] at *
    have hn := ci.pullback.hom.naturality (lk.tensor U V).hom
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    change li.edge.left.map (lk.tensor U V).hom ≫
      ci.pullback.hom.app (X.closed.tensor.obj (lk.edge.left.obj U, lk.edge.left.obj V)) =
      ci.pullback.hom.app (lk.edge.left.obj (Y.closed.tensor.obj (U, V))) ≫
        (lk.tensor U V).hom at hn
    rw [hp, hp, hp]
    rw [Category.assoc, ← hn, ← ci.tensor]
    have hc := congrArg (fun f :
        lh.edge.left.obj (Y.closed.tensor.obj (U, V)) ⟶
          X.closed.tensor.obj (li.edge.left.obj (lk.edge.left.obj U),
            li.edge.left.obj (lk.edge.left.obj V)) ↦
      f ≫ X.closed.tensor.map
        (X := (li.edge.left.obj (lk.edge.left.obj U), li.edge.left.obj (lk.edge.left.obj V)))
        (Y := (lk.edge.left.obj U, lk.edge.left.obj V))
        (ci.pullback.hom.app (lk.edge.left.obj U),
          ci.pullback.hom.app (lk.edge.left.obj V))) (cc.tensor U V)
    simp only [Category.assoc] at hc
    rw [hc]
    simp only [← X.closed.tensor.map_comp]
    congr 1
  · have hn := ci.pullback.hom.naturality lk.unit.hom
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hp]
    rw [Category.assoc, ← hn, ← ci.unit]
    exact cc.unit

end CategoryTheory.RingedDerivedComparisons
