/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-! # EtaleGeneratorsPullbackSourceComparison

Source: Stacks Project, Tags 0097 and 040E.
(blueprint: lem-sc-etale-generators-pullback-source-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- An explicit comparison factor in the generator pullback construction.
Source: Stacks Project, Tag 0097. (blueprint: lem-sc-etale-generators-pullback-source-comparison) -/
noncomputable def etaleGeneratorsPullbackSourceIso {X Y : Scheme.{u}} (f : Y ⟶ X) (W : X.Etale) :
    (pullback (Limits.pullback.snd W.hom f)).obj (unit Y) ≅
      (pullback (Limits.pullback.fst W.hom f)).obj ((pullback W.hom).obj (unit X)) :=
  pullbackObjUnitIso (Limits.pullback.snd W.hom f) ≪≫
    (pullbackObjUnitIso (Limits.pullback.fst W.hom f)).symm ≪≫
    (pullback (Limits.pullback.fst W.hom f)).mapIso (pullbackObjUnitIso W.hom).symm

/-- An explicit comparison factor in the generator pullback construction.
Source: Stacks Project, Tag 0097. (blueprint: lem-sc-etale-generators-pullback-source-comparison) -/
noncomputable def etaleGeneratorsPullbackSquareIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {V W : X.Etale} (i : V ⟶ W) (M : W.left.Modules) :
    (pullback ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).obj
      ((pullback (Limits.pullback.fst W.hom f)).obj M) ≅
      (pullback (Limits.pullback.fst V.hom f)).obj ((pullback i.left).obj M) :=
  let j := ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
  let hp : j ≫ Limits.pullback.fst W.hom f =
      Limits.pullback.fst V.hom f ≫ i.left := by
    simp [j, MorphismProperty.Over.pullback_map_left]
  (((pullbackComp j (Limits.pullback.fst W.hom f)) ≪≫ pullbackCongr hp) ≪≫
    (pullbackComp (Limits.pullback.fst V.hom f) i.left).symm).app M

private lemma unitComparison_app_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) (r : Γ(X, U)) :
    (pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U)
      (pullbackUnitApp f (unit X) U r) = f.app U r := by
  have h : (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackObjUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun φ ↦ φ.app U r) h

set_option backward.isDefEq.respectTransparency false in
private lemma unitComparison_comp {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) :
    (pullbackComp g f).inv.app (unit X) ≫
      (pullback g).map (pullbackObjUnitIso f).hom ≫ (pullbackObjUnitIso g).hom =
      (pullbackObjUnitIso (g ≫ f)).hom := by
  apply pullback_hom_ext (g ≫ f)
  intro U r
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullbackUnit_comp_app_apply]
  erw [pullbackUnit_naturality_apply g (pullbackObjUnitIso f).hom (f ⁻¹ᵁ U)]
  erw [unitComparison_app_unit f U, unitComparison_app_unit g (f ⁻¹ᵁ U),
    unitComparison_app_unit (g ≫ f) U]
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_app g f U) r).symm

private lemma unitComparison_compOfEq {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (h : Z ⟶ X) (w : g ≫ f = h) :
    (pullbackCompOfEq g f h w (unit X)).inv ≫
      (pullback g).map (pullbackObjUnitIso f).hom ≫ (pullbackObjUnitIso g).hom =
      (pullbackObjUnitIso h).hom := by
  subst h
  simpa [pullbackCompOfEq, pullbackCongr] using unitComparison_comp g f

private lemma unitComparison_compOfEq_hom {X Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (f : Y ⟶ X) (h : Z ⟶ X) (w : g ≫ f = h) :
    (pullbackCompOfEq g f h w (unit X)).hom ≫ (pullbackObjUnitIso h).hom =
      (pullback g).map (pullbackObjUnitIso f).hom ≫ (pullbackObjUnitIso g).hom := by
  apply (cancel_epi (pullbackCompOfEq g f h w (unit X)).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    (unitComparison_compOfEq g f h w).symm

private lemma unitComparison_square {A B C D : Scheme.{u}} (g : A ⟶ B) (p : B ⟶ D)
    (r : A ⟶ C) (t : C ⟶ D) (hp : g ≫ p = r ≫ t) :
    ((((pullbackComp g p) ≪≫ pullbackCongr hp) ≪≫ (pullbackComp r t).symm).hom.app
      (unit D)) ≫ (pullback r).map (pullbackObjUnitIso t).hom ≫
      (pullbackObjUnitIso r).hom =
      (pullback g).map (pullbackObjUnitIso p).hom ≫ (pullbackObjUnitIso g).hom := by
  change (pullbackCompOfEq g p (r ≫ t) hp (unit D)).hom ≫
    (pullbackComp r t).inv.app (unit D) ≫
      (pullback r).map (pullbackObjUnitIso t).hom ≫ (pullbackObjUnitIso r).hom = _
  rw [unitComparison_comp, unitComparison_compOfEq_hom]

/-- Naturality of the source factor for an arbitrary commuting diagram of schemes. -/
private lemma unitComparison_source {X Y A B C D : Scheme.{u}}
    (j : A ⟶ B) (pW : B ⟶ D) (pV : A ⟶ C) (i : C ⟶ D)
    (w : D ⟶ X) (v : C ⟶ X) (qW : B ⟶ Y) (qV : A ⟶ Y)
    (hp : j ≫ pW = pV ≫ i) (hq : j ≫ qW = qV) (hv : i ≫ w = v) :
    (pullbackCompOfEq j qW qV hq (unit Y)).inv ≫
      (pullback j).map ((pullbackObjUnitIso qW).hom ≫ (pullbackObjUnitIso pW).inv ≫
        (pullback pW).map (pullbackObjUnitIso w).inv) ≫
      ((((pullbackComp j pW) ≪≫ pullbackCongr hp) ≪≫ (pullbackComp pV i).symm).hom.app
        ((pullback w).obj (unit X))) =
      ((pullbackObjUnitIso qV).hom ≫ (pullbackObjUnitIso pV).inv ≫
        (pullback pV).map (pullbackObjUnitIso v).inv) ≫
      (pullback pV).map (pullbackCompOfEq i w v hv (unit X)).inv := by
  let k := ((pullbackComp j pW) ≪≫ pullbackCongr hp) ≪≫ (pullbackComp pV i).symm
  have hk : (pullback j).map ((pullback pW).map (pullbackObjUnitIso w).hom) ≫
      k.hom.app (unit D) = k.hom.app ((pullback w).obj (unit X)) ≫
        (pullback pV).map ((pullback i).map (pullbackObjUnitIso w).hom) :=
    k.hom.naturality (pullbackObjUnitIso w).hom
  change (pullbackCompOfEq j qW qV hq (unit Y)).inv ≫
    (pullback j).map ((pullbackObjUnitIso qW).hom ≫ (pullbackObjUnitIso pW).inv ≫
      (pullback pW).map (pullbackObjUnitIso w).inv) ≫
        k.hom.app ((pullback w).obj (unit X)) = _
  have hs := unitComparison_square j pW pV i hp
  rw [← cancel_mono ((pullback pV).map
    (pullbackCompOfEq i w v hv (unit X)).hom)]
  rw [← cancel_mono ((pullback pV).map (pullbackObjUnitIso v).hom)]
  rw [← cancel_mono (pullbackObjUnitIso pV).hom]
  simp only [Functor.map_comp, Category.assoc]
  conv_rhs =>
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((pullback pV).map
    (pullbackCompOfEq i w v hv (unit X)).hom)
      ((pullback pV).map (pullbackObjUnitIso v).hom)]
  rw [← Functor.map_comp]
  erw [unitComparison_compOfEq_hom i w v hv]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (k.hom.app ((pullback w).obj (unit X)))
    ((pullback pV).map ((pullback i).map (pullbackObjUnitIso w).hom))]
  rw [← hk]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]
  erw [hs]
  simp only [← Functor.map_comp_assoc, Category.assoc]
  erw [Iso.inv_hom_id, Category.comp_id]
  exact unitComparison_compOfEq j qW qV hq

/-- The source comparison commutes with etale restriction.
Source: Stacks Project, Tag 0097, Lemma 6.26.3; Tag 040E, Lemma 21.6.1.
(blueprint: lem-sc-etale-generators-pullback-source-comparison)

Proof: Under the pullback adjunction, the canonical unit comparison U(f) sends the image of a
section r to f.app(r). Use pullback_hom_ext, pullbackUnit_comp_app_apply, and naturality of the
adjunction unit to prove c(g,f).inv followed by g*U(f) and U(g) equals U(g followed by f).
Transport along an equality of composites and cancel to get the forward comparison formula.
Applying these formulas to the two paths of a commuting square proves that its comparison K
commutes with the unit comparisons. Expand the source factors. Postcompose by the pullback of
the forward comparison for i,W,V, then by the pulled-back U(V) and U(p_V); these are all
isomorphisms. The right side becomes U(q_V). On the left, use the composition law for i,W,V,
then naturality of K with respect to U(W), and cancel the pulled-back inverse of U(W). The
unit-square identity cancels U(p_W) and its inverse. The remaining expression is U(q_V) by the
composition law for j,q_W,q_V. The calculation is proved for arbitrary scheme morphisms and
then specialized to the etale square. No invertibility hypothesis on a coefficient module,
nonemptiness, or nonzero-ring hypothesis is used.
-/
theorem etaleGeneratorsPullbackSource_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {V W : X.Etale} (i : V ⟶ W) :
    (pullbackCompOfEq ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
      (Limits.pullback.snd W.hom f) (Limits.pullback.snd V.hom f)
      ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).w (unit Y)).inv ≫ (pullback
        ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left).map
        (etaleGeneratorsPullbackSourceIso f W).hom ≫
      (etaleGeneratorsPullbackSquareIso f i ((pullback W.hom).obj (unit X))).hom =
      (etaleGeneratorsPullbackSourceIso f V).hom ≫
        (pullback (Limits.pullback.fst V.hom f)).map (pullbackCompOfEq i.left W.hom V.hom i.w
          (unit X)).inv := by
  let j : Limits.pullback V.hom f ⟶ Limits.pullback W.hom f :=
    ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).left
  let pW := Limits.pullback.fst W.hom f
  let pV := Limits.pullback.fst V.hom f
  let qW := Limits.pullback.snd W.hom f
  let qV := Limits.pullback.snd V.hom f
  have hp : j ≫ pW = pV ≫ i.left := by
    simp [j, pW, pV, MorphismProperty.Over.pullback_map_left]
  exact unitComparison_source j pW pV i.left W.hom V.hom qW qV hp
    ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).w i.w

end AlgebraicGeometry.Scheme.Modules
