/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.FunctorialRingComplexSheaf
public import Sheaf.CategoryTheory.AugmentedComplexGluing
public import Sheaf.CategoryTheory.RingedDerivedRestriction
import Sheaf.Paper.RingFamilyLocallyEqualModels
import Sheaf.Paper.RingFamilyRestriction
import Sheaf.CategoryTheory.ModuleSheafificationLocalIso
import Sheaf.CategoryTheory.ModuleSheafificationRestriction

/-! # Descent from locally equal section ideals

Source: Stacks Project, algebraization.tex, Tag 099E, second and third paragraphs.
(blueprint: lem-weil-pbc-functorial-ring-complex-ideal-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

private instance overMap_additive
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U) :
    (SheafOfModules.overMap.{u} R a).Additive :=
  ⟨fun {_ _} b c ↦ by ext X x; rfl⟩

private abbrev commonSpanSections
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U W : C) (a : W ⟶ U)
    (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    Fin r → ((O.over W).obj ⋙ forget CommRingCat).sections :=
  ringFamilyRestrictedSections (J := J.over W) (L := J.over U)
    (Over.map a) (O.over U) r (fun i ↦ ringedSliceSection O U (f i))

private theorem restricted_ringFamily_model_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :
    ∃ e : (ringFamilySheafModel (O.over W) K ε m hm r
      (commonSpanSections O U W a r f)).1 ≅
      ((SheafOfModules.overMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i))).1,
      ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
        (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
          (commonSpanSections O U W a r f)).X n).obj X),
        (e.hom.f n).val.app X
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj
              (O.over W)).obj)).unit.app
                ((ringFamilyPresheafComplex (O.over W) K ε m hm r
                  (commonSpanSections O U W a r f)).X n)).app X x) =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj
              (O.over U)).obj)).unit.app
                ((ringFamilyPresheafComplex (O.over U) K ε m hm r
                  (fun i ↦ ringedSliceSection O U (f i))).X n)).app
                    ((Over.map a).op.obj X) x) := by
  exact exists_ringFamilySheafModel_restrictionIso
    (J := J.over W) (L := J.over U) (Over.map a) (O.over U) K ε m hm r
      (fun i ↦ ringedSliceSection O U (f i))

private abbrev sliceUnit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)) (n : ℤ) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)).obj)).unit.app
      ((ringFamilyPresheafComplex (O.over U) K ε m hm r
        (fun i ↦ ringedSliceSection O U (f i))).X n))

private abbrev sliceModelComplex
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U : C) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :=
  (ringFamilySheafModel (O.over U) K ε m hm r
    (fun i ↦ ringedSliceSection O U (f i))).1

private abbrev restrictedModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U)) :=
  ((SheafOfModules.overMap
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
      (.up ℤ)).obj (sliceModelComplex O K ε m hm U r f)

private abbrev commonSpanCanonical
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (q : restrictedModel O K ε m hm U W a r f ≅
      restrictedModel O K ε m hm V W b s g) : Prop :=
  ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
    (h : ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
      ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X)
    (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
      (commonSpanSections O U W a r f)).X n).obj X),
    (q.hom.f n).val.app X
      ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
      (sliceUnit O K ε m hm V s g n).app ((Over.map b).op.obj X)
        (ringFamilyComponentEquiv K ((O.over W).obj.obj X) _ _ h n x)

private theorem commonSpanEqualityCover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (heq : ∀ (T : C) (h : T ⟶ W), ∃ S ∈ J T,
      ∀ (Z : C) (k : Z ⟶ T), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ a).op (f t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ b).op (g t)))) :
    ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y) =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y) := by
  intro X
  obtain ⟨S, hS, hs⟩ := heq X.left X.hom
  refine ⟨(Sieve.overEquiv X).symm S, J.overEquiv_symm_mem_over X S hS, ?_⟩
  intro Y k hk
  apply Subtype.ext
  change Ideal.span (Set.range (fun t ↦ O.obj.map (Y.hom ≫ a).op (f t))) =
    Ideal.span (Set.range (fun t ↦ O.obj.map (Y.hom ≫ b).op (g t)))
  have hh := hs Y.left k.left hk
  simpa only [← Category.assoc, Over.w k] using hh

private theorem commonSpanModels_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (heq : ∀ (T : C) (h : T ⟶ W), ∃ S ∈ J T,
      ∀ (Z : C) (k : Z ⟶ T), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ a).op (f t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ b).op (g t)))) :
    ∃ q : ((SheafOfModules.overMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i))).1 ≅
      ((SheafOfModules.overMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) b).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over V) K ε m hm s
            (fun i ↦ ringedSliceSection O V (g i))).1,
      ∀ (n : ℤ) (X : (Over W)ᵒᵖ)
        (h : ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X)
        (x : ((ringFamilyPresheafComplex (O.over W) K ε m hm r
          (commonSpanSections O U W a r f)).X n).obj X),
        (q.hom.f n).val.app X
          ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
        (sliceUnit O K ε m hm V s g n).app ((Over.map b).op.obj X)
          (ringFamilyComponentEquiv K ((O.over W).obj.obj X) _ _ h n x) := by
  have hlocal : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        (ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y)).val =
          (ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y)).val := by
    intro X
    obtain ⟨S, hS, hs⟩ := heq X.left X.hom
    refine ⟨(Sieve.overEquiv X).symm S, J.overEquiv_symm_mem_over X S hS, ?_⟩
    intro Y k hk
    change Ideal.span (Set.range (fun t ↦ O.obj.map (Y.hom ≫ a).op (f t))) =
      Ideal.span (Set.range (fun t ↦ O.obj.map (Y.hom ≫ b).op (g t)))
    have hh := hs Y.left k.left hk
    simpa only [← Category.assoc, Over.w k] using hh
  obtain ⟨z, _, hz⟩ := ringFamilySheafModel_iso_of_locally_equal_ideals_with_unit
    (O.over W) K ε m hm r (commonSpanSections O U W a r f)
      s (commonSpanSections O V W b s g) hlocal
  obtain ⟨ea, ha⟩ := restricted_ringFamily_model_iso O K ε m hm U W a r f
  obtain ⟨eb, hb⟩ := restricted_ringFamily_model_iso O K ε m hm V W b s g
  refine ⟨ea.symm ≪≫ z ≪≫ eb, ?_⟩
  intro n X h x
  let η := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj (O.over W)).obj)).unit.app
      ((ringFamilyPresheafComplex (O.over W) K ε m hm r
        (commonSpanSections O U W a r f)).X n)).app X x
  have hc := congrArg (fun t ↦ (t.f n).val.app X η) ea.hom_inv_id
  change (ea.inv.f n).val.app X ((ea.hom.f n).val.app X η) = η at hc
  have ha' := (congrArg ((ea.inv.f n).val.app X) (ha n X x).symm).trans hc
  change (eb.hom.f n).val.app X
    ((z.hom.f n).val.app X ((ea.inv.f n).val.app X
      ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x))) = _
  exact (congrArg (fun t ↦ (eb.hom.f n).val.app X ((z.hom.f n).val.app X t)) ha').trans
    ((congrArg ((eb.hom.f n).val.app X) (hz n X h x)).trans
      (hb n X (ringFamilyComponentEquiv K ((O.over W).obj.obj X) _ _ h n x)))

private def spanEvaluationEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M : SheafOfModules.{u} (R.over U)) :
    ((SheafOfModules.overMap R a).obj M).val.obj (op (Over.mk (𝟙 W))) ≃ₗ[R.obj.obj (op W)]
      M.val.obj (op (Over.mk a)) :=
  let e : M.val.obj (op (Over.mk ((𝟙 W) ≫ a))) ≃ₗ[R.obj.obj (op W)]
      M.val.obj (op (Over.mk a)) :=
    (eqToIso (congrArg (fun b : W ⟶ U ↦
      (show ModuleCat (R.obj.obj (op W)) from M.val.obj (op (Over.mk b))))
        (Category.id_comp a))).toLinearEquiv
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := e.map_smul }

private theorem spanEvaluationEquiv_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U W : C} (a : W ⟶ U)
    (M N : SheafOfModules.{u} (R.over U)) (g : M ⟶ N)
    (x : ((SheafOfModules.overMap R a).obj M).val.obj (op (Over.mk (𝟙 W)))) :
    spanEvaluationEquiv R a N
        ((((SheafOfModules.overMap R a).map g).val.app (op (Over.mk (𝟙 W)))) x) =
      g.val.app (op (Over.mk a)) (spanEvaluationEquiv R a M x) := by
  have h := eqToHom_naturality
    (C := ModuleCat (R.obj.obj (op W)))
    (f := fun b : W ⟶ U ↦
      (show ModuleCat (R.obj.obj (op W)) from M.val.obj (op (Over.mk b))))
    (g := fun b : W ⟶ U ↦
      (show ModuleCat (R.obj.obj (op W)) from N.val.obj (op (Over.mk b))))
    (fun b : W ⟶ U ↦ (show M.val.obj (op (Over.mk b)) ⟶ N.val.obj (op (Over.mk b)) from
      g.val.app (op (Over.mk b)))) (Category.id_comp a)
  exact congrArg (fun z ↦ z x) h

private def spanTransitionEquiv
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((SheafOfModules.overMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((SheafOfModules.overMap R b).mapHomologicalComplex (.up ℤ)).obj N) (n : ℤ) :
    (M.X n).val.obj (op (Over.mk a)) ≃ₗ[R.obj.obj (op W)]
      (N.X n).val.obj (op (Over.mk b)) :=
  let e : ((SheafOfModules.overMap R a).obj (M.X n)).val.obj (op (Over.mk (𝟙 W))) ≃ₗ[
      R.obj.obj (op W)]
      ((SheafOfModules.overMap R b).obj (N.X n)).val.obj (op (Over.mk (𝟙 W))) :=
    ((SheafOfModules.evaluation (R.over W) (op (Over.mk (𝟙 W)))).mapIso
      (HomologicalComplex.Hom.isoApp q n)).toLinearEquiv
  (spanEvaluationEquiv R a (M.X n)).symm.trans
    (e.trans (spanEvaluationEquiv R b (N.X n)))

private theorem spanTransitionEquiv_differential
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (q : ((SheafOfModules.overMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((SheafOfModules.overMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (n k : ℤ) (x : (M.X n).val.obj (op (Over.mk a))) :
    spanTransitionEquiv R a b M N q k ((M.d n k).val.app (op (Over.mk a)) x) =
      (N.d n k).val.app (op (Over.mk b)) (spanTransitionEquiv R a b M N q n x) := by
  let y := (spanEvaluationEquiv R a (M.X n)).symm x
  have ha := spanEvaluationEquiv_naturality R a (M.X n) (M.X k) (M.d n k) y
  have hb := spanEvaluationEquiv_naturality R b (N.X n) (N.X k) (N.d n k)
    ((q.hom.f n).val.app (op (Over.mk (𝟙 W))) y)
  have hd := congrArg (fun z ↦ z.val.app (op (Over.mk (𝟙 W))) y) (q.hom.comm n k)
  have hi : (spanEvaluationEquiv R a (M.X k)).symm
      ((M.d n k).val.app (op (Over.mk a)) x) =
      (((SheafOfModules.overMap R a).map (M.d n k)).val.app (op (Over.mk (𝟙 W)))) y := by
    apply (spanEvaluationEquiv R a (M.X k)).injective
    simpa only [y, LinearEquiv.apply_symm_apply] using ha.symm
  change spanEvaluationEquiv R b (N.X k)
    ((q.hom.f k).val.app (op (Over.mk (𝟙 W)))
      ((spanEvaluationEquiv R a (M.X k)).symm
        ((M.d n k).val.app (op (Over.mk a)) x))) = _
  rw [hi]
  exact (congrArg (spanEvaluationEquiv R b (N.X k)) hd.symm).trans hb

private theorem spanTransitionEquiv_comp
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {U V T W : C}
    (a : W ⟶ U) (b : W ⟶ V) (c : W ⟶ T)
    (M : CochainComplex (SheafOfModules.{u} (R.over U)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (R.over V)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (R.over T)) ℤ)
    (q : ((SheafOfModules.overMap R a).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((SheafOfModules.overMap R b).mapHomologicalComplex (.up ℤ)).obj N)
    (z : ((SheafOfModules.overMap R b).mapHomologicalComplex (.up ℤ)).obj N ≅
      ((SheafOfModules.overMap R c).mapHomologicalComplex (.up ℤ)).obj P)
    (n : ℤ) (x : (M.X n).val.obj (op (Over.mk a))) :
    spanTransitionEquiv R a c M P (q ≪≫ z) n x =
      spanTransitionEquiv R b c N P z n (spanTransitionEquiv R a b M N q n x) := by
  simp only [spanTransitionEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rfl

private theorem commonSpanHom_ext
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U W : C) (a : W ⟶ U) (r : ℕ) (f : Fin r → O.obj.obj (op U))
    (E : (Over W)ᵒᵖ → Prop)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k → E (op Y))
    (B : ringedSiteComplex (O.over W))
    (τ χ : ((SheafOfModules.overMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a).mapHomologicalComplex
          (.up ℤ)).obj (ringFamilySheafModel (O.over U) K ε m hm r
            (fun i ↦ ringedSliceSection O U (f i))).1 ⟶ B)
    (h : ∀ (n : ℤ) (X : (Over W)ᵒᵖ), E X →
      ∀ x : ((ringFamilyPresheafComplex (O.over U) K ε m hm r
        (fun i ↦ ringedSliceSection O U (f i))).X n).obj ((Over.map a).op.obj X),
      (τ.f n).val.app X ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x) =
        (χ.f n).val.app X
          ((sliceUnit O K ε m hm U r f n).app ((Over.map a).op.obj X) x)) : τ = χ := by
  apply HomologicalComplex.hom_ext
  intro n
  exact PresheafOfModules.restricted_sheafification_hom_ext
    (J := J.over W) (K := J.over U) (Over.map a)
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))
        ((ringFamilyPresheafComplex (O.over U) K ε m hm r
          (fun i ↦ ringedSliceSection O U (f i))).X n)
        E hcover (B.X n) (τ.f n) (χ.f n) (h n)

private def sheafModelAugmentationZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ((ringFamilySheafModel O K ε m hm r f).1.X 0) ⟶
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
  (ringFamilySheafModel O K ε m hm r f).2.f 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom

private theorem sheafModelAugmentationZero_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (r : ℕ) (f : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (X : Cᵒᵖ) (x : ((ringFamilyPresheafComplex O K ε m hm r f).X 0).obj X) :
    (sheafModelAugmentationZero O K ε m hm r f).val.app X
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
          ((ringFamilyPresheafComplex O K ε m hm r f).X 0)).app X x) =
      ringComplexAugmentationValue (ε (O.obj.obj X) (ringFamilySectionIdeal O r f X)) x := by
  have h := ringFamilySheafModel_augmentation_unit O K ε m hm r f 0 X x
  have h' := congrArg
    (((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).hom).val.app X)
    h
  change _ = _ at h'
  simp only [ringFamilyPresheafAugmentation,
    HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
    Iso.app_inv, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    Category.assoc, Iso.inv_hom_id_assoc, ringFamilyPresheafAugmentationZero] at h'
  let y := ringComplexAugmentationValue
    (ε (O.obj.obj X) (ringFamilySectionIdeal O r f X)) x
  have hc := congrArg (fun z ↦ z.val.app X y)
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).inv_hom_id)
  exact h'.trans hc

private theorem commonSpanCanonical_augmentationZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V W : C) (a : W ⟶ U) (b : W ⟶ V)
    (r s : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (q : restrictedModel O K ε m hm U W a r f ≅ restrictedModel O K ε m hm V W b s g)
    (hq : commonSpanCanonical O K ε m hm U V W a b r s f g q)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y) =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y)) :
    let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
    (q.hom.f 0) ≫ (SheafOfModules.overMap R b).map
        (sheafModelAugmentationZero (O.over V) K ε m hm s
          (fun i ↦ ringedSliceSection O V (g i))) ≫
        (SheafOfModules.overMapUnitIso (R := R) b).hom =
      (SheafOfModules.overMap R a).map
        (sheafModelAugmentationZero (O.over U) K ε m hm r
          (fun i ↦ ringedSliceSection O U (f i))) ≫
        (SheafOfModules.overMapUnitIso (R := R) a).hom := by
  dsimp only
  apply PresheafOfModules.restricted_sheafification_hom_ext
    (J := J.over W) (K := J.over U) (Over.map a)
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))
      ((ringFamilyPresheafComplex (O.over U) K ε m hm r
        (fun i ↦ ringedSliceSection O U (f i))).X 0)
      (fun X ↦ ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
        ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X)
      hcover
  intro X hX x
  change (sheafModelAugmentationZero (O.over V) K ε m hm s
    (fun i ↦ ringedSliceSection O V (g i))).val.app ((Over.map b).op.obj X)
      ((q.hom.f 0).val.app X ((sliceUnit O K ε m hm U r f 0).app
        ((Over.map a).op.obj X) x)) = _
  rw [hq 0 X hX x]
  have hb := sheafModelAugmentationZero_unit (O.over V) K ε m hm s
    (fun i ↦ ringedSliceSection O V (g i)) ((Over.map b).op.obj X)
      (ringFamilyComponentEquiv K ((O.over W).obj.obj X) _ _ hX 0 x)
  have ha := sheafModelAugmentationZero_unit (O.over U) K ε m hm r
    (fun i ↦ ringedSliceSection O U (f i)) ((Over.map a).op.obj X) x
  rw [hb]
  have ht (A : CommRingCat.{u}) (I I' : {I : Ideal A // I.FG}) (h : I = I')
      (y : ((K A I).X 0).val.obj (op ⟨PUnit.unit⟩)) :
      ringComplexAugmentationValue (ε A I') (ringFamilyComponentEquiv K A I I' h 0 y) =
        ringComplexAugmentationValue (ε A I) y := by
    subst I'
    rfl
  exact (ht _ _ _ hX x).trans ha.symm

private theorem ringFamilyComponentEquiv_trans
    (K : RingComplexFamily.{u}) (A : CommRingCat.{u})
    (I L M : {I : Ideal A // I.FG}) (h : I = L) (k : L = M)
    (n : ℤ) (x : ((K A I).X n).val.obj (op ⟨PUnit.unit⟩)) :
    ringFamilyComponentEquiv K A I M (h.trans k) n x =
      ringFamilyComponentEquiv K A L M k n (ringFamilyComponentEquiv K A I L h n x) := by
  subst L
  subst M
  rfl

private theorem commonSpanCanonical_cocycle
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (U V T W : C) (a : W ⟶ U) (b : W ⟶ V) (c : W ⟶ T)
    (r s t : ℕ) (f : Fin r → O.obj.obj (op U)) (g : Fin s → O.obj.obj (op V))
    (h : Fin t → O.obj.obj (op T))
    (q : restrictedModel O K ε m hm U W a r f ≅ restrictedModel O K ε m hm V W b s g)
    (z : restrictedModel O K ε m hm V W b s g ≅ restrictedModel O K ε m hm T W c t h)
    (v : restrictedModel O K ε m hm U W a r f ≅ restrictedModel O K ε m hm T W c t h)
    (hq : commonSpanCanonical O K ε m hm U V W a b r s f g q)
    (hz : commonSpanCanonical O K ε m hm V T W b c s t g h z)
    (hv : commonSpanCanonical O K ε m hm U T W a c r t f h v)
    (hcover : ∀ X : Over W, ∃ S ∈ (J.over W) X,
      ∀ (Y : Over W) (k : Y ⟶ X), S k →
        (ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) (op Y) =
          ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y)) ∧
        (ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) (op Y) =
          ringFamilySectionIdeal (O.over W) t (commonSpanSections O T W c t h) (op Y))) :
    v.hom = q.hom ≫ z.hom := by
  apply commonSpanHom_ext O K ε m hm U W a r f
    (fun X ↦
      (ringFamilySectionIdeal (O.over W) r (commonSpanSections O U W a r f) X =
        ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X) ∧
      (ringFamilySectionIdeal (O.over W) s (commonSpanSections O V W b s g) X =
        ringFamilySectionIdeal (O.over W) t (commonSpanSections O T W c t h) X))
    hcover (restrictedModel O K ε m hm T W c t h)
  intro n X hx x
  change (v.hom.f n).val.app X _ =
    (z.hom.f n).val.app X ((q.hom.f n).val.app X _)
  rw [hv n X (hx.1.trans hx.2) x, hq n X hx.1 x, hz n X hx.2]
  exact congrArg ((sliceUnit O K ε m hm T t h n).app ((Over.map c).op.obj X))
    (ringFamilyComponentEquiv_trans K ((O.over W).obj.obj X) _ _ _ hx.1 hx.2 n x)

private theorem exists_commonSpanCoherentComparisons
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    {A : Type u} (U : A → C) (r : A → ℕ)
    (f : ∀ i : A, Fin (r i) → O.obj.obj (op (U i)))
    (heq : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      ∃ S ∈ J W, ∀ (V : C) (k : V ⟶ W), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ a).op (f i t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ b).op (f j t)))) :
    ∃ q : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      restrictedModel O K ε m hm (U i) W a (r i) (f i) ≅
        restrictedModel O K ε m hm (U j) W b (r j) (f j),
      (∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
        commonSpanCanonical O K ε m hm (U i) (U j) W a b (r i) (r j) (f i) (f j)
          (q i j W a b)) ∧
      (∀ (i j k : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j) (c : W ⟶ U k),
        (q i k W a c).hom = (q i j W a b).hom ≫ (q j k W b c).hom) := by
  classical
  have hlocal (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j) :
      ∀ (T : C) (h : T ⟶ W), ∃ S ∈ J T,
        ∀ (Z : C) (k : Z ⟶ T), S k →
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ a).op (f i t))) =
            Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ h ≫ b).op (f j t))) := by
    intro T h
    simpa only [Category.assoc] using heq i j T (h ≫ a) (h ≫ b)
  have hh := fun (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j) ↦
    commonSpanModels_iso O K ε m hm (U i) (U j) W a b (r i) (r j) (f i) (f j)
      (hlocal i j W a b)
  choose q hq using hh
  refine ⟨q, hq, ?_⟩
  intro i j k W a b c
  apply commonSpanCanonical_cocycle O K ε m hm (U i) (U j) (U k) W a b c
    (r i) (r j) (r k) (f i) (f j) (f k)
    (q i j W a b) (q j k W b c) (q i k W a c)
    (hq i j W a b) (hq j k W b c) (hq i k W a c)
  intro X
  obtain ⟨S, hS, hs⟩ := commonSpanEqualityCover O (U i) (U j) W a b
    (r i) (r j) (f i) (f j) (hlocal i j W a b) X
  obtain ⟨T, hT, ht⟩ := commonSpanEqualityCover O (U j) (U k) W b c
    (r j) (r k) (f j) (f k) (hlocal j k W b c) X
  exact ⟨S ⊓ T, (J.over W).intersection_covering hS hT,
    fun Y v hv ↦ ⟨hs Y v hv.1, ht Y v hv.2⟩⟩

/-- Locally equal section ideals give coherent strict descent data for the sheafified
ring-family complexes. This assertion has no ideal module, finite-type assumption,
covering-family assumption, derived category or Čech complex.
Source: Stacks Project, Tag 099E, the canonical identifications and their cocycle.
(blueprint: lem-weil-pbc-functorial-ring-complex-ideal-descent).

Proof: on a common test span, restrict both presheaf complexes to the slice of the test
object. The section ideals are equal on a restriction-stable locus which covers every
object, by the hypothesis applied to further test spans. On that locus identify the ring
complexes by transport along equality of their ideals. The construction
ringFamilySheafModel_iso_of_locally_equal_ideals_with_unit gives the augmented chain isomorphism.
Use exists_ringFamilySheafModel_restrictionIso to identify its source and target with
restrictions of the original slice models. Its formula on sheafification-unit sections
specifies the transition map uniquely: sheafification_hom_ext_on_locus applies on the
same covering locus. Further restriction preserves this formula, so uniqueness gives
naturality. On a triple common span intersect the three equality loci; transport along
equality is transitive there, so uniqueness gives the cocycle. The chain equation is
supplied by the chain comparisons. For augmentation, test on unit
sections: the comparison sends a section to its transport along equality of ideals, and
the ring-family augmentation commutes with that transport. The sheafification adjunction
identifies these presheaf augmentations with the specified sheaf augmentations. The same
hom-ext theorem therefore proves the augmentation equation. Evaluate the resulting chain
isomorphisms at the terminal test object to obtain the specified linear transitions.
Empty indexing families and empty generating lists use the same formulas. -/
theorem exists_ringFamily_idealDescentData
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    {A : Type u} (U : A → C) (r : A → ℕ)
    (f : ∀ i : A, Fin (r i) → O.obj.obj (op (U i)))
    (heq : ∀ (i j : A) (W : C) (a : W ⟶ U i) (b : W ⟶ U j),
      ∃ S ∈ J W, ∀ (V : C) (k : V ⟶ W), S k →
        Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ a).op (f i t))) =
          Ideal.span (Set.range (fun t ↦ O.obj.map (k ≫ b).op (f j t)))) :
    Nonempty (SheafOfModules.AugmentedComplexGlueData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U (ringedSiteRingComplex O)
      (fun i ↦ (ringFamilySheafModel (O.over (U i)) K ε m hm (r i)
        (fun t ↦ ringedSliceSection O (U i) (f i t))).1)
      (fun i ↦ (ringFamilySheafModel (O.over (U i)) K ε m hm (r i)
        (fun t ↦ ringedSliceSection O (U i) (f i t))).2 ≫
          (ringedRestrictionRingComplexIso O (U i)).inv)) := by
  sorry

end CategoryTheory
