/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntersectionSectionsFlatBaseChange
public import WeilConjectures.AlgebraicGeometry.RingedSubspace
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import WeilConjectures.AlgebraicGeometry.AffineFlatDescent

/-!
# Affine descent from an invariant intersection

Source: Stacks Project, More on Groupoids, Tag 0APK, section-ring comparisons,
omitted cocycle check and affine model; Descent, Tag 0245.
(blueprint: lem-a1-invariant-intersection-affine-descent)
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
namespace Scheme

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionSheafMap_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    {I : Type v} {J : Type v} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
      (intersectionInclusion Y U)).unit.app Y.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat (intersectionInclusion Y U)).map
        (intersectionSheafMap g U V h) =
      ⟨g.c ≫ Functor.whiskerLeft (TopologicalSpace.Opens.map g.base).op
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
          (intersectionInclusion X V)).unit.app X.sheaf).hom⟩ := by
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion Y U)).homEquiv _ _ |>.apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionSheafMap_comp {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (k : Y ⟶ Z) {I J K : Type v}
    (U : I → Z.Opens) (V : J → Y.Opens) (W : K → X.Opens)
    (hk : ∀ y : Y, (∀ j, y ∈ V j) → ∀ i, k y ∈ U i)
    (hg : ∀ x : X, (∀ j, x ∈ W j) → ∀ i, g x ∈ V i) :
    intersectionSheafMap (g ≫ k) U W (fun x hx ↦ hk (g x) (hg x hx)) =
      intersectionSheafMap k U V hk ≫
        (TopCat.Sheaf.pushforward CommRingCat (intersectionSubsetMap k U V hk)).map
          (intersectionSheafMap g V W hg) := by
  apply (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion Z U)).homEquiv _ _ |>.injective
  change _ = ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion Z U)).unit.app Z.sheaf) ≫ _
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, intersectionSheafMap_unit]
  rw [Adjunction.homEquiv_unit, intersectionSheafMap_unit]
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext B
  have ht := congrArg (fun t ↦ t.hom.app
    (op ((TopologicalSpace.Opens.map k.base).obj B.unop)))
      (intersectionSheafMap_unit g V W hg)
  change (k.c.app B ≫ g.c.app _) ≫ _ = (k.c.app B ≫ _) ≫ _
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun t ↦ k.c.app B ≫ t) ht.symm

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionSheafMap_id (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) :
    intersectionSheafMap (𝟙 X) U U (fun _ hx ↦ hx) = 𝟙 _ := by
  apply (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
    (intersectionInclusion X U)).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, intersectionSheafMap_unit, Adjunction.homEquiv_unit]
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext B
  change (𝟙 _ ≫ _) = _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionSectionsMap_comp {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (k : Y ⟶ Z) {I J K : Type v}
    (U : I → Z.Opens) (V : J → Y.Opens) (W : K → X.Opens)
    (hk : ∀ y : Y, (∀ j, y ∈ V j) → ∀ i, k y ∈ U i)
    (hg : ∀ x : X, (∀ j, x ∈ W j) → ∀ i, g x ∈ V i) :
    intersectionSectionsMap (g ≫ k) U W (fun x hx ↦ hk (g x) (hg x hx)) =
      intersectionSectionsMap k U V hk ≫ intersectionSectionsMap g V W hg := by
  unfold intersectionSectionsMap
  rw [intersectionSheafMap_comp]
  change ((intersectionSheafMap k U V hk).hom.app (op ⊤) ≫
    (intersectionSheafMap g V W hg).hom.app _) ≫ _ = _
  rw [Category.assoc, Category.assoc]
  congr 1
  have hn := (intersectionSheafMap g V W hg).hom.naturality
    (homOfLE (show (⊤ : TopologicalSpace.Opens
      (TopCat.of {y : Y // ∀ j, y ∈ V j})) ≤
      (TopologicalSpace.Opens.map (intersectionSubsetMap k U V hk)).obj ⊤
      from fun _ _ ↦ trivial)).op
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  change (X.intersectionStructureSheaf W).obj.map _ =
    (X.intersectionStructureSheaf W).obj.map _ ≫ (X.intersectionStructureSheaf W).obj.map _
  rw [← CategoryTheory.Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionSectionsMap_id (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) :
    intersectionSectionsMap (𝟙 X) U U (fun _ hx ↦ hx) = 𝟙 _ := by
  unfold intersectionSectionsMap
  rw [intersectionSheafMap_id]
  change 𝟙 _ ≫ (intersectionStructureSheaf X U).obj.map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private lemma intersectionSectionsMap_congr {X Y : Scheme.{u}} {g k : X ⟶ Y}
    (e : g = k) {I J : Type v} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i)
    (h' : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, k x ∈ U i) :
    intersectionSectionsMap g U V h = intersectionSectionsMap k U V h' := by
  subst k
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionSectionsMap_isIso {X Y : Scheme.{u}} (e : X ≅ Y)
    {I J : Type v} (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) ↔ ∀ i, e.hom x ∈ U i) :
    IsIso (intersectionSectionsMap e.hom U V (fun x hx ↦ (h x).mp hx)) := by
  let h' : ∀ y : Y, (∀ i, y ∈ U i) → ∀ j, e.inv y ∈ V j := fun y hy ↦ by
    apply (h (e.inv y)).mpr
    simpa only [← Hom.comp_apply, e.inv_hom_id, Hom.id_base, TopCat.id_app] using hy
  refine ⟨⟨intersectionSectionsMap e.inv V U h', ?_, ?_⟩⟩
  · rw [← intersectionSectionsMap_comp]
    simp only [e.inv_hom_id]
    exact intersectionSectionsMap_id Y U
  · rw [← intersectionSectionsMap_comp]
    simp only [e.hom_inv_id]
    exact intersectionSectionsMap_id X V

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionTensorMap_pure {R T : CommRingCat.{u}} (r : R ⟶ T)
    {X Y : Scheme.{u}} (f : Y ⟶ Spec R) (q : X ⟶ Spec T) (g : X ⟶ Y)
    (comm : g ≫ f = q ≫ Spec.map r) {I J : Type v}
    (U : I → Y.Opens) (V : J → X.Opens)
    (h : ∀ x : X, (∀ j, x ∈ V j) → ∀ i, g x ∈ U i)
    (c : intersectionAlgebraSections f U) (t : T) :
    intersectionTensorMap r f q g comm U V h
        (intersectionScalarTensorPure r (intersectionAlgebraSections f U) c t) =
      intersectionSectionsMap g U V h c * intersectionScalars q V t := by
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionBaseChangeMap_left {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    letI := r.hom.toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R)
      (A := intersectionAlgebraSections f U) (B := T)) ≫
      CommRingCat.ofHom (intersectionBaseChangeMap r f U).hom.toRingHom =
        intersectionSectionsMap (pullback.fst f (Spec.map r)) U
          (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) (fun _ hx ↦ hx) := by
  let := r.hom.toAlgebra
  ext c
  change intersectionBaseChangeMap r f U
    (intersectionScalarTensorPure r (intersectionAlgebraSections f U) c 1) = _
  change intersectionTensorMap r f _ _ _ U _ _
    (intersectionScalarTensorPure r (intersectionAlgebraSections f U) c 1) = _
  rw [intersectionTensorMap_pure, map_one, mul_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionBaseChangeMap_right {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    letI := r.hom.toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)
      (A := intersectionAlgebraSections f U) (B := T)).toRingHom ≫
      CommRingCat.ofHom (intersectionBaseChangeMap r f U).hom.toRingHom =
        intersectionScalars (pullback.snd f (Spec.map r))
          (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) := by
  let := r.hom.toAlgebra
  ext t
  change intersectionBaseChangeMap r f U
    (intersectionScalarTensorPure r (intersectionAlgebraSections f U) 1 t) = _
  change intersectionTensorMap r f _ _ _ U _ _
    (intersectionScalarTensorPure r (intersectionAlgebraSections f U) 1 t) = _
  rw [intersectionTensorMap_pure, map_one, one_mul]
  rfl

private def intersectionAffineComparison {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    Spec (intersectionSections (pullback f (Spec.map r))
      (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)) ⟶
      pullback (Spec.map (intersectionScalars f U)) (Spec.map r) :=
  letI := r.hom.toAlgebra
  Spec.map (CommRingCat.ofHom (intersectionBaseChangeMap r f U).hom.toRingHom) ≫
    (pullbackSpecIso R (intersectionAlgebraSections f U) T).inv

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionAffineComparison_fst {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    intersectionAffineComparison r f U ≫ pullback.fst _ _ =
      Spec.map (intersectionSectionsMap (pullback.fst f (Spec.map r)) U
        (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) (fun _ hx ↦ hx)) := by
  let := r.hom.toAlgebra
  erw [intersectionAffineComparison, Category.assoc, pullbackSpecIso_inv_fst,
    ← Spec.map_comp, intersectionBaseChangeMap_left]

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionAffineComparison_snd {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    intersectionAffineComparison r f U ≫ pullback.snd _ _ =
      Spec.map (intersectionScalars (pullback.snd f (Spec.map r))
        (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)) := by
  let := r.hom.toAlgebra
  erw [intersectionAffineComparison, Category.assoc, pullbackSpecIso_inv_snd,
    ← Spec.map_comp, intersectionBaseChangeMap_right]

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionAffineComparison_isIso {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) [QuasiSeparatedSpace Y] [Flat (Spec.map r)]
    {I : Type v} (U : I → Y.Opens) (hI : Nonempty I)
    (hqc : ∀ i, IsCompact (U i : Set Y)) :
    IsIso (intersectionAffineComparison r f U) := by
  let β := CommRingCat.ofHom (intersectionBaseChangeMap r f U).hom.toRingHom
  have hb := (flat_affine_intersection_sections_base_change.{u, v, v} r f U hI hqc).1
  have : IsIso β := by
    exact ⟨⟨(RingEquiv.ofBijective β.hom hb).toCommRingCatIso.inv,
      (RingEquiv.ofBijective β.hom hb).toCommRingCatIso.hom_inv_id,
      (RingEquiv.ofBijective β.hom hb).toCommRingCatIso.inv_hom_id⟩⟩
  unfold intersectionAffineComparison
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma Spec_sectionsMap_comp {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (k : Y ⟶ Z) {I J K : Type v}
    (U : I → Z.Opens) (V : J → Y.Opens) (W : K → X.Opens)
    (hk : ∀ y : Y, (∀ j, y ∈ V j) → ∀ i, k y ∈ U i)
    (hg : ∀ x : X, (∀ j, x ∈ W j) → ∀ i, g x ∈ V i) :
    Spec.map (intersectionSectionsMap g V W hg) ≫
      Spec.map (intersectionSectionsMap k U V hk) =
        Spec.map (intersectionSectionsMap (g ≫ k) U W (fun x hx ↦ hk (g x) (hg x hx))) := by
  rw [← Spec.map_comp, intersectionSectionsMap_comp]

set_option backward.isDefEq.respectTransparency false in
private def intersectionAffineComparisonTo {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens)
    {Z : Scheme.{u}} (z : Z ⟶ Spec R) (e : Spec (intersectionSections Y U) ≅ Z)
    (he : e.hom ≫ z = Spec.map (intersectionScalars f U)) :
    Spec (intersectionSections (pullback f (Spec.map r))
      (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)) ⟶ pullback z (Spec.map r) :=
  intersectionAffineComparison r f U ≫
    pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _) (by simpa using he.symm) (by simp)

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionAffineComparisonTo_fst {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens)
    {Z : Scheme.{u}} (z : Z ⟶ Spec R) (e : Spec (intersectionSections Y U) ≅ Z)
    (he : e.hom ≫ z = Spec.map (intersectionScalars f U)) :
    intersectionAffineComparisonTo r f U z e he ≫ pullback.fst _ _ =
      Spec.map (intersectionSectionsMap (pullback.fst f (Spec.map r)) U
        (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i) (fun _ hx ↦ hx)) ≫ e.hom := by
  rw [intersectionAffineComparisonTo, Category.assoc, pullback.lift_fst,
    ← Category.assoc, intersectionAffineComparison_fst]

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionAffineComparisonTo_snd {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens)
    {Z : Scheme.{u}} (z : Z ⟶ Spec R) (e : Spec (intersectionSections Y U) ≅ Z)
    (he : e.hom ≫ z = Spec.map (intersectionScalars f U)) :
    intersectionAffineComparisonTo r f U z e he ≫ pullback.snd _ _ =
      Spec.map (intersectionScalars (pullback.snd f (Spec.map r))
        (fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i)) := by
  rw [intersectionAffineComparisonTo, Category.assoc, pullback.lift_snd,
    Category.comp_id, intersectionAffineComparison_snd]

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionAffineComparisonTo_isIso {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) [QuasiSeparatedSpace Y] [Flat (Spec.map r)]
    {I : Type v} (U : I → Y.Opens) (hI : Nonempty I)
    (hqc : ∀ i, IsCompact (U i : Set Y))
    {Z : Scheme.{u}} (z : Z ⟶ Spec R) (e : Spec (intersectionSections Y U) ≅ Z)
    (he : e.hom ≫ z = Spec.map (intersectionScalars f U)) :
    IsIso (intersectionAffineComparisonTo r f U z e he) := by
  have : IsIso (intersectionAffineComparison r f U) :=
    intersectionAffineComparison_isIso r f U hI hqc
  unfold intersectionAffineComparisonTo
  have : IsIso (pullback.map (Spec.map (intersectionScalars f U)) (Spec.map r)
      z (Spec.map r) e.hom (𝟙 _) (𝟙 _) (by simpa using he.symm) (by simp)) :=
    pullback.map_isIso _ _ _ _ _ _ _ _ _
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private def descentDatumOfAction {X S : Scheme.{u}} (p : X ⟶ S) (W : Over X)
    (k : pullback (W.hom ≫ p) p ⟶ W.left)
    (hk : k ≫ W.hom = pullback.snd _ _)
    (hself : pullback.lift (𝟙 W.left) W.hom (by simp) ≫ k = 𝟙 W.left)
    (hcocycle : ∀ (T : Scheme.{u}) (a : T ⟶ pullback (W.hom ≫ p) p)
      (b : T ⟶ X) (h : a ≫ pullback.snd _ _ ≫ p = b ≫ p),
      pullback.lift (a ≫ k) b (by
              rw [Category.assoc, reassoc_of% hk]
              exact h) ≫ k =
        pullback.lift (a ≫ pullback.fst _ _) b
          (by simpa only [Category.assoc, pullback.condition] using h) ≫ k) :
    Over.DescentDatum p W where
  transport f₁ f₂ h a := Over.homMk
    (pullback.lift a.left f₂ (by rw [← Category.assoc, Over.w a]; exact h) ≫ k)
    (by rw [Category.assoc, hk, pullback.lift_snd]; rfl)
  transport_homMk_comp g f₁ f₂ h a := by
    apply Over.OverMorphism.ext
    change pullback.lift (g ≫ a.left) (g ≫ f₂) _ ≫ k =
      g ≫ pullback.lift a.left f₂ _ ≫ k
    apply (congrArg (fun z ↦ z ≫ k) ?_).trans (Category.assoc _ _ _)
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    · simp only [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  transport_self f a := by
    apply Over.OverMorphism.ext
    change pullback.lift a.left f _ ≫ k = a.left
    have he : (pullback.lift a.left f
        (by rw [← Category.assoc, Over.w a]; rfl) : _ ⟶ pullback (W.hom ≫ p) p) =
        a.left ≫ pullback.lift (𝟙 W.left) W.hom (by simp) := by
      apply pullback.hom_ext
      · simp only [pullback.lift_fst, Category.assoc, pullback.lift_fst,
          Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
        exact (Over.w a).symm
    rw [he, Category.assoc, hself, Category.comp_id]
  transport_transport f₁ f₂ f₃ h₁₂ h₂₃ a := by
    apply Over.OverMorphism.ext
    change pullback.lift
      (pullback.lift a.left f₂ _ ≫ k) f₃ _ ≫ k = pullback.lift a.left f₃ _ ≫ k
    have hh := hcocycle _ (pullback.lift a.left f₂
      (by rw [← Category.assoc, Over.w a]; exact h₁₂)) f₃
      (by rw [pullback.lift_snd_assoc]; exact h₂₃)
    simpa only [pullback.lift_fst] using hh

/-- The overlap map of a transport datum, with V in the first and then second position.
Source: Stacks, Tags 023V and 0APK
(blueprint: lem-a1-invariant-intersection-affine-descent). -/
def invariantIntersectionOverlap {R A : CommRingCat.{u}} (r : R ⟶ A)
    (V : Over (Spec A)) (D : Over.DescentDatum (Spec.map r) V) :
    pullback (V.hom ≫ Spec.map r) (Spec.map r) ⟶
      pullback (Spec.map r) (V.hom ≫ Spec.map r) :=
  pullback.lift (pullback.fst _ _ ≫ V.hom) D.toHom (by
    have h := Over.w (D.transport
      (pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ≫ V.hom)
      (pullback.snd (V.hom ≫ Spec.map r) (Spec.map r))
      (by rw [Category.assoc, pullback.condition]) Over.DescentDatum.universalPoint)
    change D.toHom ≫ V.hom = pullback.snd _ _ at h
    rw [← Category.assoc, h, Category.assoc, pullback.condition])

set_option backward.isDefEq.respectTransparency false in
private lemma toHom_over {X S : Scheme.{u}} {p : X ⟶ S} {V : Over X}
    (D : Over.DescentDatum p V) : D.toHom ≫ V.hom = pullback.snd _ _ :=
  Over.w _

set_option backward.isDefEq.respectTransparency false in
private lemma toHom_naturality {X S : Scheme.{u}} {p : X ⟶ S} {V : Over X}
    (D : Over.DescentDatum p V) {T : Scheme.{u}}
    (g : T ⟶ pullback (V.hom ≫ p) p) (f₁ f₂ : T ⟶ X)
    (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V)
    (h₁ : g ≫ pullback.fst _ _ = a.left) (h₂ : g ≫ pullback.snd _ _ = f₂) :
    g ≫ D.toHom = (D.transport f₁ f₂ h a).left := by
  rw [D.transport_left_eq_lift_toHom]
  congr 1
  apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, h₁, h₂]

set_option backward.isDefEq.respectTransparency false in
private lemma invariantIntersectionOverlap_isIso {R A : CommRingCat.{u}} (r : R ⟶ A)
    (V : Over (Spec A)) (D : Over.DescentDatum (Spec.map r) V) :
    IsIso (invariantIntersectionOverlap r V D) := by
  let s := pullback.fst (V.hom ≫ Spec.map r) (Spec.map r)
  let q := pullback.snd (V.hom ≫ Spec.map r) (Spec.map r)
  let t := D.toHom
  have ht : t ≫ V.hom = q := toHom_over D
  have hp : (s ≫ V.hom) ≫ Spec.map r = q ≫ Spec.map r := by
    rw [Category.assoc]
    exact pullback.condition
  let i := pullback.lift t (s ≫ V.hom) (by
    rw [← Category.assoc, ht]
    exact hp.symm)
  have his : i ≫ s = t := pullback.lift_fst _ _ _
  have hiq : i ≫ q = s ≫ V.hom := pullback.lift_snd _ _ _
  have hit : i ≫ t = s := by
    have hh := toHom_naturality D i q (s ≫ V.hom) hp.symm (Over.homMk t ht) his hiq
    rw [hh]
    change (D.transport q (s ≫ V.hom) hp.symm
      (D.transport (s ≫ V.hom) q hp Over.DescentDatum.universalPoint)).left = s
    rw [D.transport_transport, D.transport_self]
    rfl
  have hii : i ≫ i = 𝟙 _ := by
    apply pullback.hom_ext
    · change (i ≫ i) ≫ s = 𝟙 _ ≫ s
      rw [Category.assoc, his, hit, Category.id_comp]
    · rw [Category.assoc, hiq, ← Category.assoc, his, ht, Category.id_comp]
  have : IsIso i := ⟨⟨i, hii, hii⟩⟩
  have he : invariantIntersectionOverlap r V D =
      i ≫ (pullbackSymmetry (V.hom ≫ Spec.map r) (Spec.map r)).hom := by
    apply pullback.hom_ext <;>
      simp only [invariantIntersectionOverlap, pullback.lift_fst, pullback.lift_snd,
        Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
        ]
    · exact hiq.symm
    · exact his.symm
  rw [he]
  infer_instance

/-- The right-position section algebra A tensor C, retaining the actual section ring C.
Source: Stacks, Tag 0APK (blueprint: lem-a1-invariant-intersection-affine-descent). -/
def intersectionLeftTensor {R A : CommRingCat.{u}} (r : R ⟶ A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    CommRingCat.{u} :=
  letI := r.hom.toAlgebra
  CommRingCat.of (A ⊗[R] intersectionAlgebraSections f U)

/-- Pure tensors in A tensor C. Source: Stacks, Tag 0APK
(blueprint: lem-a1-invariant-intersection-affine-descent). -/
def intersectionLeftTensorPure {R A : CommRingCat.{u}} (r : R ⟶ A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens)
    (a : A) (c : intersectionAlgebraSections f U) : intersectionLeftTensor r f U :=
  letI := r.hom.toAlgebra
  a ⊗ₜ[R] c

/-- The canonical tensor swap used to identify the second affine overlap.
Source: Stacks, Tag 0APK (blueprint: lem-a1-invariant-intersection-affine-descent). -/
def intersectionTensorSwap {R A : CommRingCat.{u}} (r : R ⟶ A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    intersectionLeftTensor r f U ⟶ CommRingCat.of (intersectionTensorSource r f U) :=
  letI := r.hom.toAlgebra
  CommRingCat.ofHom (Algebra.TensorProduct.comm R A
    (intersectionAlgebraSections f U)).toRingHom

/-- The canonical comparison with V in the second position, using symmetry of the
scheme pullback and the tensor product. Source: Stacks, Tag 0APK
(blueprint: lem-a1-invariant-intersection-affine-descent). -/
def intersectionLeftComparison {R A : CommRingCat.{u}} (r : R ⟶ A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec R) {I : Type v} (U : I → Y.Opens) :
    intersectionLeftTensor r f U ⟶
      intersectionSections (pullback (Spec.map r) f)
        (fun i ↦ pullback.snd (Spec.map r) f ⁻¹ᵁ U i) := by
  letI := r.hom.toAlgebra
  exact CommRingCat.ofHom (Algebra.TensorProduct.comm R A
    (intersectionAlgebraSections f U)).toRingHom ≫
    CommRingCat.ofHom (intersectionBaseChangeMap r f U).hom.toRingHom ≫
    intersectionSectionsMap (pullbackSymmetry (Spec.map r) f).hom _ _ (by
      intro x hx i
      change ((pullbackSymmetry (Spec.map r) f).hom ≫ pullback.fst f (Spec.map r)) x ∈ U i
      simpa only [pullbackSymmetry_hom_comp_fst, Hom.mem_preimage] using
        (hx i : pullback.snd (Spec.map r) f x ∈ U i))

/-- The canonical affine scheme over X attached to the section ring, with its actual
A-action from V. Source: Stacks, Tag 0APK
(blueprint: lem-a1-invariant-intersection-affine-descent). -/
def intersectionAffineModel {A : CommRingCat.{u}} (V : Over (Spec A))
    {I : Type v} (U : I → V.left.Opens) : Over (Spec A) :=
  Over.mk (Spec.map (intersectionScalars V.hom U))

/-- Tensor-spectrum identification for C tensor A with the affine model overlap.
Source: Stacks, Tag 0APK; affine pullbacks, Tag 01JO
(blueprint: lem-a1-invariant-intersection-affine-descent). -/
def intersectionAffineOverlapIso {R A : CommRingCat.{u}} (r : R ⟶ A)
    (V : Over (Spec A)) {I : Type v} (U : I → V.left.Opens) :
    pullback ((intersectionAffineModel V U).hom ≫ Spec.map r) (Spec.map r) ≅
      Spec (CommRingCat.of (intersectionTensorSource r (V.hom ≫ Spec.map r) U)) := by
  letI := r.hom.toAlgebra
  let C := intersectionAlgebraSections (V.hom ≫ Spec.map r) U
  exact (pullback.congrHom (by
    change Spec.map (intersectionScalars V.hom U) ≫ Spec.map r =
      Spec.map (intersectionScalars (V.hom ≫ Spec.map r) U)
    rw [← Spec.map_comp]
    congr 1
    unfold intersectionScalars
    simp only [Hom.comp_appTop, Category.assoc, ΓSpecIso_inv_naturality_assoc]) rfl) ≪≫
    pullbackSpecIso R C A

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionScalars_comp {R T : CommRingCat.{u}} (r : R ⟶ T)
    {Y : Scheme.{u}} (f : Y ⟶ Spec T) {I : Type v} (U : I → Y.Opens) :
    intersectionScalars (f ≫ Spec.map r) U = r ≫ intersectionScalars f U := by
  unfold intersectionScalars
  simp only [Hom.comp_appTop, Category.assoc, ΓSpecIso_inv_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
private def intersectionModelComparison {R A : CommRingCat.{u}} (r : R ⟶ A)
    (V : Over (Spec A)) {I : Type v} (U : I → V.left.Opens) :
    Spec (intersectionSections (pullback (V.hom ≫ Spec.map r) (Spec.map r))
      (fun i ↦ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ U i)) ⟶
      pullback ((intersectionAffineModel V U).hom ≫ Spec.map r) (Spec.map r) :=
  Spec.map (CommRingCat.ofHom
    (intersectionBaseChangeMap r (V.hom ≫ Spec.map r) U).hom.toRingHom) ≫
      (intersectionAffineOverlapIso r V U).inv

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionModelComparison_fst {R A : CommRingCat.{u}} (r : R ⟶ A)
    (V : Over (Spec A)) {I : Type v} (U : I → V.left.Opens) :
    intersectionModelComparison r V U ≫ pullback.fst _ _ =
      Spec.map (intersectionSectionsMap
        (pullback.fst (V.hom ≫ Spec.map r) (Spec.map r)) U
        (fun i ↦ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ U i)
        (fun _ hx ↦ hx)) := by
  let := r.hom.toAlgebra
  unfold intersectionModelComparison intersectionAffineOverlapIso
  simp only [Iso.trans_inv, Category.assoc, pullback.congrHom_inv,
    pullback.lift_fst, Category.comp_id]
  change Spec.map _ ≫ (pullbackSpecIso R
    (intersectionAlgebraSections (V.hom ≫ Spec.map r) U) A).inv ≫
      pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst]
  rw [← Spec.map_comp, intersectionBaseChangeMap_left]

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionModelComparison_snd {R A : CommRingCat.{u}} (r : R ⟶ A)
    (V : Over (Spec A)) {I : Type v} (U : I → V.left.Opens) :
    intersectionModelComparison r V U ≫ pullback.snd _ _ =
      Spec.map (intersectionScalars
        (pullback.snd (V.hom ≫ Spec.map r) (Spec.map r))
        (fun i ↦ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ U i)) := by
  let := r.hom.toAlgebra
  unfold intersectionModelComparison intersectionAffineOverlapIso
  simp only [Iso.trans_inv, Category.assoc, pullback.congrHom_inv,
    pullback.lift_snd, Category.comp_id]
  change Spec.map _ ≫ (pullbackSpecIso R
    (intersectionAlgebraSections (V.hom ≫ Spec.map r) U) A).inv ≫
      pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd]
  rw [← Spec.map_comp]
  exact congrArg Spec.map (intersectionBaseChangeMap_right r (V.hom ≫ Spec.map r) U)

set_option backward.isDefEq.respectTransparency false in
private lemma intersectionModelComparison_isIso {R A : CommRingCat.{u}} (r : R ⟶ A)
    [Flat (Spec.map r)] (V : Over (Spec A)) [QuasiSeparatedSpace V.left]
    {I : Type v} (U : I → V.left.Opens) (hI : Nonempty I)
    (hqc : ∀ i, IsCompact (U i : Set V.left)) :
    IsIso (intersectionModelComparison r V U) := by
  let β := CommRingCat.ofHom (intersectionBaseChangeMap r (V.hom ≫ Spec.map r) U).hom.toRingHom
  have hb := (flat_affine_intersection_sections_base_change.{u, v, v} r
    (V.hom ≫ Spec.map r) U hI hqc).1
  have : IsIso β := by
    exact ⟨⟨(RingEquiv.ofBijective β.hom hb).toCommRingCatIso.inv,
      (RingEquiv.ofBijective β.hom hb).toCommRingCatIso.hom_inv_id,
      (RingEquiv.ofBijective β.hom hb).toCommRingCatIso.inv_hom_id⟩⟩
  unfold intersectionModelComparison
  infer_instance

end Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Invariant intersections give canonical section-ring isomorphisms and effective affine
scheme descent. The ring cocycle is expressed equivalently by the transport cocycle of F:
Spec is fully faithful on rings and reverses composition, so F's universal three-point
identity is precisely psi_02 = psi_01 composed with psi_12. The iteration clause records
the canonical section comparisons used to make that identification.

Source: Stacks Project, Tag 0APK, section-ring comparisons and omitted cocycle check;
Tag 0245, affine effectivity (blueprint: lem-a1-invariant-intersection-affine-descent).

Proof:
1. Apply lem-a1-intersection-sections-flat-base-change to V over Spec R and T=A.
   Its comparison is the stated alpha0. Symmetry of tensor products and scheme pullbacks
   gives alpha1; both comparisons send a pure tensor to pullback times the scalar.
2. Restrict the datum to the indicated inverse-image sheaves, using
   lem-a1-subspace-ring-restriction-unit-coherence. Its comorphism b is the canonical
   intersectionSectionsMap. Put psi = alpha0 inverse composed with b and alpha1.
   Since the datum is over X times_S X, psi preserves both A-actions; tensor-pushout
   uniqueness (lem-weil-pbc-algebra-tensor-pushout-universal-property) gives linearity.
3. Apply the section comparison again with T=A tensor_R A. This is flat by
   lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-flat-ring-map-iff-flat-affine and lem-weil-pbc-flat-ring-map-comp.
   The naturality and iteration clauses identify the triple-overlap section maps with
   tensor pullbacks in all positions, with the canonical associators.
4. Restrict the given geometric cocycle. Unit coherence makes the restricted sheaf maps
   compose. On sections b02=b01 composed with b12; conjugating by the three comparisons
   cancels the middle comparison and gives psi02=psi01 composed with psi12.
5. Taking Spec and using lem-weil-pbc-fibre-product-affine-spectra gives the datum F
   with the indicated overlap map; contravariance reverses the ring cocycle.
6. The model is affine over X by lem-weil-pbc-morphism-affine-schemes-affine.
   Apply lem-galois-affine-flat-descent-effective: F.IsEffective gives Z0 over S and
   the datum-compatible pullback identification. Empty intersections give the zero ring
   and empty affine model, with the same formulas. -/
theorem invariant_intersection_affine_descent
    {R A : CommRingCat.{u}} (r : R ⟶ A)
    [Flat (Spec.map r)] [Surjective (Spec.map r)]
    (V : Over (Spec A)) [QuasiSeparatedSpace V.left]
    (D : Over.DescentDatum (Spec.map r) V)
    {I : Type v} (U : I → V.left.Opens) (hI : Nonempty I)
    (hqc : ∀ i, IsCompact (U i : Set V.left))
    (hinv : ∀ x : ↥(pullback (V.hom ≫ Spec.map r) (Spec.map r) : Scheme.{u}),
      (∀ i, pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) x ∈ U i) ↔ ∀ i, D.toHom x ∈ U i) :
    ∃ (α0 : CommRingCat.of (Scheme.intersectionTensorSource r
          (V.hom ≫ Spec.map r) U) ≅
        Scheme.intersectionSections (pullback (V.hom ≫ Spec.map r) (Spec.map r))
          (fun i ↦ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ U i))
      (α1 : Scheme.intersectionLeftTensor r (V.hom ≫ Spec.map r) U ≅
        Scheme.intersectionSections (pullback (Spec.map r) (V.hom ≫ Spec.map r))
          (fun i ↦ pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) ⁻¹ᵁ U i))
      (ψ : Scheme.intersectionLeftTensor r (V.hom ≫ Spec.map r) U ≅
        CommRingCat.of (Scheme.intersectionTensorSource r (V.hom ≫ Spec.map r) U)),
      α0.hom = CommRingCat.ofHom
        (Scheme.intersectionBaseChangeMap r (V.hom ≫ Spec.map r) U).hom.toRingHom ∧
      α1.hom = Scheme.intersectionLeftComparison r (V.hom ≫ Spec.map r) U ∧
      ψ.hom ≫ α0.hom = α1.hom ≫
        Scheme.intersectionSectionsMap (Scheme.invariantIntersectionOverlap r V D)
          (fun i ↦ pullback.snd (Spec.map r) (V.hom ≫ Spec.map r) ⁻¹ᵁ U i)
          (fun i ↦ pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ⁻¹ᵁ U i)
          (fun x hx i ↦ by
            change ((Scheme.invariantIntersectionOverlap r V D ≫
              pullback.snd (Spec.map r) (V.hom ≫ Spec.map r)) x) ∈ U i
            simpa only [Scheme.invariantIntersectionOverlap, pullback.lift_snd,
              Scheme.Hom.mem_preimage] using (hinv x).mp hx i) ∧
      (∀ a b : A,
        ψ.hom (Scheme.intersectionLeftTensorPure r (V.hom ≫ Spec.map r) U a
            (Scheme.intersectionScalars V.hom U b)) =
          Scheme.intersectionScalarTensorPure r
            (Scheme.intersectionAlgebraSections (V.hom ≫ Spec.map r) U)
            (Scheme.intersectionScalars V.hom U a) b) ∧
      Scheme.intersectionBaseChangeNaturality.{u, v, v} r (V.hom ≫ Spec.map r) U ∧
      Scheme.intersectionBaseChangeIteration r (V.hom ≫ Spec.map r) U ∧
      ∃ F : Over.DescentDatum (Spec.map r) (Scheme.intersectionAffineModel V U),
        F.IsEffective ∧
        Scheme.invariantIntersectionOverlap r (Scheme.intersectionAffineModel V U) F ≫
            (pullbackSymmetry (Spec.map r)
              ((Scheme.intersectionAffineModel V U).hom ≫ Spec.map r)).hom ≫
            (Scheme.intersectionAffineOverlapIso r V U).hom ≫
            Spec.map (Scheme.intersectionTensorSwap r (V.hom ≫ Spec.map r) U) =
          (Scheme.intersectionAffineOverlapIso r V U).hom ≫ Spec.map ψ.hom  := by
  classical
  let f := V.hom ≫ Spec.map r
  let P := pullback f (Spec.map r)
  let Q := pullback (Spec.map r) f
  let U₀ := fun i ↦ pullback.fst f (Spec.map r) ⁻¹ᵁ U i
  let U₁ := fun i ↦ pullback.snd (Spec.map r) f ⁻¹ᵁ U i
  let β := CommRingCat.ofHom (Scheme.intersectionBaseChangeMap r f U).hom.toRingHom
  obtain ⟨hβ, hβpure, hnat, hiter⟩ :=
    flat_affine_intersection_sections_base_change.{u, v, v} r f U hI hqc
  let α0 := (RingEquiv.ofBijective β.hom hβ).toCommRingCatIso
  have hα0 : α0.hom = β := rfl
  let σ := pullbackSymmetry (Spec.map r) f
  have hσ : ∀ x : Q, (∀ i, x ∈ U₁ i) ↔ ∀ i, σ.hom x ∈ U₀ i := by
    intro x
    have he : σ.hom ≫ pullback.fst f (Spec.map r) = pullback.snd (Spec.map r) f :=
      pullbackSymmetry_hom_comp_fst _ _
    change (∀ i, pullback.snd (Spec.map r) f x ∈ U i) ↔
      ∀ i, (σ.hom ≫ pullback.fst f (Spec.map r)) x ∈ U i
    rw [he]
  let bσ := Scheme.intersectionSectionsMap σ.hom U₀ U₁ (fun x hx ↦ (hσ x).mp hx)
  have : IsIso bσ := Scheme.intersectionSectionsMap_isIso σ U₀ U₁ hσ
  let := r.hom.toAlgebra
  let swap := (Algebra.TensorProduct.comm R A
    (Scheme.intersectionAlgebraSections f U)).toRingEquiv.toCommRingCatIso
  let α1 := swap ≪≫ α0 ≪≫ asIso bσ
  have hα1 : α1.hom = Scheme.intersectionLeftComparison r f U := rfl
  let φ := Scheme.invariantIntersectionOverlap r V D
  have hφ : ∀ x : P, (∀ i, x ∈ U₀ i) ↔ ∀ i, φ x ∈ U₁ i := by
    intro x
    change (∀ i, pullback.fst f (Spec.map r) x ∈ U i) ↔
      ∀ i, (φ ≫ pullback.snd (Spec.map r) f) x ∈ U i
    change (∀ i, pullback.fst f (Spec.map r) x ∈ U i) ↔
      ∀ i, (Scheme.invariantIntersectionOverlap r V D ≫
        pullback.snd (Spec.map r) (V.hom ≫ Spec.map r)) x ∈ U i
    simpa only [Scheme.invariantIntersectionOverlap, pullback.lift_snd] using hinv x
  have : IsIso φ := Scheme.invariantIntersectionOverlap_isIso r V D
  let b := Scheme.intersectionSectionsMap φ U₁ U₀ (fun x hx ↦ (hφ x).mp hx)
  have : IsIso b := Scheme.intersectionSectionsMap_isIso (asIso φ) U₁ U₀ hφ
  let ψ := α1 ≪≫ asIso b ≪≫ α0.symm
  refine ⟨α0, α1, ψ, hα0, hα1, ?_, ?_, hnat, hiter, ?_⟩
  · change (α1.hom ≫ b ≫ α0.inv) ≫ α0.hom = α1.hom ≫ b
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro a b'
    apply hβ.1
    change α0.hom (ψ.hom _) = α0.hom _
    have he : ψ.hom ≫ α0.hom = α1.hom ≫ b := by
      simp only [ψ, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      rfl
    rw [← CommRingCat.comp_apply, he]
    change b (bσ (β (Scheme.intersectionScalarTensorPure r
      (Scheme.intersectionAlgebraSections f U) (Scheme.intersectionScalars V.hom U b') a))) = _
    have hβpure' : ∀ (c : Scheme.intersectionAlgebraSections f U) (a : A),
        β (Scheme.intersectionScalarTensorPure r (Scheme.intersectionAlgebraSections f U) c a) =
          Scheme.intersectionSectionsMap (pullback.fst f (Spec.map r)) U U₀
            (fun _ hx ↦ hx) c * Scheme.intersectionScalars (pullback.snd f (Spec.map r)) U₀ a :=
      hβpure
    rw [hβpure']
    change b (bσ (_ * _)) = _
    rw [map_mul bσ.hom, map_mul b.hom]
    have hs : Scheme.intersectionScalars V.hom U ≫
        Scheme.intersectionSectionsMap (pullback.fst f (Spec.map r)) U U₀ (fun _ hx ↦ hx) =
        Scheme.intersectionScalars (pullback.fst f (Spec.map r) ≫ V.hom) U₀ := by
      simpa using Scheme.intersectionScalars_map (𝟙 A) V.hom
        (pullback.fst f (Spec.map r) ≫ V.hom) (pullback.fst f (Spec.map r))
        (by simp) U U₀ (fun _ hx ↦ hx)
    have hq : (φ ≫ σ.hom) ≫ pullback.snd f (Spec.map r) =
        pullback.fst f (Spec.map r) ≫ V.hom := by
      change (Scheme.invariantIntersectionOverlap r V D ≫
        (pullbackSymmetry (Spec.map r) (V.hom ≫ Spec.map r)).hom) ≫
          pullback.snd (V.hom ≫ Spec.map r) (Spec.map r) = _
      simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
        Scheme.invariantIntersectionOverlap, pullback.lift_fst]
      rfl
    have ht : (φ ≫ σ.hom) ≫ (pullback.fst f (Spec.map r) ≫ V.hom) =
        pullback.snd f (Spec.map r) := by
      change (Scheme.invariantIntersectionOverlap r V D ≫
        (pullbackSymmetry (Spec.map r) (V.hom ≫ Spec.map r)).hom) ≫
          pullback.fst (V.hom ≫ Spec.map r) (Spec.map r) ≫ V.hom = _
      rw [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc]
      rw [← Category.assoc]
      change (pullback.lift _ D.toHom _ ≫ pullback.snd _ _) ≫ V.hom = _
      rw [pullback.lift_snd]
      exact Scheme.toHom_over D
    have hbs : bσ ≫ b = Scheme.intersectionSectionsMap (φ ≫ σ.hom) U₀ U₀
        (fun x hx ↦ (hσ (φ x)).mp ((hφ x).mp hx)) :=
      (Scheme.intersectionSectionsMap_comp φ σ.hom U₀ U₁ U₀
        (fun x hx ↦ (hσ x).mp hx) (fun x hx ↦ (hφ x).mp hx)).symm
    have hleft := Scheme.intersectionScalars_map (𝟙 A)
      (pullback.fst f (Spec.map r) ≫ V.hom) (pullback.snd f (Spec.map r))
      (φ ≫ σ.hom) (by simpa using ht) U₀ U₀
      (fun x hx ↦ (hσ (φ x)).mp ((hφ x).mp hx))
    have hright := Scheme.intersectionScalars_map (𝟙 A)
      (pullback.snd f (Spec.map r)) (pullback.fst f (Spec.map r) ≫ V.hom)
      (φ ≫ σ.hom) (by simpa using hq) U₀ U₀
      (fun x hx ↦ (hσ (φ x)).mp ((hφ x).mp hx))
    have el : b (bσ (Scheme.intersectionSectionsMap (pullback.fst f (Spec.map r))
        U U₀ (fun _ hx ↦ hx) (Scheme.intersectionScalars V.hom U b'))) =
        Scheme.intersectionScalars (pullback.snd f (Spec.map r)) U₀ b' := by
      have hes := congrArg (fun z ↦ z b') hs
      rw [CommRingCat.comp_apply] at hes
      rw [hes]
      change (Scheme.intersectionScalars (pullback.fst f (Spec.map r) ≫ V.hom) U₀ ≫
        (bσ ≫ b)) b' = _
      rw [hbs, hleft]
      rfl
    have er : b (bσ (Scheme.intersectionScalars (pullback.snd f (Spec.map r)) U₀ a)) =
        Scheme.intersectionScalars (pullback.fst f (Spec.map r) ≫ V.hom) U₀ a := by
      change (Scheme.intersectionScalars (pullback.snd f (Spec.map r)) U₀ ≫ (bσ ≫ b)) a = _
      rw [hbs, hright]
      rfl
    rw [el, er]
    change _ = β _
    rw [hβpure']
    have hes := congrArg (fun z ↦ z a) hs
    rw [CommRingCat.comp_apply] at hes
    rw [hes, mul_comm]
  · let W := Scheme.intersectionAffineModel V U
    let s := pullback.fst f (Spec.map r)
    let q := pullback.snd f (Spec.map r)
    let t := D.toHom
    have ht : t ≫ V.hom = q := Scheme.toHom_over D
    have hinvt : ∀ x : P, (∀ i, x ∈ U₀ i) → ∀ i, t x ∈ U i :=
      fun x hx ↦ (hinv x).mp hx
    let bt := Scheme.intersectionSectionsMap t U U₀ hinvt
    let M := Scheme.intersectionModelComparison r V U
    have : IsIso M := Scheme.intersectionModelComparison_isIso r V U hI hqc
    let k := inv M ≫ Spec.map bt
    have hMk : M ≫ k = Spec.map bt := by
      dsimp only [k]
      rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    have hMs : M ≫ pullback.fst _ _ = Spec.map
        (Scheme.intersectionSectionsMap s U U₀ (fun _ hx ↦ hx)) :=
      Scheme.intersectionModelComparison_fst r V U
    have hMq : M ≫ pullback.snd _ _ = Spec.map (Scheme.intersectionScalars q U₀) :=
      Scheme.intersectionModelComparison_snd r V U
    have hk : k ≫ W.hom = pullback.snd _ _ := by
      apply (cancel_epi M).mp
      rw [← Category.assoc, hMk, hMq]
      change Spec.map bt ≫ Spec.map (Scheme.intersectionScalars V.hom U) = _
      rw [← Spec.map_comp]
      congr 1
      simpa using Scheme.intersectionScalars_map (𝟙 A) V.hom q t
        (by simpa using ht) U U₀ hinvt
    let d : V.left ⟶ P := pullback.lift (𝟙 _) V.hom (by simp [f])
    have hds : d ≫ s = 𝟙 _ := pullback.lift_fst _ _ _
    have hdq : d ≫ q = V.hom := pullback.lift_snd _ _ _
    have hdt : d ≫ t = 𝟙 _ := by
      have hh := Scheme.toHom_naturality D d V.hom V.hom rfl
        (Over.homMk (𝟙 _)) hds hdq
      rw [D.transport_self] at hh
      exact hh
    have hdU : ∀ x : V.left, (∀ i, x ∈ U i) → ∀ i, d x ∈ U₀ i := by
      intro x hx
      change ∀ i, (d ≫ s) x ∈ U i
      simpa only [hds, Scheme.Hom.id_base, TopCat.id_app] using hx
    let bd := Scheme.intersectionSectionsMap d U₀ U hdU
    have hsd : Spec.map bd ≫ M = pullback.lift (𝟙 W.left) W.hom (by simp [W]) := by
      apply pullback.hom_ext
      · rw [Category.assoc, hMs, Scheme.Spec_sectionsMap_comp]
        have hh := Scheme.intersectionSectionsMap_congr hds U U
          (fun x hx ↦ by
            simpa only [hds, Scheme.Hom.id_base, TopCat.id_app] using hx)
          (fun _ hx ↦ hx)
        exact (congrArg Spec.map hh).trans (by
          rw [Scheme.intersectionSectionsMap_id, Spec.map_id, pullback.lift_fst]
          rfl)
      · rw [Category.assoc, hMq, ← Spec.map_comp, pullback.lift_snd]
        change Spec.map (Scheme.intersectionScalars q U₀ ≫ bd) =
          Spec.map (Scheme.intersectionScalars V.hom U)
        congr 1
        simpa using Scheme.intersectionScalars_map (𝟙 A) q V.hom d
          (by simpa using hdq) U₀ U hdU
    have hself : pullback.lift (𝟙 W.left) W.hom (by simp [W]) ≫ k = 𝟙 _ := by
      rw [← hsd, Category.assoc, hMk, Scheme.Spec_sectionsMap_comp]
      rw [Scheme.intersectionSectionsMap_congr hdt U U _ (fun _ hx ↦ hx),
        Scheme.intersectionSectionsMap_id, Spec.map_id]
      all_goals rfl
    have hcocycle : ∀ (T : Scheme.{u})
        (a : T ⟶ pullback (W.hom ≫ Spec.map r) (Spec.map r)) (b : T ⟶ Spec A)
        (h : a ≫ pullback.snd _ _ ≫ Spec.map r = b ≫ Spec.map r),
        pullback.lift (a ≫ k) b
            (by
              change (a ≫ k) ≫ W.hom ≫ Spec.map r = _
              rw [Category.assoc, reassoc_of% hk]
              exact h) ≫ k =
          pullback.lift (a ≫ pullback.fst _ _) b
            (by
              change (a ≫ pullback.fst (W.hom ≫ Spec.map r) (Spec.map r)) ≫
                W.hom ≫ Spec.map r = _
              rw [Category.assoc, pullback.condition]
              exact h) ≫ k := by
      let P₂ := pullback (q ≫ Spec.map r) (Spec.map r)
      let j : P₂ ⟶ P := pullback.fst _ _
      let l : P₂ ⟶ Spec A := pullback.snd _ _
      let U₂ : I → P₂.Opens := fun i ↦ j ⁻¹ᵁ U₀ i
      have hj : j ≫ q ≫ Spec.map r = l ≫ Spec.map r := pullback.condition
      let u : P₂ ⟶ P := pullback.lift (j ≫ t) l (by
        change (j ≫ t) ≫ V.hom ≫ Spec.map r = _
        rw [Category.assoc, reassoc_of% ht]
        exact hj)
      let v' : P₂ ⟶ P := pullback.lift (j ≫ s) l (by
        change (j ≫ s) ≫ V.hom ≫ Spec.map r = _
        rw [Category.assoc, pullback.condition]
        exact hj)
      have hus : u ≫ s = j ≫ t := pullback.lift_fst _ _ _
      have huq : u ≫ q = l := pullback.lift_snd _ _ _
      have hvs : v' ≫ s = j ≫ s := pullback.lift_fst _ _ _
      have hvq : v' ≫ q = l := pullback.lift_snd _ _ _
      have huv : u ≫ t = v' ≫ t := by
        let a₀ : Over.mk (j ≫ s ≫ V.hom) ⟶ V := Over.homMk (j ≫ s)
        have h₁₂ : j ≫ s ≫ V.hom ≫ Spec.map r = j ≫ q ≫ Spec.map r := by
          change j ≫ s ≫ f = j ≫ q ≫ Spec.map r
          rw [pullback.condition]
        have h₁₃ := h₁₂.trans hj
        have hju : j ≫ t = (D.transport (j ≫ s ≫ V.hom) (j ≫ q) h₁₂ a₀).left :=
          Scheme.toHom_naturality D j (j ≫ s ≫ V.hom) (j ≫ q) h₁₂ a₀ rfl rfl
        have hu : u ≫ t = (D.transport (j ≫ q) l hj
            (D.transport (j ≫ s ≫ V.hom) (j ≫ q) h₁₂ a₀)).left := by
          apply Scheme.toHom_naturality D u (j ≫ q) l hj _ _ huq
          exact hus.trans hju
        have hv : v' ≫ t = (D.transport (j ≫ s ≫ V.hom) l h₁₃ a₀).left :=
          Scheme.toHom_naturality D v' (j ≫ s ≫ V.hom) l h₁₃ a₀ hvs hvq
        rw [hu, hv, D.transport_transport]
      have huU : ∀ x : P₂, (∀ i, x ∈ U₂ i) → ∀ i, u x ∈ U₀ i := by
        intro x hx
        change ∀ i, (u ≫ s) x ∈ U i
        rw [hus]
        exact hinvt (j x) hx
      have hvU : ∀ x : P₂, (∀ i, x ∈ U₂ i) → ∀ i, v' x ∈ U₀ i := by
        intro x hx
        change ∀ i, (v' ≫ s) x ∈ U i
        rw [hvs]
        exact hx
      let bu := Scheme.intersectionSectionsMap u U₀ U₂ huU
      let bv := Scheme.intersectionSectionsMap v' U₀ U₂ hvU
      have : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated s
      have hqc₀ : ∀ i, IsCompact (U₀ i : Set P) :=
        fun i ↦ s.isCompact_preimage (hqc i)
      have he : M ≫ (pullback.snd (W.hom ≫ Spec.map r) (Spec.map r) ≫
          Spec.map r) = Spec.map (Scheme.intersectionScalars (q ≫ Spec.map r) U₀) := by
        rw [← Category.assoc, hMq, ← Spec.map_comp, Scheme.intersectionScalars_comp]
      let N := Scheme.intersectionAffineComparisonTo r (q ≫ Spec.map r) U₀
        (pullback.snd (W.hom ≫ Spec.map r) (Spec.map r) ≫ Spec.map r) (asIso M) he
      have : IsIso N := Scheme.intersectionAffineComparisonTo_isIso r
        (q ≫ Spec.map r) U₀ hI hqc₀ _ (asIso M) he
      have hNj : N ≫ pullback.fst _ _ =
          Spec.map (Scheme.intersectionSectionsMap j U₀ U₂ (fun _ hx ↦ hx)) ≫ M :=
        Scheme.intersectionAffineComparisonTo_fst r (q ≫ Spec.map r) U₀ _ (asIso M) he
      have hNl : N ≫ pullback.snd _ _ = Spec.map (Scheme.intersectionScalars l U₂) :=
        Scheme.intersectionAffineComparisonTo_snd r (q ≫ Spec.map r) U₀ _ (asIso M) he
      let L := pullback
        (pullback.snd (W.hom ≫ Spec.map r) (Spec.map r) ≫ Spec.map r) (Spec.map r)
      let a₁ : L ⟶ pullback (W.hom ≫ Spec.map r) (Spec.map r) :=
        pullback.lift (pullback.fst _ _ ≫ k) (pullback.snd _ _) (by
          rw [Category.assoc, reassoc_of% hk]
          exact pullback.condition)
      let a₂ : L ⟶ pullback (W.hom ≫ Spec.map r) (Spec.map r) :=
        pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
          rw [Category.assoc, pullback.condition]
          exact pullback.condition)
      have hNu : N ≫ a₁ = Spec.map bu ≫ M := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hNj,
            Category.assoc, hMk, Scheme.Spec_sectionsMap_comp,
            Category.assoc, hMs, Scheme.Spec_sectionsMap_comp]
          congr 1
          exact Scheme.intersectionSectionsMap_congr hus.symm U U₂ _ _
        · rw [Category.assoc, pullback.lift_snd, hNl, Category.assoc, hMq,
            ← Spec.map_comp]
          congr 1
          exact (Scheme.intersectionScalars_map (𝟙 A) q l u
            (by simpa using huq) U₀ U₂ huU).symm
      have hNv : N ≫ a₂ = Spec.map bv ≫ M := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hNj,
            Category.assoc, hMs, Scheme.Spec_sectionsMap_comp,
            Category.assoc, hMs, Scheme.Spec_sectionsMap_comp]
          congr 1
          exact Scheme.intersectionSectionsMap_congr hvs.symm U U₂ _ _
        · rw [Category.assoc, pullback.lift_snd, hNl, Category.assoc, hMq,
            ← Spec.map_comp]
          congr 1
          exact (Scheme.intersectionScalars_map (𝟙 A) q l v'
            (by simpa using hvq) U₀ U₂ hvU).symm
      have hc : a₁ ≫ k = a₂ ≫ k := by
        apply (cancel_epi N).mp
        rw [← Category.assoc, hNu, Category.assoc, hMk,
          ← Category.assoc, hNv, Category.assoc, hMk,
          Scheme.Spec_sectionsMap_comp, Scheme.Spec_sectionsMap_comp]
        congr 1
        exact Scheme.intersectionSectionsMap_congr huv U U₂ _ _
      intro T a b h
      let ab : T ⟶ L := pullback.lift a b h
      have hab₁ : ab ≫ a₁ = pullback.lift (a ≫ k) b (by
          rw [Category.assoc, reassoc_of% hk]
          exact h) := by
        apply pullback.hom_ext <;>
          simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, ab, a₁]
      have hab₂ : ab ≫ a₂ = pullback.lift (a ≫ pullback.fst _ _) b (by
          rw [Category.assoc, pullback.condition]
          exact h) := by
        apply pullback.hom_ext <;>
          simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, ab, a₂]
      rw [← hab₁, ← hab₂, Category.assoc, Category.assoc, hc]
    let F := Scheme.descentDatumOfAction (Spec.map r) W k hk hself hcocycle
    have hFk : F.toHom = k := by
      change pullback.lift (pullback.fst _ _) (pullback.snd _ _) _ ≫ k = k
      rw [pullback.lift_fst_snd, Category.id_comp]
    refine ⟨F, ?_, ?_⟩
    · have : IsAffine W.left := by change IsAffine (Spec _); infer_instance
      have : IsAffineHom W.hom := isAffineHom_of_isAffine W.hom
      exact F.isEffective_of_isAffineHom_flat_affine (Spec.map r) inferInstance inferInstance
    · let i := φ ≫ σ.hom
      have hiU : ∀ x : P, (∀ j, x ∈ U₀ j) → ∀ j, i x ∈ U₀ j :=
        fun x hx ↦ (hσ (φ x)).mp ((hφ x).mp hx)
      let bi := Scheme.intersectionSectionsMap i U₀ U₀ hiU
      have his : i ≫ s = t := by
        change (Scheme.invariantIntersectionOverlap r V D ≫
          (pullbackSymmetry (Spec.map r) f).hom) ≫ pullback.fst f (Spec.map r) = _
        rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
        exact pullback.lift_snd _ _ _
      have hiq : i ≫ q = s ≫ V.hom := by
        change (Scheme.invariantIntersectionOverlap r V D ≫
          (pullbackSymmetry (Spec.map r) f).hom) ≫ pullback.snd f (Spec.map r) = _
        rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
        exact pullback.lift_fst _ _ _
      let iF := Scheme.invariantIntersectionOverlap r W F ≫
        (pullbackSymmetry (Spec.map r) (W.hom ≫ Spec.map r)).hom
      have hiFs : iF ≫ pullback.fst _ _ = k := by
        dsimp only [iF]
        rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
        change pullback.lift _ F.toHom _ ≫ pullback.snd _ _ = k
        rw [pullback.lift_snd, hFk]
      have hiFq : iF ≫ pullback.snd _ _ = pullback.fst _ _ ≫ W.hom := by
        dsimp only [iF]
        rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
        exact pullback.lift_fst _ _ _
      have hMi : M ≫ iF = Spec.map bi ≫ M := by
        apply pullback.hom_ext
        · rw [Category.assoc, hiFs, hMk, Category.assoc, hMs,
            Scheme.Spec_sectionsMap_comp]
          congr 1
          exact Scheme.intersectionSectionsMap_congr his.symm U U₀ _ _
        · rw [Category.assoc, hiFq, ← Category.assoc, hMs, Category.assoc, hMq]
          change Spec.map (Scheme.intersectionSectionsMap s U U₀ _) ≫
            Spec.map (Scheme.intersectionScalars V.hom U) =
              Spec.map bi ≫ Spec.map (Scheme.intersectionScalars q U₀)
          rw [← Spec.map_comp, ← Spec.map_comp]
          congr 1
          change Scheme.intersectionScalars V.hom U ≫
            Scheme.intersectionSectionsMap s U U₀ _ = Scheme.intersectionScalars q U₀ ≫ bi
          have h₁ := Scheme.intersectionScalars_map (𝟙 A) V.hom (s ≫ V.hom) s
            (by simp) U U₀ (fun _ hx ↦ hx)
          have h₂ := Scheme.intersectionScalars_map (𝟙 A) q (s ≫ V.hom) i
            (by simpa using hiq) U₀ U₀ hiU
          simpa only [Category.id_comp] using h₁.trans h₂.symm
      have hMH : M ≫ (Scheme.intersectionAffineOverlapIso r V U).hom = Spec.map β := by
        change (Spec.map β ≫ (Scheme.intersectionAffineOverlapIso r V U).inv) ≫
          (Scheme.intersectionAffineOverlapIso r V U).hom = _
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have hbs : bσ ≫ b = bi :=
        (Scheme.intersectionSectionsMap_comp φ σ.hom U₀ U₁ U₀
          (fun x hx ↦ (hσ x).mp hx) (fun x hx ↦ (hφ x).mp hx)).symm
      have hψ : swap.hom ≫ β ≫ bi = ψ.hom ≫ β := by
        change _ = (α1.hom ≫ b ≫ α0.inv) ≫ α0.hom
        rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
        change _ = (swap.hom ≫ β ≫ bσ) ≫ b
        rw [Category.assoc, Category.assoc, hbs]
      apply (cancel_epi M).mp
      change M ≫ iF ≫ (Scheme.intersectionAffineOverlapIso r V U).hom ≫
        Spec.map swap.hom = M ≫ (Scheme.intersectionAffineOverlapIso r V U).hom ≫
          Spec.map ψ.hom
      calc
        _ = (M ≫ iF) ≫ (Scheme.intersectionAffineOverlapIso r V U).hom ≫
            Spec.map swap.hom := by simp only [Category.assoc]
        _ = (Spec.map bi ≫ M) ≫ (Scheme.intersectionAffineOverlapIso r V U).hom ≫
            Spec.map swap.hom := by rw [hMi]
        _ = Spec.map bi ≫ Spec.map β ≫ Spec.map swap.hom := by
          rw [Category.assoc, reassoc_of% hMH]
        _ = Spec.map (swap.hom ≫ β ≫ bi) := by
          rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc]
        _ = Spec.map (ψ.hom ≫ β) := congrArg Spec.map hψ
        _ = _ := by rw [← Category.assoc M, hMH, ← Spec.map_comp]


end AlgebraicGeometry
