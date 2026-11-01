/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveLineRestriction
public import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.Projective.ProjectiveLineTopClass
import WeilConjectures.WeilSheaf.Projective.ProjectiveLineOffTop
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import WeilConjectures.WeilSheaf.HomologyShift
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # The projective-line decomposition, normalized at infinity -/

@[expose] public section

universe u
open CategoryTheory Limits Preadditive Pretriangulated Triangulated

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

namespace AlgebraicGeometry.WeilComplex

section CalculationTStructure

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

private instance :
    (objectProperty k₀ l X).HasInducedTStructure _root_.DerivedCategory.TStructure.t :=
  .mk' fun K hK n ↦ by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncLE hc n⟩,
      ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
        _root_.DerivedCategory.homologyProperty_truncGE hc n⟩⟩

variable (k₀ l X) in
/-- The canonical t-structure on Weil complexes, induced by the canonical t-structure of the
derived category of pro-étale Weil sheaves. -/
private noncomputable def projectiveCalculationTStructure : TStructure (WeilComplex k₀ l X) :=
  (objectProperty k₀ l X).tStructure _root_.DerivedCategory.TStructure.t

private lemma projectiveCalculation_isLE_iff (K : WeilComplex k₀ l X) (n : ℤ) :
    (projectiveCalculationTStructure k₀ l X).IsLE K n ↔ K.obj.IsLE n :=
  ObjectProperty.tStructure_isLE_iff _ _ K n

private lemma projectiveCalculation_isGE_iff (K : WeilComplex k₀ l X) (n : ℤ) :
    (projectiveCalculationTStructure k₀ l X).IsGE K n ↔ K.obj.IsGE n :=
  ObjectProperty.tStructure_isGE_iff _ _ K n

private instance (G : WeilSheaf k₀ l X) :
    (projectiveCalculationTStructure k₀ l X).IsLE (WeilSheaf.toComplex.obj G) 0 :=
  (projectiveCalculation_isLE_iff _ _).2
    (inferInstanceAs (((_root_.DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).obj
      G.obj).IsLE 0))

private instance (G : WeilSheaf k₀ l X) :
    (projectiveCalculationTStructure k₀ l X).IsGE (WeilSheaf.toComplex.obj G) 0 :=
  (projectiveCalculation_isGE_iff _ _).2
    (inferInstanceAs (((_root_.DerivedCategory.singleFunctor (ProEtaleWeilSheaf k₀ l X) 0).obj
      G.obj).IsGE 0))

/-- A Weil complex concentrated in degree `b` is its cohomology sheaf `𝓗ᵇ` placed in
degree `b`. -/
private theorem projectiveCalculation_iso_single
    (K : WeilComplex k₀ l X) (b : ℤ)
    [(projectiveCalculationTStructure k₀ l X).IsGE K b]
    [(projectiveCalculationTStructure k₀ l X).IsLE K b] :
    Nonempty (K ≅ (WeilSheaf.toComplex.obj ((homologySheaf b).obj K))⟦-b⟧) := by
  have : K.obj.IsGE b := (projectiveCalculation_isGE_iff _ _).1 inferInstance
  have : K.obj.IsLE b := (projectiveCalculation_isLE_iff _ _).1 inferInstance
  obtain ⟨A, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K.obj b
  let eA : A ≅ ((homologySheaf b).obj K).obj :=
    ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ b).app A).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ b).mapIso e.symm
  exact ⟨ObjectProperty.isoMk _ (e ≪≫ (_root_.DerivedCategory.singleFunctor _ b).mapIso eA ≪≫
    ((_root_.DerivedCategory.singleFunctors _).shiftIso (-b) b 0 (by lia)).symm.app _ ≪≫
    (((objectProperty k₀ l X).ι.commShiftIso (-b)).app
      (WeilSheaf.toComplex.obj ((homologySheaf b).obj K))).symm)⟩

end CalculationTStructure

private noncomputable def bool_product_iso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    [HasFiniteProducts C] (f : Bool → C) :
    (∏ᶜ f) ≅ f true ⊞ f false where
  hom := biprod.lift (Pi.π _ true) (Pi.π _ false)
  inv := Pi.lift fun b ↦ by
    cases b
    · exact biprod.snd
    · exact biprod.fst
  hom_inv_id := by
    apply Pi.hom_ext
    intro b
    cases b <;> simp
  inv_hom_id := by
    apply biprod.hom_ext <;> simp

private theorem biprod_triangle_distinguished
    {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasBinaryBiproducts C] [HasFiniteProducts C]
    (T₁ T₂ : Triangle C) (h₁ : T₁ ∈ distTriang C) (h₂ : T₂ ∈ distTriang C) :
    Triangle.mk (biprod.map T₁.mor₁ T₂.mor₁) (biprod.map T₁.mor₂ T₂.mor₂)
      (biprod.map T₁.mor₃ T₂.mor₃ ≫
        ((shiftFunctor C (1 : ℤ)).mapBiprod T₁.obj₁ T₂.obj₁).inv) ∈ distTriang C := by
  let T : Bool → Triangle C := fun b ↦ if b then T₁ else T₂
  have hd : productTriangle T ∈ distTriang C :=
    productTriangle_distinguished T (by
      intro b
      cases b
      · exact h₂
      · exact h₁)
  refine isomorphic_distinguished _ hd _ (Triangle.isoMk _ _
    (bool_product_iso (fun b ↦ (T b).obj₁)).symm
    (bool_product_iso (fun b ↦ (T b).obj₂)).symm
    (bool_product_iso (fun b ↦ (T b).obj₃)).symm ?_ ?_ ?_)
  · apply Pi.hom_ext
    intro b
    cases b <;> simp [T, bool_product_iso, productTriangle]
  · apply Pi.hom_ext
    intro b
    cases b <;> simp [T, bool_product_iso, productTriangle]
  · rw [← cancel_mono (piComparison (shiftFunctor C (1 : ℤ)) _)]
    apply Pi.hom_ext
    intro b
    cases b <;> simp [T, bool_product_iso, productTriangle, Functor.mapBiprod_inv]
    all_goals
      simp only [biprod.desc_eq, add_comp, Category.assoc, ← Functor.map_comp]
      simp

private theorem biprod_desc_shift_isIso
    {C D : Type*} [Category C] [Category D] [Preadditive D]
    [HasBinaryBiproducts D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    {F₁ F₂ G : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ] [G.CommShift ℤ]
    (α : F₁ ⟶ G) (β : F₂ ⟶ G) [NatTrans.CommShift α ℤ]
    [NatTrans.CommShift β ℤ] (K : C) (n : ℤ)
    [IsIso (biprod.desc (α.app K) (β.app K))] :
    IsIso (biprod.desc (α.app (K⟦n⟧)) (β.app (K⟦n⟧))) := by
  have he : biprod.desc (α.app (K⟦n⟧)) (β.app (K⟦n⟧)) =
      (biprod.mapIso ((F₁.commShiftIso n).app K) ((F₂.commShiftIso n).app K)).hom ≫
        ((shiftFunctor D n).mapBiprod (F₁.obj K) (F₂.obj K)).inv ≫
        (biprod.desc (α.app K) (β.app K))⟦n⟧' ≫ (G.commShiftIso n).inv.app K := by
    apply biprod.hom_ext' <;>
      simp [NatTrans.app_shift, ← Functor.map_comp_assoc]
  rw [he]
  infer_instance

private theorem biprod_desc_triangle_isIso
    {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    [HasBinaryBiproducts D] [HasFiniteProducts D]
    {F₁ F₂ G : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ] [G.CommShift ℤ]
    [F₁.IsTriangulated] [F₂.IsTriangulated] [G.IsTriangulated]
    (α : F₁ ⟶ G) (β : F₂ ⟶ G) [NatTrans.CommShift α ℤ]
    [NatTrans.CommShift β ℤ] (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsIso (biprod.desc (α.app T.obj₁) (β.app T.obj₁)))
    (h₃ : IsIso (biprod.desc (α.app T.obj₃) (β.app T.obj₃))) :
    IsIso (biprod.desc (α.app T.obj₂) (β.app T.obj₂)) := by
  let S₁ := F₁.mapTriangle.obj T
  let S₂ := F₂.mapTriangle.obj T
  let S : Triangle D := Triangle.mk
    (biprod.map S₁.mor₁ S₂.mor₁) (biprod.map S₁.mor₂ S₂.mor₂)
    (biprod.map S₁.mor₃ S₂.mor₃ ≫
      ((shiftFunctor D (1 : ℤ)).mapBiprod S₁.obj₁ S₂.obj₁).inv)
  have hS : S ∈ distTriang D := biprod_triangle_distinguished S₁ S₂
    (F₁.map_distinguished T hT) (F₂.map_distinguished T hT)
  let φ : S ⟶ G.mapTriangle.obj T :=
    { hom₁ := biprod.desc (α.app T.obj₁) (β.app T.obj₁)
      hom₂ := biprod.desc (α.app T.obj₂) (β.app T.obj₂)
      hom₃ := biprod.desc (α.app T.obj₃) (β.app T.obj₃)
      comm₁ := by
        apply biprod.hom_ext' <;> simp [S, S₁, S₂, Functor.mapTriangle]
      comm₂ := by
        apply biprod.hom_ext' <;> simp [S, S₁, S₂, Functor.mapTriangle]
      comm₃ := by
        dsimp [S, S₁, S₂, Functor.mapTriangle]
        apply biprod.hom_ext' <;>
          simp [Category.assoc, Functor.mapBiprod_inv, ← Functor.map_comp,
            NatTrans.shift_app_comm] }
  exact isIso₂_of_isIso₁₃ φ hS (G.map_distinguished T hT) h₁ h₃

private theorem section_restriction_unit
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (I : D ⥤ C) (e : L ⋙ I ≅ 𝟭 C) (K : C) :
    adj.unit.app K ≫ e.inv.app ((L ⋙ R).obj K) ≫
      I.map (adj.counit.app (L.obj K)) ≫ e.hom.app K = 𝟙 K := by
  have h := e.inv.naturality (adj.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at h
  rw [← Category.assoc, ← Category.assoc, h]
  have ht : L.map (adj.unit.app K) ≫ adj.counit.app (L.obj K) = 𝟙 _ :=
    adj.left_triangle_components K
  simp only [Category.assoc, ← I.map_comp]
  rw [ht, I.map_id]
  simp

private theorem normalized_biprod_isIso
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {A B D : C} (f : A ⟶ B) (s : D ⟶ B) (r : B ⟶ D)
    (hs : s ≫ r = 𝟙 D) [IsIso (biprod.desc f s)] :
    IsIso (biprod.lift (inv (biprod.desc f s) ≫ biprod.fst) r) := by
  let d := biprod.desc f s
  let m : A ⊞ D ⟶ A ⊞ D :=
    biprod.lift biprod.fst (biprod.fst ≫ f ≫ r + biprod.snd)
  have hm : IsIso m := by
    refine ⟨⟨biprod.lift biprod.fst (-biprod.fst ≫ f ≫ r + biprod.snd), ?_, ?_⟩⟩
    all_goals
      apply biprod.hom_ext <;> simp [m, Category.assoc, comp_add]
  have he : biprod.lift (inv d ≫ biprod.fst) r = inv d ≫ m := by
    apply biprod.hom_ext
    · simp [m]
    · simp only [biprod.lift_snd, m, Category.assoc, biprod.lift_snd, comp_add]
      rw [← comp_add]
      have : biprod.fst ≫ f ≫ r + biprod.snd = d ≫ r := by
        simp [d, biprod.desc_eq, add_comp, Category.assoc, hs]
      rw [this, IsIso.inv_hom_id_assoc]
  rw [he]
  infer_instance

private theorem projectiveLine_unit_restriction
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l)
        (ProjectiveLine X ↘ X)).unit.app K ≫
      (projectiveLineRestriction X).app K = 𝟙 K := by
  let q := ProjectiveLine X ↘ X
  let i := ProjectiveLine.infinity X
  let : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change (i ≫ q) ≫ (X ↘ Spec (CommRingCat.of k₀)) = _
    rw [ProjectiveLine.infinity_over, Category.id_comp]⟩
  let L := upperStar (k₀ := k₀) (l := l) q
  let R := derivedLowerStar (k₀ := k₀) (l := l) q
  let I := upperStar (k₀ := k₀) (l := l) i
  let e : L ⋙ I ≅ 𝟭 _ :=
    (upperStarCompIso i q).symm ≪≫ upperStarCongrIso ProjectiveLine.infinity_over ≪≫
      upperStarIdIso X
  dsimp only [projectiveLineRestriction, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  change _ ≫ (e.inv.app ((L ⋙ R).obj K) ≫
    I.map ((upperStarDerivedLowerStarAdjunction q).counit.app (L.obj K)) ≫
      e.hom.app K) = _
  simpa only [Category.assoc] using
    section_restriction_unit (upperStarDerivedLowerStarAdjunction q) I e K

private theorem biprod_desc_isIso_of_iso
    {C D : Type*} [Category C] [Category D] [Preadditive D]
    [HasBinaryBiproducts D] {F₁ F₂ G : C ⥤ D}
    (α : F₁ ⟶ G) (β : F₂ ⟶ G) {K K' : C} (e : K ≅ K')
    [IsIso (biprod.desc (α.app K') (β.app K'))] :
    IsIso (biprod.desc (α.app K) (β.app K)) := by
  have he : biprod.desc (α.app K) (β.app K) =
      (biprod.mapIso (F₁.mapIso e) (F₂.mapIso e)).hom ≫
        biprod.desc (α.app K') (β.app K') ≫ G.map e.inv := by
    apply biprod.hom_ext' <;> simp
  rw [he]
  infer_instance

private theorem biprod_desc_weilComplex_isIso
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    {F₁ F₂ G : WeilComplex k₀ l X ⥤ WeilComplex k₀ l X}
    [F₁.CommShift ℤ] [F₂.CommShift ℤ] [G.CommShift ℤ]
    [F₁.IsTriangulated] [F₂.IsTriangulated] [G.IsTriangulated]
    (α : F₁ ⟶ G) (β : F₂ ⟶ G) [NatTrans.CommShift α ℤ]
    [NatTrans.CommShift β ℤ]
    (h : ∀ M : WeilSheaf k₀ l X,
      IsIso (biprod.desc (α.app (WeilSheaf.toComplex.obj M))
        (β.app (WeilSheaf.toComplex.obj M)))) (K : WeilComplex k₀ l X) :
    IsIso (biprod.desc (α.app K) (β.app K)) := by
  let t := projectiveCalculationTStructure k₀ l X
  have hbounded : ∀ (n : ℕ) (a : ℤ) (K : WeilComplex k₀ l X),
      t.IsGE K a → t.IsLE K (a + n - 1) →
      IsIso (biprod.desc (α.app K) (β.app K)) := by
    intro n
    induction n with
    | zero =>
      intro a K hge hle
      have hz := t.isZero K (a + (0 : ℕ) - 1) a (by omega)
      have h₁ := F₁.map_isZero hz
      have h₂ := F₂.map_isZero hz
      have hG := G.map_isZero hz
      exact ((biprod_isZero_iff _ _).2 ⟨h₁, h₂⟩).isIso hG _
    | succ n ih =>
      intro a K hge hle
      have : t.IsGE K a := hge
      have : t.IsLE K (a + n) := t.isLE_of_le K (a + (n + 1 : ℕ) - 1) _ (by omega)
      let T := (t.triangleLEGE (a + n - 1) (a + n) (by omega)).obj K
      have hT : T ∈ distTriang _ := t.triangleLEGE_distinguished _ _ _ K
      have h₁ : t.IsGE T.obj₁ a :=
        inferInstanceAs (t.IsGE ((t.truncLE (a + n - 1)).obj K) a)
      have h₁' : t.IsLE T.obj₁ (a + n - 1) :=
        inferInstanceAs (t.IsLE ((t.truncLE (a + n - 1)).obj K) (a + n - 1))
      have hi₁ := ih a T.obj₁ h₁ h₁'
      have : t.IsGE T.obj₃ (a + n) :=
        inferInstanceAs (t.IsGE ((t.truncGE (a + n)).obj K) (a + n))
      have : t.IsLE T.obj₃ (a + n) :=
        inferInstanceAs (t.IsLE ((t.truncGE (a + n)).obj K) (a + n))
      obtain ⟨e⟩ := projectiveCalculation_iso_single T.obj₃ (a + n)
      have := h ((homologySheaf (a + n)).obj T.obj₃)
      have := biprod_desc_shift_isIso α β
        (WeilSheaf.toComplex.obj ((homologySheaf (a + n)).obj T.obj₃)) (-(a + n))
      have hi₃ := biprod_desc_isIso_of_iso α β e
      exact biprod_desc_triangle_isIso α β T hT hi₁ hi₃
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  have hge : t.IsGE K a := (projectiveCalculation_isGE_iff _ _).2 ha
  have hle : t.IsLE K b := (projectiveCalculation_isLE_iff _ _).2 hb
  exact hbounded (b - a + 1).toNat a K hge
    (t.isLE_of_le K b _ (by omega))

private theorem isIso_map_desc_of_zero_left
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {A B E : C} (a : A ⟶ E) (b : B ⟶ E)
    (ha : IsZero (F.obj A)) [IsIso (F.map b)] : IsIso (F.map (biprod.desc a b)) := by
  have : IsIso (biprod.inr : F.obj B ⟶ F.obj A ⊞ F.obj B) :=
    (inferInstanceAs (IsIso (isoZeroBiprod ha).hom))
  have he : (biprod.inr ≫ (F.mapBiprod A B).inv) ≫ F.map (biprod.desc a b) = F.map b := by
    simp [← Functor.map_comp]
  have : IsIso ((biprod.inr ≫ (F.mapBiprod A B).inv) ≫ F.map (biprod.desc a b)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (biprod.inr ≫ (F.mapBiprod A B).inv) _

private theorem isIso_map_desc_of_zero_right
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {A B E : C} (a : A ⟶ E) (b : B ⟶ E)
    (hb : IsZero (F.obj B)) [IsIso (F.map a)] : IsIso (F.map (biprod.desc a b)) := by
  have : IsIso (biprod.inl : F.obj A ⟶ F.obj A ⊞ F.obj B) :=
    (inferInstanceAs (IsIso (isoBiprodZero hb).hom))
  have he : (biprod.inl ≫ (F.mapBiprod A B).inv) ≫ F.map (biprod.desc a b) = F.map a := by
    simp [← Functor.map_comp]
  have : IsIso ((biprod.inl ≫ (F.mapBiprod A B).inv) ≫ F.map (biprod.desc a b)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (biprod.inl ≫ (F.mapBiprod A B).inv) _

private noncomputable def tateTwist_single_iso
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (M : WeilSheaf k₀ l X) :
    (tateTwist k₀ l X (-1)).obj (WeilSheaf.toComplex.obj M) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.tateTwistSheaf k₀ l X (-1)).tensorObj M
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X (-1))) := by
  let L := WeilSheaf.tateTwistSheaf k₀ l X (-1)
  have hL := WeilSheaf.isLisse_tateTwistSheaf k₀ l X (-1)
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (L.dual hL).obj hL.dual
  let F := ProEtaleWeilSheaf.ihomFunctor k₀ l X (L.dual hL).obj
  exact ObjectProperty.isoMk _ (F.singleFunctorCompRightDerivedFunctorIso.app M.obj)

private theorem tateTwist_shift_single_isZero
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (M : WeilSheaf k₀ l X) (i : ℤ) (hi : i ≠ 2) :
    IsZero ((homologySheaf i).obj
      (((tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)).obj
        (WeilSheaf.toComplex.obj M)))) := by
  exact (isZero_homologySheaf_shift_toComplex _ (by omega : (-2 : ℤ) + i ≠ 0)).of_iso
    ((homologySheaf i).mapIso ((shiftFunctor _ (-2 : ℤ)).mapIso (tateTwist_single_iso M)))

private theorem projectiveLine_negative_cohomology
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (M : WeilSheaf k₀ l X) (i : ℤ) (hi : i < 0) :
    IsZero ((homologySheaf i).obj
      ((projectiveLineCohomology (k₀ := k₀) (l := l) X).obj
        (WeilSheaf.toComplex.obj M))) := by
  let q := ProjectiveLine X ↘ X
  let L := ProEtaleWeilSheaf.upperStar k₀ l q
  let R := ProEtaleWeilSheaf.lowerStar k₀ l q
  let e := R.rightDerivedFunctor.mapIso ((L.mapDerivedCategorySingleFunctor 0).app M.obj)
  have hge := R.isGE_rightDerivedFunctor_obj_singleFunctor (L.obj M.obj)
  have hzero := _root_.DerivedCategory.isZero_of_isGE (hX := hge) _ 0 i hi
  exact IsZero.of_full_of_faithful_of_isZero (WeilSheaf.objectProperty k₀ l X).ι _
    (hzero.of_iso ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e))

private theorem projectiveLine_desc_single_isIso
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (c : tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ) ⟶
      projectiveLineCohomology (k₀ := k₀) (l := l) X)
    (hc : ∀ M : WeilSheaf k₀ l X,
      IsIso ((homologySheaf 2).map (c.app (WeilSheaf.toComplex.obj M))))
    (M : WeilSheaf k₀ l X) :
    IsIso (biprod.desc (c.app (WeilSheaf.toComplex.obj M))
      ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l)
        (ProjectiveLine X ↘ X)).unit.app (WeilSheaf.toComplex.obj M))) := by
  let a := c.app (WeilSheaf.toComplex.obj M)
  let b := (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l)
    (ProjectiveLine X ↘ X)).unit.app (WeilSheaf.toComplex.obj M)
  obtain ⟨h0, hv⟩ := projectiveLine_cohomology_off_top X M
  have hmaps (i : ℤ) : IsIso ((homologySheaf i).map (biprod.desc a b)) := by
    by_cases hi0 : i = 0
    · subst i
      exact isIso_map_desc_of_zero_left (homologySheaf 0) a b
        (tateTwist_shift_single_isZero M 0 (by omega))
    by_cases hi2 : i = 2
    · subst i
      have := hc M
      exact isIso_map_desc_of_zero_right (homologySheaf 2) a b
        (isZero_homologySheaf_singleComplex (by omega) M)
    have hA := tateTwist_shift_single_isZero M i hi2
    have hB := isZero_homologySheaf_singleComplex hi0 M
    have hE : IsZero ((homologySheaf i).obj
        ((projectiveLineCohomology (k₀ := k₀) (l := l) X).obj
          (WeilSheaf.toComplex.obj M))) := by
      by_cases hi : i < 0
      · exact projectiveLine_negative_cohomology M i hi
      · exact hv i (by omega) hi2
    have hsource : IsZero ((homologySheaf i).obj (_ ⊞ _)) :=
      ((biprod_isZero_iff _ _).2 ⟨hA, hB⟩).of_iso
        ((homologySheaf i).mapBiprod _ _)
    exact hsource.isIso hE _
  have : IsIso ((objectProperty k₀ l X).ι.map (biprod.desc a b)) := by
    apply (_root_.DerivedCategory.isIso_iff _ _).2
    intro i
    have := hmaps i
    exact (WeilSheaf.objectProperty k₀ l X).ι.map_isIso
      ((homologySheaf i).map (biprod.desc a b))
  exact (objectProperty k₀ l X).fullyFaithfulι.isIso_of_isIso_map _

private noncomputable def firstInverseComponent
    {C D : Type*} [Category C] [Category D] [Preadditive D] [HasBinaryBiproducts D]
    {F₁ F₂ G : C ⥤ D} (α : F₁ ⟶ G) (β : F₂ ⟶ G)
    (h : ∀ K, IsIso (biprod.desc (α.app K) (β.app K))) : G ⟶ F₁ := by
  have := h
  have hα (K : C) : α.app K ≫ inv (biprod.desc (α.app K) (β.app K)) = biprod.inl := by
    calc
      _ = (biprod.inl ≫ biprod.desc (α.app K) (β.app K)) ≫
          inv (biprod.desc (α.app K) (β.app K)) := by simp
      _ = _ := by simp
  have hβ (K : C) : β.app K ≫ inv (biprod.desc (α.app K) (β.app K)) = biprod.inr := by
    calc
      _ = (biprod.inr ≫ biprod.desc (α.app K) (β.app K)) ≫
          inv (biprod.desc (α.app K) (β.app K)) := by simp
      _ = _ := by simp
  refine ⟨fun K ↦ inv (biprod.desc (α.app K) (β.app K)) ≫ biprod.fst, ?_⟩
  intro K K' f
  apply (cancel_epi (biprod.desc (α.app K) (β.app K))).mp
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, Category.assoc]
    rw [← α.naturality_assoc, reassoc_of% (hα K'), reassoc_of% (hα K)]
    simp
  · simp only [biprod.inr_desc_assoc, Category.assoc]
    rw [← β.naturality_assoc, reassoc_of% (hβ K'), reassoc_of% (hβ K)]
    simp

/-- The relative projective-line calculation with restriction to infinity as its degree-zero
coordinate (blueprint: lem-pur-b3-weil-projective-decomposition).

Source: blueprint `thm-amb-p1-decomposition` and `sk-prop-an` (integration); also the
projective-line decomposition used in
`thm-pur-rank-one-thom`, Step 3. For the proper projection q of the projective line, the unit
and the first Chern class give the decomposition Rq_*q^*K = K ⊕ K(-1)[-2]. The second
coordinate in the ordering here is restriction to infinity. To check this normalization,
restrict the unit to infinity: it is the identity by the adjunction identities. The Chern
class restricts to zero since O(1) restricted to that section is trivial. Thus the matrix of
restriction is (0,1). The other coordinate is the trace. The finite-coefficient projective
bundle formula and projection formula prove that the resulting matrix is invertible; pass
through the compatible adic system, extend scalars, and retain the Frobenius-equivariant
maps. Descent from finite coefficients preserves this isomorphism, giving the asserted
natural transformation for bounded constructible Weil complexes. This is only the proper
projective-line calculation; it does not assert the affine-line Thom isomorphism. -/
theorem exists_projectiveLine_trace_decomposition
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ p : projectiveLineCohomology (k₀ := k₀) (l := l) X ⟶
        tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ),
      ∀ K, IsIso (biprod.lift (p.app K) ((projectiveLineRestriction X).app K)) := by
  have : LocallyOfFiniteType (ProjectiveLine X ↘ Spec (CommRingCat.of k₀)) := by
    simpa only [comp_over] using (inferInstanceAs
      (LocallyOfFiniteType ((ProjectiveLine X ↘ X) ≫ (X ↘ Spec (CommRingCat.of k₀)))))
  let q := ProjectiveLine X ↘ X
  let adj := upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) q
  let : (derivedLowerStar (k₀ := k₀) (l := l) q).CommShift ℤ :=
    adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : (derivedLowerStar (k₀ := k₀) (l := l) q).IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  obtain ⟨c, hc, htop⟩ := exists_projectiveLine_top_class (k₀ := k₀) (l := l) X
  have := hc
  have hdesc (K : WeilComplex k₀ l X) : IsIso (biprod.desc (c.app K) (adj.unit.app K)) :=
    biprod_desc_weilComplex_isIso c adj.unit (projectiveLine_desc_single_isIso c htop) K
  refine ⟨firstInverseComponent c adj.unit hdesc, fun K ↦ ?_⟩
  have := hdesc K
  exact normalized_biprod_isIso (c.app K) (adj.unit.app K)
    ((projectiveLineRestriction X).app K) (projectiveLine_unit_restriction X K)

end AlgebraicGeometry.WeilComplex
