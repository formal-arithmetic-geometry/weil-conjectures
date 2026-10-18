/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.StageSystem.Shift

/-!
# The pair category of a stage system of triangulated categories

Let `S` be a stage system over a directed preorder whose stages `C i` are pretriangulated, whose
transition functors are triangulated and whose associators commute with the shifts. Then the pair
category `S.PairCategory`, the filtered `2`-colimit of the stages, is pretriangulated
(`CategoryTheory.StageSystem.PairCategory.pretriangulated`): a triangle is distinguished if it is
isomorphic to the image of a distinguished triangle of some stage under the stage inclusion. The
axioms are checked after moving finitely many data to a common stage. If the stages are
triangulated, so is the pair category, and the stage inclusions are triangulated functors.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits Pretriangulated Triangulated

/-- Lifting a commutative square to a morphism of triangles is invariant under isomorphisms of
triangles: if it can be done (for the transported square) for `T₁'` and `T₂'`, then it can be
done for isomorphic triangles `T₁` and `T₂`. -/
lemma Pretriangulated.Triangle.exists_comp_of_iso {C : Type*} [Category C] [HasShift C ℤ]
    {T₁ T₂ T₁' T₂' : Triangle C} (e₁ : T₁ ≅ T₁') (e₂ : T₂ ≅ T₂')
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (hab : T₁.mor₁ ≫ b = a ≫ T₂.mor₁)
    (H : T₁'.mor₁ ≫ (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) =
        (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁) ≫ T₂'.mor₁ →
      ∃ c' : T₁'.obj₃ ⟶ T₂'.obj₃, T₁'.mor₂ ≫ c' = (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) ≫ T₂'.mor₂ ∧
        T₁'.mor₃ ≫ (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)⟦1⟧' = c' ≫ T₂'.mor₃) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨c', h₁, h₂⟩ := H (by
    simp only [Category.assoc]
    rw [reassoc_of% e₁.inv.comm₁, reassoc_of% hab, e₂.hom.comm₁])
  refine ⟨e₁.hom.hom₃ ≫ c' ≫ e₂.inv.hom₃, ?_, ?_⟩
  · rw [reassoc_of% e₁.hom.comm₂, reassoc_of% h₁]
    rw [e₂.inv.comm₂, Iso.hom_inv_id_triangle_hom₂_assoc, Iso.hom_inv_id_triangle_hom₂_assoc]
  · have h₃ := e₂.inv.comm₃
    have h₄ := e₁.hom.comm₃
    simp only [Category.assoc]
    rw [← h₃, reassoc_of% h₂.symm.trans rfl]
    simp only [Functor.map_comp]
    rw [← reassoc_of% h₄]
    simp only [← Functor.map_comp, Category.assoc, Iso.hom_inv_id_triangle_hom₁,
      Iso.hom_inv_id_triangle_hom₁_assoc, Category.comp_id]

namespace StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i, HasShift (C i) ℤ] [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] (S : StageSystem C)
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ] [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
  [∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated]
  [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ]

open PairCategory

instance (a : ℤ) : (shiftFunctor S.PairCategory a).Additive := by
  have : ∀ i, ((S.shiftMorphism a).Φ i).Additive := fun i ↦
    inferInstanceAs (shiftFunctor (C i) a).Additive
  exact inferInstanceAs (S.shiftMorphism a).functor.Additive

/-- The distinguished triangles of the pair category: the triangles isomorphic to the image of a
distinguished triangle of some stage under the stage inclusion. -/
def distinguishedTriangles : Set (Triangle S.PairCategory) :=
  {T | ∃ (i : I) (D : Triangle (C i)) (_ : D ∈ distTriang (C i)),
    Nonempty (T ≅ (S.ι i).mapTriangle.obj D)}

variable {S}

/-- Moving a triangle of the stage `i` to a further stage `j`. -/
noncomputable def mapTriangleTransIso {i j : I} (h : i ≤ j) (D : Triangle (C i)) :
    (S.ι i).mapTriangle.obj D ≅ (S.ι j).mapTriangle.obj ((S.T h).mapTriangle.obj D) :=
  (Functor.mapTriangleIso (S.transIso h)).symm.app D ≪≫
    (Functor.mapTriangleCompIso (S.T h) (S.ι j)).app D

omit [∀ {i j : I} (h : i ≤ j), (S.T h).Additive] in
/-- Two distinguished triangles are, up to isomorphism, images of distinguished triangles at a
common stage, above any given stage. -/
lemma exists_common_stage_distTriang {T₁ T₂ : Triangle S.PairCategory}
    (h₁ : T₁ ∈ S.distinguishedTriangles) (h₂ : T₂ ∈ S.distinguishedTriangles) :
    ∃ (n : I) (D₁ D₂ : Triangle (C n)) (_ : D₁ ∈ Pretriangulated.distinguishedTriangles)
      (_ : D₂ ∈ Pretriangulated.distinguishedTriangles),
      Nonempty (T₁ ≅ (S.ι n).mapTriangle.obj D₁) ∧ Nonempty (T₂ ≅ (S.ι n).mapTriangle.obj D₂) := by
  obtain ⟨i₁, D₁, hD₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨i₂, D₂, hD₂, ⟨e₂⟩⟩ := h₂
  obtain ⟨n, h, h'⟩ := exists_ge_ge i₁ i₂
  exact ⟨n, _, _, (S.T h).map_distinguished _ hD₁, (S.T h').map_distinguished _ hD₂,
    ⟨e₁ ≪≫ mapTriangleTransIso h D₁⟩, ⟨e₂ ≪≫ mapTriangleTransIso h' D₂⟩⟩

omit [∀ {i j : I} (h : i ≤ j), (S.T h).Additive] in
/-- The lifting of commutative squares between images of distinguished triangles of the stage
`p`, for squares coming from the stage `p`. -/
lemma exists_comp_ι {p : I} {D₁ D₂ : Triangle (C p)} (hD₁ : D₁ ∈ distTriang (C p))
    (hD₂ : D₂ ∈ distTriang (C p)) (u : D₁.obj₁ ⟶ D₂.obj₁) (v : D₁.obj₂ ⟶ D₂.obj₂)
    (huv : (S.ι p).map D₁.mor₁ ≫ (S.ι p).map v = (S.ι p).map u ≫ (S.ι p).map D₂.mor₁) :
    ∃ c' : (S.ι p).obj D₁.obj₃ ⟶ (S.ι p).obj D₂.obj₃,
      (S.ι p).map D₁.mor₂ ≫ c' = (S.ι p).map v ≫ (S.ι p).map D₂.mor₂ ∧
      ((S.ι p).map D₁.mor₃ ≫ ((S.ι p).commShiftIso (1 : ℤ)).hom.app D₁.obj₁) ≫
          ((S.ι p).map u)⟦(1 : ℤ)⟧' =
        c' ≫ (S.ι p).map D₂.mor₃ ≫ ((S.ι p).commShiftIso (1 : ℤ)).hom.app D₂.obj₁ := by
  rw [← Functor.map_comp, ← Functor.map_comp, ι_map_eq_ι_map_iff] at huv
  obtain ⟨q, h, e⟩ := huv
  obtain ⟨c₀, hc₀, hc₀'⟩ : ∃ c₀ : (S.T h).obj D₁.obj₃ ⟶ (S.T h).obj D₂.obj₃,
      (S.T h).map D₁.mor₂ ≫ c₀ = (S.T h).map v ≫ (S.T h).map D₂.mor₂ ∧
      ((S.T h).map D₁.mor₃ ≫ ((S.T h).commShiftIso (1 : ℤ)).hom.app D₁.obj₁) ≫
          ((S.T h).map u)⟦(1 : ℤ)⟧' =
        c₀ ≫ (S.T h).map D₂.mor₃ ≫ ((S.T h).commShiftIso (1 : ℤ)).hom.app D₂.obj₁ :=
    complete_distinguished_triangle_morphism _ _
      ((S.T h).map_distinguished _ hD₁) ((S.T h).map_distinguished _ hD₂)
      ((S.T h).map u) ((S.T h).map v) (by simp only [Functor.map_comp] at e; exact e)
  have N := (S.transIso h).inv.naturality
  have N' := (S.transIso h).hom.naturality
  simp only [Functor.comp_map] at N N'
  refine ⟨(S.transIso h).inv.app _ ≫ (S.ι q).map c₀ ≫ (S.transIso h).hom.app _, ?_, ?_⟩
  · rw [reassoc_of% N, ← Functor.map_comp_assoc, hc₀]
    rw [Functor.map_comp, Category.assoc, N', reassoc_of% N', Iso.inv_hom_id_app_assoc]
  · have nat := ((S.T h).commShiftIso (1 : ℤ)).hom.naturality u
    simp only [Functor.comp_map] at nat
    have key : (S.T h).map (D₁.mor₃ ≫ u⟦(1 : ℤ)⟧') = c₀ ≫ (S.T h).map D₂.mor₃ := by
      rw [← cancel_mono (((S.T h).commShiftIso (1 : ℤ)).hom.app D₂.obj₁), Functor.map_comp,
        Category.assoc, nat]
      simpa only [Category.assoc] using hc₀'
    rw [ι_commShiftIso_hom_app, ι_commShiftIso_hom_app]
    erw [Category.comp_id, Category.comp_id, shiftFunctor_map_ι]
    rw [← Functor.map_comp, Category.assoc, Category.assoc, ← N', ← Functor.map_comp_assoc,
      ← key, N', Iso.inv_hom_id_app_assoc]

omit [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
  [∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated] in
lemma mapTriangleTransIso_hom_hom₁ {i j : I} (h : i ≤ j) (D : Triangle (C i)) :
    (mapTriangleTransIso (S := S) h D).hom.hom₁ = (S.transIso h).inv.app D.obj₁ :=
  Category.comp_id _

omit [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
  [∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated] in
lemma mapTriangleTransIso_hom_hom₂ {i j : I} (h : i ≤ j) (D : Triangle (C i)) :
    (mapTriangleTransIso (S := S) h D).hom.hom₂ = (S.transIso h).inv.app D.obj₂ :=
  Category.comp_id _

omit [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
  [∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated] in
lemma mapTriangleTransIso_inv_hom₁ {i j : I} (h : i ≤ j) (D : Triangle (C i)) :
    (mapTriangleTransIso (S := S) h D).inv.hom₁ = (S.transIso h).hom.app D.obj₁ :=
  Category.id_comp _

omit [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
  [∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated] in
lemma mapTriangleTransIso_inv_hom₂ {i j : I} (h : i ≤ j) (D : Triangle (C i)) :
    (mapTriangleTransIso (S := S) h D).inv.hom₂ = (S.transIso h).hom.app D.obj₂ :=
  Category.id_comp _

variable (S) in
/-- **The pair category of a stage system of pretriangulated categories along triangulated
transition functors is pretriangulated**: a triangle is distinguished if it is isomorphic to the
image of a distinguished triangle of some stage. -/
noncomputable instance PairCategory.pretriangulated [Nonempty I] :
    Pretriangulated S.PairCategory where
  distinguishedTriangles := S.distinguishedTriangles
  isomorphic_distinguished T₁ h₁ T₂ e := by
    obtain ⟨i, D, hD, ⟨e'⟩⟩ := h₁
    exact ⟨i, D, hD, ⟨e ≪≫ e'⟩⟩
  contractible_distinguished X := by
    refine ⟨X.stage, contractibleTriangle X.obj, contractible_distinguished _, ⟨?_⟩⟩
    refine Triangle.isoMk _ (Triangle.mk ((S.ι X.stage).map (𝟙 X.obj)) ((S.ι X.stage).map 0)
      ((S.ι X.stage).map 0 ≫ ((S.ι X.stage).commShiftIso (1 : ℤ)).hom.app X.obj)) (Iso.refl _)
      (Iso.refl _) ((isZero_zero _).iso ((S.ι X.stage).map_isZero (isZero_zero _))) ?_ ?_ ?_
    · change 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ (S.ι X.stage).map (𝟙 X.obj)
      rw [Functor.map_id]; rfl
    · exact ((S.ι X.stage).map_isZero (isZero_zero _)).eq_of_tgt _ _
    · exact (isZero_zero _).eq_of_src _ _
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨n, -, hX, hY, u, rfl⟩ := exists_le_mkHom_eq f X.stage
    obtain ⟨Z, v, w, hD⟩ := distinguished_cocone_triangle u
    refine ⟨(S.ι n).obj Z, (S.isoToStage Y hY).hom ≫ (S.ι n).map v,
      ((S.ι n).map w ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app _) ≫
        ((S.isoToStage X hX).inv)⟦(1 : ℤ)⟧', n, _, hD, ⟨?_⟩⟩
    refine Triangle.isoMk _ (Triangle.mk ((S.ι n).map u) ((S.ι n).map v)
      ((S.ι n).map w ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app _)) (S.isoToStage X hX)
      (S.isoToStage Y hY) (Iso.refl _) ?_ ?_ ?_
    · simp [mkHom_eq_isoToStage]
    · simp
    · simp [← Functor.map_comp]
  rotate_distinguished_triangle T := by
    constructor
    · rintro ⟨i, D, hD, ⟨e⟩⟩
      exact ⟨i, D.rotate, rot_of_distTriang _ hD,
        ⟨(rotate _).mapIso e ≪≫ ((S.ι i).mapTriangleRotateIso).app D⟩⟩
    · rintro ⟨i, D, hD, ⟨e⟩⟩
      exact ⟨i, D.invRotate, inv_rot_of_distTriang _ hD,
        ⟨(triangleRotation _).unitIso.app T ≪≫ (invRotate _).mapIso e ≪≫
          ((S.ι i).mapTriangleInvRotateIso).app D⟩⟩
  complete_distinguished_triangle_morphism T₁ T₂ h₁ h₂ a b hab := by
    obtain ⟨n, D₁, D₂, hD₁, hD₂, ⟨e₁⟩, ⟨e₂⟩⟩ := exists_common_stage_distTriang h₁ h₂
    refine Triangle.exists_comp_of_iso e₁ e₂ a b hab (fun hab' ↦ ?_)
    generalize e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁ = a' at hab' ⊢
    generalize e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂ = b' at hab' ⊢
    obtain ⟨p, hnp, hX, hY, hX', hY', u, v, rfl, rfl⟩ := exists_common_stage a' b' n
    refine Triangle.exists_comp_of_iso (mapTriangleTransIso hnp D₁)
      (mapTriangleTransIso hnp D₂) _ _ hab' (fun hab'' ↦ ?_)
    rw [mapTriangleTransIso_inv_hom₁, mapTriangleTransIso_hom_hom₁,
      transIso_hom_app_mkHom_transIso_inv_app] at hab'' ⊢
    rw [mapTriangleTransIso_inv_hom₂, mapTriangleTransIso_hom_hom₂,
      transIso_hom_app_mkHom_transIso_inv_app] at hab'' ⊢
    exact exists_comp_ι ((S.T hnp).map_distinguished _ hD₁)
      ((S.T hnp).map_distinguished _ hD₂) _ _ hab''

variable [Nonempty I]

lemma mem_distTriang_iff (T : Triangle S.PairCategory) :
    T ∈ distTriang S.PairCategory ↔ ∃ (i : I) (D : Triangle (C i)) (_ : D ∈ distTriang (C i)),
      Nonempty (T ≅ (S.ι i).mapTriangle.obj D) :=
  Iff.rfl

/-- The stage inclusions are triangulated functors. -/
instance (i : I) : (S.ι i).IsTriangulated where
  map_distinguished D hD := ⟨i, D, hD, ⟨Iso.refl _⟩⟩

/-- If the stages are triangulated, so is the pair category: an octahedron at a common stage
maps to an octahedron of the pair category. -/
instance PairCategory.isTriangulated [∀ i, IsTriangulated (C i)] :
    IsTriangulated S.PairCategory := by
  apply IsTriangulated.mk
  intro X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
  obtain ⟨n, -, h₁, h₂, h₂', h₃, u, v, rfl, rfl⟩ := exists_common_stage u₁₂ u₂₃ X₁.stage
  obtain ⟨_, _, _, h₁₂'⟩ := distinguished_cocone_triangle u
  obtain ⟨_, _, _, h₂₃'⟩ := distinguished_cocone_triangle v
  obtain ⟨_, _, _, h₁₃'⟩ := distinguished_cocone_triangle (u ≫ v)
  exact ⟨Octahedron.ofIso (e₁ := S.isoToStage X₁ h₁) (e₂ := S.isoToStage X₂ h₂)
    (e₃ := S.isoToStage X₃ h₃) (comm₁₂ := by rw [mkHom_eq_isoToStage]; simp)
    (comm₂₃ := by rw [mkHom_eq_isoToStage]; simp)
    (H := (someOctahedron rfl h₁₂' h₂₃' h₁₃').map (S.ι n)) ..⟩

end StageSystem

end CategoryTheory
