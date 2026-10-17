/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import WeilConjectures.CategoryTheory.StageSystem.Shift
public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated

/-!
# The pair category of a system of pretriangulated categories

Let `S` be a stage system of pretriangulated categories `C i` whose transition functors are
triangulated (they commute with the shift and preserve distinguished triangles) and whose
associators are compatible with the shifts. The pair category `S.PairCategory` carries the shift
of `CategoryTheory.StageSystem.PairCategory.hasShift`, and a triangle of `S.PairCategory` is
*distinguished* if it is isomorphic to the image under a stage inclusion `ι i` of a distinguished
triangle of the stage `i` (blueprint `def-weil-pbc-common-stage-cones`).

These data make the pair category pretriangulated (blueprint `thm-weil-pbc-verdier-axioms`);
the stage inclusions `ι i` are triangulated functors and the identifications
`T_{j/i} ⋙ ι j ≅ ι i` commute with the shifts. The proofs of the axioms reduce, by transport to a
common stage, to the corresponding axioms at a finite stage.

The *common-stage cone triangle* `CategoryTheory.StageSystem.PairCategory.coneTriangle` of a
representative `u` at a stage `n` of a morphism `f` and of a distinguished triangle on `u` is
distinguished, and the cone triangles of two representatives of the same morphism are isomorphic
by an isomorphism whose first two components are identities
(blueprint `prop-weil-pbc-cone-independence`).

## Main definitions

- `CategoryTheory.StageSystem.PairCategory.distinguishedTriangles`.
- `CategoryTheory.StageSystem.PairCategory.pretriangulated`.
- `CategoryTheory.StageSystem.PairCategory.coneTriangle`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject

namespace StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i, HasShift (C i) ℤ] [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] {S : StageSystem C}
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ] [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated]
  [∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k), NatTrans.CommShift (S.assoc h h').hom ℤ]

namespace PairCategory

instance (n : ℤ) : (shiftFunctor S.PairCategory n).Additive :=
  inferInstanceAs (S.shiftMorphism ℤ n).functor.Additive

instance [Nonempty I] : HasZeroObject S.PairCategory := hasZeroObject

variable (S) in
/-- The distinguished triangles of the pair category (blueprint
`def-weil-pbc-common-stage-cones`): the triangles which are isomorphic to the image under a stage
inclusion `ι i` of a distinguished triangle of the stage `i`. -/
def distinguishedTriangles : Set (Triangle S.PairCategory) :=
  fun T ↦ ∃ (i : I) (τ : Triangle (C i)), τ ∈ distTriang (C i) ∧
    Nonempty (T ≅ (S.ι i).mapTriangle.obj τ)

lemma isomorphic_distinguished (T₁ : Triangle S.PairCategory)
    (h₁ : T₁ ∈ distinguishedTriangles S) (T₂ : Triangle S.PairCategory) (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles S := by
  obtain ⟨i, τ, hτ, ⟨e'⟩⟩ := h₁
  exact ⟨i, τ, hτ, ⟨e ≪≫ e'⟩⟩

lemma mapTriangle_mem_distinguishedTriangles {i : I} (τ : Triangle (C i))
    (hτ : τ ∈ distTriang (C i)) : (S.ι i).mapTriangle.obj τ ∈ distinguishedTriangles S :=
  ⟨i, τ, hτ, ⟨Iso.refl _⟩⟩

/-- A triangle whose first morphism is isomorphic to the first morphism of a triangle `τ` can be
completed to a triangle isomorphic to `τ`. -/
def triangleOfArrowIso {D : Type*} [Category* D] [HasShift D ℤ] (τ : Triangle D) {X Y : D}
    (f : X ⟶ Y) (e₁ : τ.obj₁ ≅ X) (e₂ : τ.obj₂ ≅ Y) (comm : τ.mor₁ ≫ e₂.hom = e₁.hom ≫ f) :
    τ ≅ Triangle.mk f (e₂.inv ≫ τ.mor₂) (τ.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') :=
  Triangle.isoMk _ _ e₁ e₂ (Iso.refl _) comm (by simp) (by simp)

lemma contractible_distinguished [Nonempty I] (X : S.PairCategory) :
    contractibleTriangle X ∈ distinguishedTriangles S := by
  refine ⟨X.stage, contractibleTriangle X.obj, Pretriangulated.contractible_distinguished _,
    ⟨Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((isZero_zero _).iso (isZero_ι_obj (isZero_zero _))) ?_ ?_ ?_⟩⟩
  · exact ((comp_id _).trans ((S.ι X.stage).map_id X.obj).symm).trans (id_comp _).symm
  · exact (isZero_ι_obj (isZero_zero _)).eq_of_tgt _ _
  · exact (isZero_zero _).eq_of_src _ _

lemma distinguished_cocone_triangle {X Y : S.PairCategory} (f : X ⟶ Y) :
    ∃ (Z : S.PairCategory) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles S := by
  obtain ⟨n, -, hX, hY, u, rfl⟩ := exists_le_mkHom_eq f X.stage
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle u
  have comm : (S.ι n).map u ≫ (S.isoToStage Y hY).inv =
      (S.isoToStage X hX).inv ≫ mkHom n hX hY u := by
    simp [mkHom_eq_isoToStage]
  exact ⟨_, _, _, n, _, hT, ⟨(triangleOfArrowIso ((S.ι n).mapTriangle.obj (Triangle.mk u g h))
    (mkHom n hX hY u) (S.isoToStage X hX).symm (S.isoToStage Y hY).symm comm).symm⟩⟩

lemma rotate_distinguished_triangle (T : Triangle S.PairCategory) :
    T ∈ distinguishedTriangles S ↔ T.rotate ∈ distinguishedTriangles S := by
  constructor
  · rintro ⟨i, τ, hτ, ⟨e⟩⟩
    exact ⟨i, τ.rotate, rot_of_distTriang _ hτ,
      ⟨(rotate _).mapIso e ≪≫ (S.ι i).mapTriangleRotateIso.app τ⟩⟩
  · rintro ⟨i, τ, hτ, ⟨e⟩⟩
    exact ⟨i, τ.invRotate, inv_rot_of_distTriang _ hτ,
      ⟨(rotCompInvRot (C := S.PairCategory)).app T ≪≫ (invRotate _).mapIso e ≪≫
        (S.ι i).mapTriangleInvRotateIso.app τ⟩⟩

/-- The morphism axiom for images of distinguished triangles of two stages: after transport to a
common stage where the given square commutes, it follows from the morphism axiom there. -/
lemma exists_hom₃_ι {i j : I} (τ₁ : Triangle (C i)) (τ₂ : Triangle (C j))
    (h₁ : τ₁ ∈ distTriang (C i)) (h₂ : τ₂ ∈ distTriang (C j))
    (a : (S.ι i).obj τ₁.obj₁ ⟶ (S.ι j).obj τ₂.obj₁) (b : (S.ι i).obj τ₁.obj₂ ⟶ (S.ι j).obj τ₂.obj₂)
    (comm : (S.ι i).map τ₁.mor₁ ≫ b = a ≫ (S.ι j).map τ₂.mor₁) :
    ∃ c : (S.ι i).obj τ₁.obj₃ ⟶ (S.ι j).obj τ₂.obj₃,
      (S.ι i).map τ₁.mor₂ ≫ c = b ≫ (S.ι j).map τ₂.mor₂ ∧
      ((S.ι i).map τ₁.mor₃ ≫ ((S.ι i).commShiftIso (1 : ℤ)).hom.app τ₁.obj₁) ≫ a⟦(1 : ℤ)⟧' =
        c ≫ ((S.ι j).map τ₂.mor₃ ≫ ((S.ι j).commShiftIso (1 : ℤ)).hom.app τ₂.obj₁) := by
  obtain ⟨m, hi, hj⟩ := exists_ge_ge i j
  obtain ⟨n, -, hX, hY, hX', hY', u, u', rfl, rfl⟩ := exists_common_stage a b m
  rw [ι_map_eq (hX : i ≤ n), ι_map_eq (hY : j ≤ n), mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_eq_mkHom_iff] at comm
  obtain ⟨q, hq, e⟩ := comm
  rw [← tr_injective, tr_comp, tr_comp, tr_map, tr_map] at e
  obtain ⟨c, hc₂, hc₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism _ _
    ((S.T (hX.trans hq)).map_distinguished _ h₁) ((S.T (hY.trans hq)).map_distinguished _ h₂)
    (S.tr hq u) (S.tr hq u') e
  refine ⟨mkHom q (hX.trans hq) (hY.trans hq) c, ?_, ?_⟩
  · rw [← mkHom_tr hq u', ι_map_eq (hX.trans hq : i ≤ q), ι_map_eq (hY.trans hq : j ≤ q), mkHom_comp_mkHom,
      mkHom_comp_mkHom]
    exact congr_arg _ hc₂
  · simp only [ι_commShiftIso_hom_app, comp_id]
    rw [← mkHom_tr hq u, shiftFunctor_map_mkHom, ι_map_eq (hX.trans hq : i ≤ q), ι_map_eq (hY.trans hq : j ≤ q),
      mkHom_comp_mkHom, mkHom_comp_mkHom]
    congr 1
    simp only [Functor.mapTriangle_obj, Triangle.mk_mor₃, Triangle.mk_obj₁, Category.assoc]
      at hc₃
    rw [reassoc_of% hc₃]
    simp

lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle S.PairCategory)
    (h₁ : T₁ ∈ distinguishedTriangles S) (h₂ : T₂ ∈ distinguishedTriangles S)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨i, τ₁, hτ₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨j, τ₂, hτ₂, ⟨e₂⟩⟩ := h₂
  exact Idempotents.Karoubi.exists_hom₃_of_retract (Retract.ofIso e₁) (Retract.ofIso e₂)
    (fun a b comm ↦ exists_hom₃_ι τ₁ τ₂ hτ₁ hτ₂ a b comm) a b comm

variable [Nonempty I]

/-- Blueprint `thm-weil-pbc-verdier-axioms` (the axioms TR1–TR3): the pair category of a stage
system of pretriangulated categories with triangulated transition functors is pretriangulated,
for the shift of `CategoryTheory.StageSystem.PairCategory.hasShift` and the triangles isomorphic
to images of distinguished triangles of a single stage. -/
noncomputable instance pretriangulated : Pretriangulated S.PairCategory where
  distinguishedTriangles := distinguishedTriangles S
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

lemma mem_distTriang_iff (T : Triangle S.PairCategory) :
    T ∈ distTriang S.PairCategory ↔ ∃ (i : I) (τ : Triangle (C i)), τ ∈ distTriang (C i) ∧
      Nonempty (T ≅ (S.ι i).mapTriangle.obj τ) := Iff.rfl

end PairCategory

open PairCategory

variable [Nonempty I]

/-- The stage inclusions are triangulated functors. -/
instance ι_isTriangulated (i : I) : (S.ι i).IsTriangulated where
  map_distinguished τ hτ := mapTriangle_mem_distinguishedTriangles τ hτ

end StageSystem

end CategoryTheory
