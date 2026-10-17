/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Shift
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# The pair category of a stage system of triangulated categories

Let `S` be a stage system of pretriangulated categories whose transition functors are
triangulated and whose associators commute with the shifts. A triangle of the pair category
`S.PairCategory` is *distinguished* if it is isomorphic to the image under a stage inclusion
`j_k` of a distinguished triangle of the stage `k`; equivalently, it is isomorphic to a
*common-stage cone triangle* `(E, K) → (F, L) → (M, C(u)) → (E, K)[1]` of a morphism
represented by `u : T_{M/E} K ⟶ T_{M/F} L`
(`CategoryTheory.StageSystem.PairCategory.cone_triangle_distinguished`).

With these triangles the pair category is pretriangulated, and it is triangulated when the
stages are. The stage inclusions are triangulated functors.

This is blueprint `def-weil-pbc-common-stage-cones` (the distinguished triangles), together with
the Verdier axioms for them, to which blueprint `def-weil-pbc-qbar-category` refers.

## Main definitions

- `CategoryTheory.StageSystem.PairCategory.distTriangles`: the distinguished triangles.
- `CategoryTheory.StageSystem.PairCategory.pretriangulated`: the pretriangulated structure.

## Main statements

- `CategoryTheory.StageSystem.PairCategory.isTriangulated`: the pair category is triangulated if
  the stages are.
- `CategoryTheory.StageSystem.ι_isTriangulated`: the stage inclusions are triangulated.
- `CategoryTheory.StageSystem.PairCategory.cone_triangle_distinguished`: common-stage cone
  triangles are distinguished.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject

namespace StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] {S : StageSystem C}

section Transport

variable [∀ i, HasShift (C i) ℤ] [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).CommShift ℤ]
  [S.ShiftCompatible ℤ] [∀ i, Preadditive (C i)] [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).Additive]
  [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]

variable (S) in
/-- The transport isomorphism `j_j(T_{j/i} K) ≅ j_i(K)` of triangles, for stages `i ≤ j`. -/
noncomputable def ιMapTriangleTransIso {i j : I} (h : i ≤ j) :
    (S.T h).mapTriangle ⋙ (S.ι j).mapTriangle ≅ (S.ι i).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫ Functor.mapTriangleIso (S.transIso h)

section

variable {i j : I} (h : i ≤ j) (T : Triangle (C i))

@[simp]
lemma ιMapTriangleTransIso_hom_app_hom₁ :
    ((S.ιMapTriangleTransIso h).hom.app T).hom₁ = (S.transIso h).hom.app T.obj₁ := by
  simp [ιMapTriangleTransIso]
  erw [Category.id_comp]

@[simp]
lemma ιMapTriangleTransIso_hom_app_hom₂ :
    ((S.ιMapTriangleTransIso h).hom.app T).hom₂ = (S.transIso h).hom.app T.obj₂ := by
  simp [ιMapTriangleTransIso]
  erw [Category.id_comp]

@[simp]
lemma ιMapTriangleTransIso_hom_app_hom₃ :
    ((S.ιMapTriangleTransIso h).hom.app T).hom₃ = (S.transIso h).hom.app T.obj₃ := by
  simp [ιMapTriangleTransIso]
  erw [Category.id_comp]

@[simp]
lemma ιMapTriangleTransIso_inv_app_hom₁ :
    ((S.ιMapTriangleTransIso h).inv.app T).hom₁ = (S.transIso h).inv.app T.obj₁ := by
  simp [ιMapTriangleTransIso]
  erw [Category.comp_id]

@[simp]
lemma ιMapTriangleTransIso_inv_app_hom₂ :
    ((S.ιMapTriangleTransIso h).inv.app T).hom₂ = (S.transIso h).inv.app T.obj₂ := by
  simp [ιMapTriangleTransIso]
  erw [Category.comp_id]

@[simp]
lemma ιMapTriangleTransIso_inv_app_hom₃ :
    ((S.ιMapTriangleTransIso h).inv.app T).hom₃ = (S.transIso h).inv.app T.obj₃ := by
  simp [ιMapTriangleTransIso]
  erw [Category.comp_id]

end

end Transport

namespace PairCategory

variable [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)] [∀ i, HasShift (C i) ℤ]
  [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive] [∀ i, Pretriangulated (C i)]
  [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).Additive] [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).IsTriangulated] [S.ShiftCompatible ℤ] [Nonempty I]

variable (S) in
/-- Blueprint `def-weil-pbc-common-stage-cones`: a triangle of the pair category is
distinguished if it is isomorphic to the image under a stage inclusion `j_k` of a
distinguished triangle of the stage `k`. -/
def distTriangles : Set (Triangle S.PairCategory) :=
  fun T ↦ ∃ (k : I) (T' : Triangle (C k)) (_ : T' ∈ distTriang (C k)),
    Nonempty (T ≅ (S.ι k).mapTriangle.obj T')

lemma ι_mapTriangle_mem_distTriangles {k : I} (T : Triangle (C k))
    (hT : T ∈ distTriang (C k)) : (S.ι k).mapTriangle.obj T ∈ distTriangles S :=
  ⟨k, T, hT, ⟨Iso.refl _⟩⟩

lemma mem_distTriangles_of_iso {T T' : Triangle S.PairCategory} (e : T ≅ T')
    (hT' : T' ∈ distTriangles S) : T ∈ distTriangles S := by
  obtain ⟨k, T'', hT'', ⟨e'⟩⟩ := hT'
  exact ⟨k, T'', hT'', ⟨e ≪≫ e'⟩⟩

/-- A distinguished triangle of the pair category is the image of a distinguished triangle of
any large enough stage. -/
lemma exists_iso_of_mem_distTriangles {T : Triangle S.PairCategory}
    (hT : T ∈ distTriangles S) (m₀ : I) :
    ∃ (m : I) (_ : m₀ ≤ m) (T' : Triangle (C m)) (_ : T' ∈ distTriang (C m)),
      Nonempty (T ≅ (S.ι m).mapTriangle.obj T') := by
  obtain ⟨k, T', hT', ⟨e⟩⟩ := hT
  obtain ⟨m, hm₀, hk⟩ := exists_ge_ge m₀ k
  exact ⟨m, hm₀, (S.T hk).mapTriangle.obj T', (S.T hk).map_distinguished T' hT',
    ⟨e ≪≫ ((S.ιMapTriangleTransIso hk).app T').symm⟩⟩

lemma contractible_mem_distTriangles (X : S.PairCategory) :
    contractibleTriangle X ∈ distTriangles S := by
  have hZ : IsZero ((S.ι X.stage).obj (0 : C X.stage)) := isZero_of_isZero (isZero_zero _)
  refine ⟨X.stage, contractibleTriangle X.obj, contractible_distinguished _, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ((isZero_zero _).iso hZ) ?_ ?_ ?_
  · change 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ (S.ι X.stage).map (𝟙 X.obj)
    rw [Functor.map_id]
    rfl
  · exact hZ.eq_of_tgt _ _
  · exact (isZero_zero _).eq_of_src _ _

lemma exists_cocone_mem_distTriangles {X Y : S.PairCategory} (f : X ⟶ Y) :
    ∃ (Z : S.PairCategory) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriangles S := by
  obtain ⟨n, -, hX, hY, u, rfl⟩ := exists_le_mkHom_eq f X.stage
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle u
  refine ⟨(S.ι n).obj Z, (S.isoToStage Y hY).hom ≫ (S.ι n).map g,
    (S.ι n).map h ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app _ ≫
      (S.isoToStage X hX).inv⟦(1 : ℤ)⟧', ⟨n, _, hT, ⟨?_⟩⟩⟩
  refine Triangle.isoMk _ _ (S.isoToStage X hX) (S.isoToStage Y hY) (Iso.refl _) ?_ ?_ ?_
  · simp [mkHom_eq_isoToStage hX hY u]; rfl
  · simp; rfl
  · simp [← Functor.map_comp]; rfl

lemma rotate_mem_distTriangles {T : Triangle S.PairCategory} (hT : T ∈ distTriangles S) :
    T.rotate ∈ distTriangles S := by
  obtain ⟨k, T', hT', ⟨e⟩⟩ := hT
  exact ⟨k, T'.rotate, rot_of_distTriang _ hT',
    ⟨(rotate _).mapIso e ≪≫ ((S.ι k).mapTriangleRotateIso).app T'⟩⟩

lemma invRotate_mem_distTriangles {T : Triangle S.PairCategory} (hT : T ∈ distTriangles S) :
    T.invRotate ∈ distTriangles S := by
  obtain ⟨k, T', hT', ⟨e⟩⟩ := hT
  exact ⟨k, T'.invRotate, inv_rot_of_distTriang _ hT',
    ⟨(invRotate _).mapIso e ≪≫ ((S.ι k).mapTriangleInvRotateIso).app T'⟩⟩

/-- The morphism axiom TR3 is invariant under isomorphisms of triangles. -/
lemma complete_morphism_of_iso {T₁ T₂ T₁' T₂' : Triangle S.PairCategory} (e₁ : T₁ ≅ T₁')
    (e₂ : T₂ ≅ T₂')
    (H : ∀ (a : T₁'.obj₁ ⟶ T₂'.obj₁) (b : T₁'.obj₂ ⟶ T₂'.obj₂),
      T₁'.mor₁ ≫ b = a ≫ T₂'.mor₁ → ∃ c, T₁'.mor₂ ≫ c = b ≫ T₂'.mor₂ ∧
        T₁'.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂'.mor₃)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (hcomm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨c, hc₂, hc₃⟩ := H (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁) (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) (by
    simp only [Category.assoc]
    rw [reassoc_of% e₁.inv.comm₁, reassoc_of% hcomm, e₂.hom.comm₁])
  refine ⟨e₁.hom.hom₃ ≫ c ≫ e₂.inv.hom₃, ?_, ?_⟩
  · rw [reassoc_of% e₁.hom.comm₂, reassoc_of% hc₂]
    simp only [Category.assoc, e₂.inv.comm₂, Iso.hom_inv_id_triangle_hom₂_assoc]
  · simp only [Category.assoc]
    rw [← e₂.inv.comm₃, ← reassoc_of% hc₃, ← reassoc_of% e₁.hom.comm₃, ← Functor.map_comp,
      ← Functor.map_comp]
    simp

/-- TR3 for images of distinguished triangles of a stage `k`, for morphisms represented at a
further stage `m` and commuting there. -/
lemma complete_morphism_ι_of_stage {k m : I} (h : k ≤ m) {T₁ T₂ : Triangle (C k)}
    (hT₁ : T₁ ∈ distTriang _) (hT₂ : T₂ ∈ distTriang _)
    (a : (S.T h).obj T₁.obj₁ ⟶ (S.T h).obj T₂.obj₁)
    (b : (S.T h).obj T₁.obj₂ ⟶ (S.T h).obj T₂.obj₂)
    (hcomm : (S.T h).map T₁.mor₁ ≫ b = a ≫ (S.T h).map T₂.mor₁) :
    ∃ c, ((S.ι k).mapTriangle.obj T₁).mor₂ ≫ c =
        mkHom (X := (S.ι k).obj T₁.obj₂) (Y := (S.ι k).obj T₂.obj₂) m h h b ≫
          ((S.ι k).mapTriangle.obj T₂).mor₂ ∧
      ((S.ι k).mapTriangle.obj T₁).mor₃ ≫
          (mkHom (X := (S.ι k).obj T₁.obj₁) (Y := (S.ι k).obj T₂.obj₁) m h h a)⟦(1 : ℤ)⟧' =
        c ≫ ((S.ι k).mapTriangle.obj T₂).mor₃ := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism _ _
    ((S.T h).map_distinguished _ hT₁) ((S.T h).map_distinguished _ hT₂) a b hcomm
  let ψ : (S.T h).mapTriangle.obj T₁ ⟶ (S.T h).mapTriangle.obj T₂ :=
    { hom₁ := a, hom₂ := b, hom₃ := c, comm₁ := hcomm, comm₂ := hc₂, comm₃ := hc₃ }
  let Φ := (S.ιMapTriangleTransIso h).inv.app T₁ ≫ (S.ι m).mapTriangle.map ψ ≫
    (S.ιMapTriangleTransIso h).hom.app T₂
  have e₁ : Φ.hom₁ = mkHom (X := (S.ι k).obj T₁.obj₁) (Y := (S.ι k).obj T₂.obj₁) m h h a := by
    simp [Φ, ψ, mkHom_eq_isoToStage (X := (S.ι k).obj T₁.obj₁) (Y := (S.ι k).obj T₂.obj₁) h h a,
      transIso_hom_app, transIso_inv_app]
    rfl
  have e₂ : Φ.hom₂ = mkHom (X := (S.ι k).obj T₁.obj₂) (Y := (S.ι k).obj T₂.obj₂) m h h b := by
    simp [Φ, ψ, mkHom_eq_isoToStage (X := (S.ι k).obj T₁.obj₂) (Y := (S.ι k).obj T₂.obj₂) h h b,
      transIso_hom_app, transIso_inv_app]
    rfl
  refine ⟨Φ.hom₃, ?_, ?_⟩
  · rw [← e₂]
    exact Φ.comm₂
  · rw [← e₁]
    exact Φ.comm₃

/-- TR3 for images of distinguished triangles of a common stage. -/
lemma complete_morphism_ι {k : I} {T₁ T₂ : Triangle (C k)}
    (hT₁ : T₁ ∈ distTriang _) (hT₂ : T₂ ∈ distTriang _)
    (a : (S.ι k).obj T₁.obj₁ ⟶ (S.ι k).obj T₂.obj₁)
    (b : (S.ι k).obj T₁.obj₂ ⟶ (S.ι k).obj T₂.obj₂)
    (hcomm : (S.ι k).map T₁.mor₁ ≫ b = a ≫ (S.ι k).map T₂.mor₁) :
    ∃ c, ((S.ι k).mapTriangle.obj T₁).mor₂ ≫ c = b ≫ ((S.ι k).mapTriangle.obj T₂).mor₂ ∧
      ((S.ι k).mapTriangle.obj T₁).mor₃ ≫ a⟦(1 : ℤ)⟧' =
        c ≫ ((S.ι k).mapTriangle.obj T₂).mor₃ := by
  obtain ⟨m, hkm, h₁, h₁', h₂, h₂', a', b', rfl, rfl⟩ := exists_common_stage a b k
  rw [ι_map_eq (h₂ : k ≤ m) T₁.mor₁, ι_map_eq (h₁' : k ≤ m) T₂.mor₁, mkHom_comp_mkHom,
    mkHom_comp_mkHom,
    mkHom_eq_mkHom_iff] at hcomm
  obtain ⟨p, hp, e⟩ := hcomm
  rw [← tr_injective, tr_comp, tr_comp, tr_map, tr_map] at e
  rw [← mkHom_tr hp a', ← mkHom_tr hp b']
  exact complete_morphism_ι_of_stage (hkm.trans hp) hT₁ hT₂ _ _ e

lemma complete_morphism_of_mem_distTriangles {T₁ T₂ : Triangle S.PairCategory}
    (hT₁ : T₁ ∈ distTriangles S) (hT₂ : T₂ ∈ distTriangles S)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (hcomm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨k₁, T₁', hT₁', ⟨e₁⟩⟩ := hT₁
  obtain ⟨k, hk, T₂', hT₂', ⟨e₂⟩⟩ := exists_iso_of_mem_distTriangles hT₂ k₁
  exact complete_morphism_of_iso (e₁ ≪≫ ((S.ιMapTriangleTransIso hk).app T₁').symm) e₂
    (complete_morphism_ι ((S.T hk).map_distinguished _ hT₁') hT₂') a b hcomm

/-- Blueprint `def-weil-pbc-common-stage-cones`: the pair category of a stage system of
pretriangulated categories is pretriangulated, the distinguished triangles being the triangles
isomorphic to images of distinguished triangles of a stage. -/
noncomputable instance pretriangulated : Pretriangulated S.PairCategory where
  distinguishedTriangles := distTriangles S
  isomorphic_distinguished _ hT _ e := mem_distTriangles_of_iso e hT
  contractible_distinguished := contractible_mem_distTriangles
  distinguished_cocone_triangle f := exists_cocone_mem_distTriangles f
  rotate_distinguished_triangle T :=
    ⟨rotate_mem_distTriangles, fun h ↦ mem_distTriangles_of_iso
      ((rotCompInvRot (C := S.PairCategory)).app T) (invRotate_mem_distTriangles h)⟩
  complete_distinguished_triangle_morphism _ _ hT₁ hT₂ a b hcomm :=
    complete_morphism_of_mem_distTriangles hT₁ hT₂ a b hcomm

lemma mem_distTriang_iff (T : Triangle S.PairCategory) :
    T ∈ distTriang S.PairCategory ↔ ∃ (k : I) (T' : Triangle (C k))
      (_ : T' ∈ distTriang (C k)), Nonempty (T ≅ (S.ι k).mapTriangle.obj T') :=
  Iff.rfl

/-- Blueprint `def-weil-pbc-common-stage-cones`: the common-stage cone triangle of a morphism
`f = [M, u] : (E, K) ⟶ (F, L)`. For a distinguished triangle
`T_{M/E} K ⟶ T_{M/F} L ⟶ C(u) ⟶ (T_{M/E} K)[1]` of the stage `M` extending `u`, the triangle
`(E, K) ⟶ (F, L) ⟶ (M, C(u)) ⟶ (E, K)[1]` of the pair category, whose second and third arrows
are the images of `i_u` and `p_u` under `j_M` composed with the transport isomorphisms
`(F, L) ≅ (M, T_{M/F} L)` and `(E, K) ≅ (M, T_{M/E} K)`, is distinguished. -/
lemma cone_triangle_distinguished {X Y : S.PairCategory} {n : I} (hX : X.stage ≤ n)
    (hY : Y.stage ≤ n) (u : X.toStage hX ⟶ Y.toStage hY) {Z : C n} (i : Y.toStage hY ⟶ Z)
    (p : Z ⟶ (X.toStage hX)⟦(1 : ℤ)⟧) (hT : Triangle.mk u i p ∈ distTriang _) :
    Triangle.mk (mkHom n hX hY u) ((S.isoToStage Y hY).hom ≫ (S.ι n).map i)
      ((S.ι n).map p ≫ ((S.ι n).commShiftIso (1 : ℤ)).hom.app _ ≫
        (S.isoToStage X hX).inv⟦(1 : ℤ)⟧') ∈ distTriang S.PairCategory := by
  refine ⟨n, _, hT, ⟨Triangle.isoMk _ _ (S.isoToStage X hX) (S.isoToStage Y hY) (Iso.refl _)
    ?_ ?_ ?_⟩⟩
  · simp [mkHom_eq_isoToStage hX hY u]; rfl
  · simp; rfl
  · simp [← Functor.map_comp]; rfl

/-- Every distinguished triangle of the pair category is isomorphic to the image of a
distinguished triangle of a stage. -/
lemma exists_iso_ι_mapTriangle {T : Triangle S.PairCategory} (hT : T ∈ distTriang _) :
    ∃ (k : I) (T' : Triangle (C k)) (_ : T' ∈ distTriang _),
      Nonempty (T ≅ (S.ι k).mapTriangle.obj T') :=
  hT

section Octahedron

variable [∀ i, IsTriangulated (C i)]

open Triangulated in
/-- The pair category of a stage system of triangulated categories is triangulated. -/
instance isTriangulated : IsTriangulated S.PairCategory := by
  apply IsTriangulated.mk
  intro X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ hcomm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
  obtain ⟨k, -, h₁, h₂, h₂', h₃, f, g, rfl, rfl⟩ := exists_common_stage u₁₂ u₂₃ X₁.stage
  subst hcomm
  obtain ⟨_, _, _, h₁₂'⟩ := distinguished_cocone_triangle f
  obtain ⟨_, _, _, h₂₃'⟩ := distinguished_cocone_triangle g
  obtain ⟨_, _, _, h₁₃'⟩ := distinguished_cocone_triangle (f ≫ g)
  have : (S.ι k).IsTriangulated := ⟨fun T hT ↦ ι_mapTriangle_mem_distTriangles T hT⟩
  exact ⟨Octahedron.ofIso (e₁ := S.isoToStage X₁ h₁) (e₂ := S.isoToStage X₂ h₂)
    (e₃ := S.isoToStage X₃ h₃) (comm₁₂ := by simp [mkHom_eq_isoToStage h₁ h₂ f])
    (comm₂₃ := by simp [mkHom_eq_isoToStage h₂' h₃ g])
    (H := (someOctahedron rfl h₁₂' h₂₃' h₁₃').map (S.ι k)) ..⟩

end Octahedron

end PairCategory

open PairCategory

variable [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)] [∀ i, HasShift (C i) ℤ]
  [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive] [∀ i, Pretriangulated (C i)]
  [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).Additive] [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).IsTriangulated] [S.ShiftCompatible ℤ] [Nonempty I]

/-- The stage inclusions are triangulated functors. -/
instance ι_isTriangulated (k : I) : (S.ι k).IsTriangulated where
  map_distinguished T hT := ι_mapTriangle_mem_distTriangles T hT

end StageSystem

end CategoryTheory
