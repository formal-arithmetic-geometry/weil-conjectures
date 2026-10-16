/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.PairCategory.Transport
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# The pair category of a directed system of triangulated categories

Let `F` be a pseudofunctor from a directed preorder to pretriangulated categories whose
transition functors are triangulated, the unit and composition isomorphisms commuting with the
shifts. A triangle of the pair category `PairCategory F` is *distinguished* if it is isomorphic
to the image under a stage inclusion `j_k` of a distinguished triangle of the stage `k`:
equivalently, it is isomorphic to a *common-stage cone triangle*
`(E, K) → (F, L) → (M, C(u)) → (E, K)[1]` of a morphism represented by
`u : T_{M/E} K ⟶ T_{M/F} L` (`PairCategory.cone_triangle_distinguished`).

With these triangles the pair category is pretriangulated, and it is triangulated when the
stages are. The stage inclusions are triangulated functors.

This is blueprint `def-weil-pbc-common-stage-cones` (the distinguished triangles) together with
the Verdier axioms for them, which blueprint `def-weil-pbc-qbar-category` refers to.

## Main definitions

- `CategoryTheory.PairCategory.distTriangles` : the distinguished triangles.
- `CategoryTheory.PairCategory.pretriangulated` : the pretriangulated structure.

## Main results

- `CategoryTheory.PairCategory.isTriangulated` : the pair category is triangulated if the
  stages are.
- `CategoryTheory.PairCategory.incl_isTriangulated` : the stage inclusions are triangulated.
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits Pseudofunctor Pretriangulated ZeroObject

namespace CategoryTheory.PairCategory

variable {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)]
  {F : Pseudofunctor (LocallyDiscrete ι) Cat.{v, u}}

section ShiftUnit

variable [∀ i : ι, HasShift (F.obj ⟨i⟩) ℤ] [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).CommShift ℤ]
  [ShiftCompatible F ℤ]

/-- The unit isomorphism `T_{k/k} ≅ 𝟭` commutes with the shifts, in the form used for the
third arrow of cone triangles. -/
@[reassoc]
lemma transitionId_inv_shift (k : ι) (h : k ≤ k) (n : ℤ) (K : F.obj ⟨k⟩) :
    ((F.transitionId k h).inv.app K)⟦n⟧' ≫ ((F.transition h).commShiftIso n).inv.app K =
      (F.transitionId k h).inv.app (K⟦n⟧) := by
  have e := NatTrans.shift_app_comm (F.transitionId k h).hom n K
  rw [Functor.commShiftIso_id_hom_app] at e
  erw [comp_id] at e
  rw [← cancel_epi (((F.transitionId k h).hom.app K)⟦n⟧'), ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, id_comp,
    ← cancel_epi (((F.transition h).commShiftIso n).hom.app K), Iso.hom_inv_id_app,
    reassoc_of% e, Iso.hom_inv_id_app]
  rfl

end ShiftUnit

section Transport

variable [∀ i : ι, Preadditive (F.obj ⟨i⟩)] [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).Additive]
  [∀ i : ι, HasShift (F.obj ⟨i⟩) ℤ] [∀ (i : ι) (n : ℤ), (shiftFunctor (F.obj ⟨i⟩) n).Additive]
  [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).CommShift ℤ] [ShiftCompatible F ℤ]

lemma trHom_transition_map {k m m' : ι} (h : k ≤ m) (h' : m ≤ m') {A B : F.obj ⟨k⟩}
    (u : A ⟶ B) :
    trHom (X := (incl F k).obj A) (Y := (incl F k).obj B) h' h h (h.trans h') (h.trans h')
      ((F.transition h).map u) = (F.transition (h.trans h')).map u := by
  simp only [trHom]
  rw [← transitionComp_hom_naturality_assoc, Iso.hom_inv_id_app, comp_id]

variable (F) in
/-- The transport isomorphism `j_k(S) ≅ j_m(T_{m/k} S)` of triangles, for stages `k ≤ m`. -/
noncomputable def inclMapTriangleTransIso {k m : ι} (h : k ≤ m) :
    (incl F k).mapTriangle ≅ (F.transition h).mapTriangle ⋙ (incl F m).mapTriangle :=
  Functor.mapTriangleIso (inclTransIso F h) ≪≫ Functor.mapTriangleCompIso _ _

section

variable {k m : ι} (h : k ≤ m) (S : Triangle (F.obj ⟨k⟩))

@[simp]
lemma inclMapTriangleTransIso_hom_app_hom₁ :
    ((inclMapTriangleTransIso F h).hom.app S).hom₁ = (inclTransIso F h).hom.app S.obj₁ := by
  simp [inclMapTriangleTransIso] <;> first | exact comp_id _ | exact id_comp _

@[simp]
lemma inclMapTriangleTransIso_hom_app_hom₂ :
    ((inclMapTriangleTransIso F h).hom.app S).hom₂ = (inclTransIso F h).hom.app S.obj₂ := by
  simp [inclMapTriangleTransIso] <;> first | exact comp_id _ | exact id_comp _

@[simp]
lemma inclMapTriangleTransIso_hom_app_hom₃ :
    ((inclMapTriangleTransIso F h).hom.app S).hom₃ = (inclTransIso F h).hom.app S.obj₃ := by
  simp [inclMapTriangleTransIso] <;> first | exact comp_id _ | exact id_comp _

@[simp]
lemma inclMapTriangleTransIso_inv_app_hom₁ :
    ((inclMapTriangleTransIso F h).inv.app S).hom₁ = (inclTransIso F h).inv.app S.obj₁ := by
  simp [inclMapTriangleTransIso] <;> first | exact comp_id _ | exact id_comp _

@[simp]
lemma inclMapTriangleTransIso_inv_app_hom₂ :
    ((inclMapTriangleTransIso F h).inv.app S).hom₂ = (inclTransIso F h).inv.app S.obj₂ := by
  simp [inclMapTriangleTransIso] <;> first | exact comp_id _ | exact id_comp _

@[simp]
lemma inclMapTriangleTransIso_inv_app_hom₃ :
    ((inclMapTriangleTransIso F h).inv.app S).hom₃ = (inclTransIso F h).inv.app S.obj₃ := by
  simp [inclMapTriangleTransIso] <;> first | exact comp_id _ | exact id_comp _

end

end Transport

variable [∀ i : ι, Preadditive (F.obj ⟨i⟩)] [∀ i : ι, HasZeroObject (F.obj ⟨i⟩)]
  [∀ i : ι, HasShift (F.obj ⟨i⟩) ℤ] [∀ (i : ι) (n : ℤ), (shiftFunctor (F.obj ⟨i⟩) n).Additive]
  [∀ i : ι, Pretriangulated (F.obj ⟨i⟩)]
  [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).Additive]
  [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).CommShift ℤ]
  [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).IsTriangulated] [ShiftCompatible F ℤ]
  [Nonempty ι]

variable (F) in
/-- Blueprint `def-weil-pbc-common-stage-cones`: a triangle of the pair category is
distinguished if it is isomorphic to the image under a stage inclusion `j_k` of a
distinguished triangle of the stage `k`. -/
def distTriangles : Set (Triangle (PairCategory F)) :=
  fun T ↦ ∃ (k : ι) (S : Triangle (F.obj ⟨k⟩)) (_ : S ∈ distTriang (F.obj ⟨k⟩)),
    Nonempty (T ≅ (incl F k).mapTriangle.obj S)

lemma incl_mapTriangle_mem_distTriangles {k : ι} (S : Triangle (F.obj ⟨k⟩))
    (hS : S ∈ distTriang (F.obj ⟨k⟩)) : (incl F k).mapTriangle.obj S ∈ distTriangles F :=
  ⟨k, S, hS, ⟨Iso.refl _⟩⟩

lemma mem_distTriangles_of_iso {T T' : Triangle (PairCategory F)} (e : T ≅ T')
    (hT' : T' ∈ distTriangles F) : T ∈ distTriangles F := by
  obtain ⟨k, S, hS, ⟨e'⟩⟩ := hT'
  exact ⟨k, S, hS, ⟨e ≪≫ e'⟩⟩

/-- A distinguished triangle of the pair category is the image of a distinguished triangle of
any large enough stage. -/
lemma exists_iso_of_mem_distTriangles {T : Triangle (PairCategory F)}
    (hT : T ∈ distTriangles F) (m₀ : ι) :
    ∃ (m : ι) (_ : m₀ ≤ m) (S : Triangle (F.obj ⟨m⟩)) (_ : S ∈ distTriang (F.obj ⟨m⟩)),
      Nonempty (T ≅ (incl F m).mapTriangle.obj S) := by
  obtain ⟨k, S, hS, ⟨e⟩⟩ := hT
  obtain ⟨m, hm₀, hk⟩ := directed_of (· ≤ ·) m₀ k
  exact ⟨m, hm₀, (F.transition hk).mapTriangle.obj S,
    (F.transition hk).map_distinguished S hS, ⟨e ≪≫ (inclMapTriangleTransIso F hk).app S⟩⟩

lemma contractible_mem_distTriangles (X : PairCategory F) :
    contractibleTriangle X ∈ distTriangles F := by
  refine ⟨X.idx, contractibleTriangle X.obj, contractible_distinguished _, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((isZero_zero _).iso (isZero_of_isZero (X := (incl F X.idx).obj 0) (isZero_zero _)))
    ?_ ?_ ?_
  · change 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ (incl F X.idx).map (𝟙 X.obj)
    rw [Functor.map_id]
    rfl
  · exact (isZero_of_isZero (X := (incl F X.idx).obj 0) (isZero_zero _)).eq_of_tgt _ _
  · exact (isZero_zero _).eq_of_src _ _

lemma exists_cocone_mem_distTriangles {X Y : PairCategory F} (f : X ⟶ Y) :
    ∃ (Z : PairCategory F) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriangles F := by
  obtain ⟨k, hX, hY, u, rfl⟩ := exists_rep f
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle u
  refine ⟨(incl F k).obj Z, (isoToStage Y hY).hom ≫ (incl F k).map g,
    (incl F k).map h ≫ ((incl F k).commShiftIso (1 : ℤ)).hom.app _ ≫
      (isoToStage X hX).inv⟦(1 : ℤ)⟧', ⟨k, _, hT, ⟨?_⟩⟩⟩
  refine Triangle.isoMk _ _ (isoToStage X hX) (isoToStage Y hY) (Iso.refl _) ?_ ?_ ?_
  · simp [homMk_eq]
    rfl
  · simp
    rfl
  · simp [← Functor.map_comp]
    rfl

lemma rotate_mem_distTriangles {T : Triangle (PairCategory F)} (hT : T ∈ distTriangles F) :
    T.rotate ∈ distTriangles F := by
  obtain ⟨k, S, hS, ⟨e⟩⟩ := hT
  exact ⟨k, S.rotate, rot_of_distTriang _ hS,
    ⟨(rotate _).mapIso e ≪≫ ((incl F k).mapTriangleRotateIso).app S⟩⟩

lemma invRotate_mem_distTriangles {T : Triangle (PairCategory F)} (hT : T ∈ distTriangles F) :
    T.invRotate ∈ distTriangles F := by
  obtain ⟨k, S, hS, ⟨e⟩⟩ := hT
  exact ⟨k, S.invRotate, inv_rot_of_distTriang _ hS,
    ⟨(invRotate _).mapIso e ≪≫ ((incl F k).mapTriangleInvRotateIso).app S⟩⟩

/-- The morphism axiom TR3 is invariant under isomorphisms of triangles. -/
lemma complete_morphism_of_iso {T₁ T₂ T₁' T₂' : Triangle (PairCategory F)} (e₁ : T₁ ≅ T₁')
    (e₂ : T₂ ≅ T₂')
    (H : ∀ (a : T₁'.obj₁ ⟶ T₂'.obj₁) (b : T₁'.obj₂ ⟶ T₂'.obj₂),
      T₁'.mor₁ ≫ b = a ≫ T₂'.mor₁ → ∃ c, T₁'.mor₂ ≫ c = b ≫ T₂'.mor₂ ∧
        T₁'.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂'.mor₃)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (hcomm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨c, hc₂, hc₃⟩ := H (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁) (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) (by
    simp only [assoc]
    rw [reassoc_of% e₁.inv.comm₁, reassoc_of% hcomm, e₂.hom.comm₁])
  refine ⟨e₁.hom.hom₃ ≫ c ≫ e₂.inv.hom₃, ?_, ?_⟩
  · rw [reassoc_of% e₁.hom.comm₂, reassoc_of% hc₂]
    simp only [assoc, e₂.inv.comm₂, Iso.hom_inv_id_triangle_hom₂_assoc]
  · simp only [assoc]
    rw [← e₂.inv.comm₃, ← reassoc_of% hc₃, ← reassoc_of% e₁.hom.comm₃, ← Functor.map_comp,
      ← Functor.map_comp]
    simp

/-- TR3 for images of distinguished triangles of a stage `k`, for morphisms which are images of
morphisms commuting at a further stage `m`. -/
lemma complete_morphism_incl_of_stage {k m : ι} (h : k ≤ m) {S₁ S₂ : Triangle (F.obj ⟨k⟩)}
    (hS₁ : S₁ ∈ distTriang _) (hS₂ : S₂ ∈ distTriang _)
    (a : (F.transition h).obj S₁.obj₁ ⟶ (F.transition h).obj S₂.obj₁)
    (b : (F.transition h).obj S₁.obj₂ ⟶ (F.transition h).obj S₂.obj₂)
    (hcomm : (F.transition h).map S₁.mor₁ ≫ b = a ≫ (F.transition h).map S₂.mor₁) :
    ∃ c, ((incl F k).mapTriangle.obj S₁).mor₂ ≫ c =
        homMk (X := (incl F k).obj S₁.obj₂) (Y := (incl F k).obj S₂.obj₂) h h b ≫
          ((incl F k).mapTriangle.obj S₂).mor₂ ∧
      ((incl F k).mapTriangle.obj S₁).mor₃ ≫
          (homMk (X := (incl F k).obj S₁.obj₁) (Y := (incl F k).obj S₂.obj₁) h h a)⟦(1 : ℤ)⟧' =
        c ≫ ((incl F k).mapTriangle.obj S₂).mor₃ := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism _ _
    ((F.transition h).map_distinguished _ hS₁) ((F.transition h).map_distinguished _ hS₂) a b
    hcomm
  let ψ : (F.transition h).mapTriangle.obj S₁ ⟶ (F.transition h).mapTriangle.obj S₂ :=
    { hom₁ := a, hom₂ := b, hom₃ := c, comm₁ := hcomm, comm₂ := hc₂, comm₃ := hc₃ }
  let Φ := (inclMapTriangleTransIso F h).hom.app S₁ ≫ (incl F m).mapTriangle.map ψ ≫
    (inclMapTriangleTransIso F h).inv.app S₂
  have e₁ : Φ.hom₁ = homMk (X := (incl F k).obj S₁.obj₁) (Y := (incl F k).obj S₂.obj₁) h h a := by
    simp [Φ, ψ, homMk_incl_eq]
  have e₂ : Φ.hom₂ = homMk (X := (incl F k).obj S₁.obj₂) (Y := (incl F k).obj S₂.obj₂) h h b := by
    simp [Φ, ψ, homMk_incl_eq]
  refine ⟨Φ.hom₃, ?_, ?_⟩
  · rw [← e₂]
    exact Φ.comm₂
  · rw [← e₁]
    exact Φ.comm₃

/-- TR3 for images of distinguished triangles of a common stage. -/
lemma complete_morphism_incl {k : ι} {S₁ S₂ : Triangle (F.obj ⟨k⟩)}
    (hS₁ : S₁ ∈ distTriang _) (hS₂ : S₂ ∈ distTriang _)
    (a : (incl F k).obj S₁.obj₁ ⟶ (incl F k).obj S₂.obj₁)
    (b : (incl F k).obj S₁.obj₂ ⟶ (incl F k).obj S₂.obj₂)
    (hcomm : (incl F k).map S₁.mor₁ ≫ b = a ≫ (incl F k).map S₂.mor₁) :
    ∃ c, ((incl F k).mapTriangle.obj S₁).mor₂ ≫ c = b ≫ ((incl F k).mapTriangle.obj S₂).mor₂ ∧
      ((incl F k).mapTriangle.obj S₁).mor₃ ≫ a⟦(1 : ℤ)⟧' =
        c ≫ ((incl F k).mapTriangle.obj S₂).mor₃ := by
  revert hcomm
  obtain ⟨m₁, -, h₁, h₁', a₁, rfl⟩ := exists_homMk_ge a k
  obtain ⟨m, hm, h₂, h₂', b₁, rfl⟩ := exists_homMk_ge b m₁
  intro hcomm
  rw [← homMk_trHom hm h₁ h₁' (h₁.trans hm) (h₁'.trans hm) a₁] at hcomm ⊢
  generalize trHom hm h₁ h₁' (h₁.trans hm) (h₁'.trans hm) a₁ = a₂ at hcomm ⊢
  rw [incl_map_eq_homMk (i := k) h₂ S₁.mor₁, incl_map_eq_homMk (i := k) h₂' S₂.mor₁,
    homMk_comp_homMk, homMk_comp_homMk,
    homMk_eq_homMk_iff] at hcomm
  obtain ⟨m', hm', e⟩ := hcomm
  rw [trHom_comp (X := (incl F k).obj S₁.obj₁) (Y := (incl F k).obj S₁.obj₂)
      (Z := (incl F k).obj S₂.obj₂) hm' _ _ _ _ ((h₂ : k ≤ m).trans hm'),
    trHom_comp (X := (incl F k).obj S₁.obj₁) (Y := (incl F k).obj S₂.obj₁)
      (Z := (incl F k).obj S₂.obj₂) hm' _ _ _ _ ((h₂ : k ≤ m).trans hm'),
    trHom_transition_map, trHom_transition_map] at e
  rw [← homMk_trHom hm' (h₁.trans hm) (h₁'.trans hm) (h₂.trans hm') (h₂'.trans hm') a₂,
    ← homMk_trHom hm' h₂ h₂' (h₂.trans hm') (h₂'.trans hm') b₁]
  exact complete_morphism_incl_of_stage (h₂.trans hm') hS₁ hS₂ _ _ e

lemma complete_morphism_of_mem_distTriangles {T₁ T₂ : Triangle (PairCategory F)}
    (hT₁ : T₁ ∈ distTriangles F) (hT₂ : T₂ ∈ distTriangles F)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (hcomm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨k₁, S₁, hS₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨k, hk, S₂, hS₂, ⟨e₂⟩⟩ := exists_iso_of_mem_distTriangles hT₂ k₁
  exact complete_morphism_of_iso (e₁ ≪≫ (inclMapTriangleTransIso F hk).app S₁) e₂
    (complete_morphism_incl ((F.transition hk).map_distinguished _ hS₁) hS₂) a b hcomm


/-- Blueprint `def-weil-pbc-common-stage-cones`: the pair category of a directed system of
pretriangulated categories is pretriangulated, the distinguished triangles being the triangles
isomorphic to images of distinguished triangles of a stage. -/
noncomputable instance pretriangulated : Pretriangulated (PairCategory F) where
  distinguishedTriangles := distTriangles F
  isomorphic_distinguished _ hT _ e := mem_distTriangles_of_iso e hT
  contractible_distinguished := contractible_mem_distTriangles
  distinguished_cocone_triangle f := exists_cocone_mem_distTriangles f
  rotate_distinguished_triangle T :=
    ⟨rotate_mem_distTriangles, fun h ↦ mem_distTriangles_of_iso
      ((rotCompInvRot (C := PairCategory F)).app T) (invRotate_mem_distTriangles h)⟩
  complete_distinguished_triangle_morphism _ _ hT₁ hT₂ a b hcomm :=
    complete_morphism_of_mem_distTriangles hT₁ hT₂ a b hcomm

lemma mem_distTriang_iff (T : Triangle (PairCategory F)) :
    T ∈ distTriang (PairCategory F) ↔ ∃ (k : ι) (S : Triangle (F.obj ⟨k⟩))
      (_ : S ∈ distTriang (F.obj ⟨k⟩)), Nonempty (T ≅ (incl F k).mapTriangle.obj S) :=
  Iff.rfl

/-- The stage inclusions are triangulated functors. -/
instance incl_isTriangulated (k : ι) : (incl F k).IsTriangulated where
  map_distinguished S hS := incl_mapTriangle_mem_distTriangles S hS

/-- Blueprint `def-weil-pbc-common-stage-cones`: the common-stage cone triangle of a morphism
`f = [M, u] : (E, K) ⟶ (F, L)`: for a distinguished triangle
`T_{M/E} K ⟶ T_{M/F} L ⟶ C(u) ⟶ (T_{M/E} K)[1]` of the stage `M` extending `u`, the triangle
`(E, K) ⟶ (F, L) ⟶ (M, C(u)) ⟶ (E, K)[1]` of the pair category is distinguished. -/
lemma cone_triangle_distinguished {X Y : PairCategory F} {k : ι} (hX : X.idx ≤ k)
    (hY : Y.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) {C : F.obj ⟨k⟩} (i : Y.at_ hY ⟶ C)
    (p : C ⟶ (X.at_ hX)⟦(1 : ℤ)⟧) (hT : Triangle.mk u i p ∈ distTriang _) :
    Triangle.mk (homMk hX hY u) (homMk (Y := ⟨k, C⟩) hY le_rfl
      (i ≫ (F.transitionId k le_rfl).inv.app C))
      (homMk (X := ⟨k, C⟩) (Y := ⟨X.idx, (shiftFunctor _ (1 : ℤ)).obj X.obj⟩) le_rfl hX
        ((F.transitionId k le_rfl).hom.app C ≫ p ≫
          ((F.transition hX).commShiftIso (1 : ℤ)).inv.app X.obj)) ∈
      distTriang (PairCategory F) := by
  refine ⟨k, _, hT, ⟨Triangle.isoMk _ _ (isoToStage X hX) (isoToStage Y hY) (Iso.refl _)
    ?_ ?_ ?_⟩⟩
  · change _ = _ ≫ (incl F k).map u
    simp [homMk_eq]
  · change _ ≫ 𝟙 _ = (isoToStage Y hY).hom ≫ (incl F k).map i
    simp only [comp_id, isoToStage, incl, homMk_comp_homMk]
    congr 1
    simp
  · change homMk (X := ⟨k, C⟩) (Y := ⟨X.idx, (shiftFunctor _ (1 : ℤ)).obj X.obj⟩) le_rfl hX _ ≫
        (shiftFunctor (PairCategory F) (1 : ℤ)).map (isoToStage X hX).hom =
      𝟙 _ ≫ ((incl F k).map p ≫ 𝟙 _)
    rw [id_comp, comp_id, isoToStage, shiftFunctor_map_homMk, homMk_comp_homMk]
    change _ = homMk _ _ _
    congr 1
    simp only [assoc, Iso.inv_hom_id_app_assoc, transitionId_inv_shift]

/-- Every distinguished triangle of the pair category is isomorphic to a common-stage cone
triangle. -/
lemma exists_iso_cone_triangle {T : Triangle (PairCategory F)} (hT : T ∈ distTriang _) :
    ∃ (k : ι) (S : Triangle (F.obj ⟨k⟩)) (_ : S ∈ distTriang _),
      Nonempty (T ≅ (incl F k).mapTriangle.obj S) :=
  hT

/-- Two composable morphisms of the pair category are represented at a common stage. -/
lemma exists_homMk_comp {X₁ X₂ X₃ : PairCategory F} (u₁₂ : X₁ ⟶ X₂) (u₂₃ : X₂ ⟶ X₃) :
    ∃ (k : ι) (h₁ : X₁.idx ≤ k) (h₂ : X₂.idx ≤ k) (h₃ : X₃.idx ≤ k) (f : X₁.at_ h₁ ⟶ X₂.at_ h₂)
      (g : X₂.at_ h₂ ⟶ X₃.at_ h₃), u₁₂ = homMk h₁ h₂ f ∧ u₂₃ = homMk h₂ h₃ g := by
  obtain ⟨k₁, -, h₁, h₂, f, rfl⟩ := exists_homMk_ge u₁₂ X₁.idx
  obtain ⟨k, hk, h₂', h₃, g, rfl⟩ := exists_homMk_ge u₂₃ k₁
  exact ⟨k, h₁.trans hk, h₂', h₃, _, g, (homMk_trHom hk h₁ h₂ _ h₂' f).symm, rfl⟩

section Octahedron

variable [∀ i : ι, IsTriangulated (F.obj ⟨i⟩)]

open Triangulated in
/-- The pair category of a directed system of triangulated categories is triangulated. -/
instance isTriangulated : IsTriangulated (PairCategory F) := by
  apply IsTriangulated.mk
  intro X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ hcomm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
  obtain ⟨k, h₁, h₂, h₃, f, g, rfl, rfl⟩ := exists_homMk_comp u₁₂ u₂₃
  subst hcomm
  obtain ⟨_, _, _, h₁₂'⟩ := distinguished_cocone_triangle f
  obtain ⟨_, _, _, h₂₃'⟩ := distinguished_cocone_triangle g
  obtain ⟨_, _, _, h₁₃'⟩ := distinguished_cocone_triangle (f ≫ g)
  exact ⟨Octahedron.ofIso (e₁ := isoToStage X₁ h₁) (e₂ := isoToStage X₂ h₂)
    (e₃ := isoToStage X₃ h₃) (comm₁₂ := by simp [homMk_eq]) (comm₂₃ := by simp [homMk_eq])
    (H := (someOctahedron rfl h₁₂' h₂₃' h₁₃').map (incl F k)) ..⟩

end Octahedron

end CategoryTheory.PairCategory
