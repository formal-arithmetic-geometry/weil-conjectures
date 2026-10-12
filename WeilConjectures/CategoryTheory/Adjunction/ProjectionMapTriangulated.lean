/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit
public import WeilConjectures.CategoryTheory.Triangulated.IsoLocus

/-!
# The objects at which a projection map is an isomorphism

Let `adj : F ⊣ G` be an adjunction with `F : D ⥤ C`, and let
`π : G M ⊗ L ⟶ G (M ⊗ F L)` be the right adjoint projection map attached to a comparison
`φ : F (a ⊗ b) ⟶ F a ⊗ F b` (`CategoryTheory.Adjunction.rightAdjointProjectionMap`). We study,
for a fixed `M`, the objects `L` at which `π` is an isomorphism.

* If `L` is a retract of an object `Y` at which `π` is an isomorphism, so is `π` at `L`, with
  the explicit inverse `G (M ⊗ F L) ⟶ G (M ⊗ F Y) ⟶ G M ⊗ Y ⟶ G M ⊗ L`
  (`CategoryTheory.Adjunction.rightAdjointProjectionMapInvOfRetract`), which therefore does not
  depend on the retraction. This is blueprint `lemma-weil-pbc-projection-formula-projective-summand`.
* If `C` and `D` are pretriangulated, `F`, `G`, the adjunction, the tensor products and `φ`
  commute with the shifts and all functors are triangulated, these objects form a thick
  triangulated subcategory (`CategoryTheory.Adjunction.isTriangulated_isoLocus_projectionMap`).
* If moreover `F` is oplax monoidal with comonoidal structure `φ` and invertible unit comparison,
  the unit lies in it, hence so do the finite sums of shifted copies of the unit
  (`CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_shift_biproduct_unit`),
  blueprint `lemma-weil-pbc-projection-formula-finite-free`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category Limits MonoidalCategory Pretriangulated _root_.CategoryTheory.Functor

section Retract

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

/-- The right adjoint projection map `G M ⊗ L ⟶ G (M ⊗ F L)` for a fixed `M`, as a natural
transformation between the functors `L ↦ G M ⊗ L` and `L ↦ G (M ⊗ F L)`. -/
def rightAdjointProjectionMapApp (M : C) : T_D.obj (G.obj M) ⟶ (F ⋙ T_C.obj M) ⋙ G :=
  (adj.rightAdjointProjectionMap φ).app M

@[simp]
lemma rightAdjointProjectionMapApp_app (M : C) (L : D) :
    (adj.rightAdjointProjectionMapApp φ M).app L =
      ((adj.rightAdjointProjectionMap φ).app M).app L :=
  rfl

@[reassoc]
lemma rightAdjointProjectionMap_naturality (M : C) {L L' : D} (f : L ⟶ L') :
    (T_D.obj (G.obj M)).map f ≫ ((adj.rightAdjointProjectionMap φ).app M).app L' =
      ((adj.rightAdjointProjectionMap φ).app M).app L ≫ G.map ((T_C.obj M).map (F.map f)) :=
  (adj.rightAdjointProjectionMapApp φ M).naturality f

variable {X Y : D} (h : Retract X Y) (M : C)
  [IsIso (((adj.rightAdjointProjectionMap φ).app M).app Y)]

/-- Let `h` exhibit `X` as a retract of `Y`, with `i : X ⟶ Y` and `r : Y ⟶ X`, and suppose
that the projection map `π_Y : G M ⊗ Y ⟶ G (M ⊗ F Y)` is an isomorphism. The composite
```
G (M ⊗ F X) --G (M ⊗ F i)--> G (M ⊗ F Y) --π_Y⁻¹--> G M ⊗ Y --G M ⊗ r--> G M ⊗ X
```
is the inverse of the projection map at `X` (blueprint `def-weil-pbc-projection-formula-arrows`,
the arrow `ρ_{F^r}`; see `CategoryTheory.Adjunction.rightAdjointProjectionMapInvOfRetract_eq`). -/
noncomputable def rightAdjointProjectionMapInvOfRetract :
    G.obj ((T_C.obj M).obj (F.obj X)) ⟶ (T_D.obj (G.obj M)).obj X :=
  G.map ((T_C.obj M).map (F.map h.i)) ≫ inv (((adj.rightAdjointProjectionMap φ).app M).app Y) ≫
    (T_D.obj (G.obj M)).map h.r

@[reassoc (attr := simp)]
lemma rightAdjointProjectionMap_comp_invOfRetract :
    ((adj.rightAdjointProjectionMap φ).app M).app X ≫
        adj.rightAdjointProjectionMapInvOfRetract φ h M = 𝟙 _ := by
  rw [rightAdjointProjectionMapInvOfRetract, ← rightAdjointProjectionMap_naturality_assoc,
    IsIso.hom_inv_id_assoc, ← Functor.map_comp, h.retract, Functor.map_id]
  rfl

@[reassoc (attr := simp)]
lemma rightAdjointProjectionMapInvOfRetract_comp :
    adj.rightAdjointProjectionMapInvOfRetract φ h M ≫
        ((adj.rightAdjointProjectionMap φ).app M).app X = 𝟙 _ := by
  rw [rightAdjointProjectionMapInvOfRetract, assoc, assoc,
    rightAdjointProjectionMap_naturality, IsIso.inv_hom_id_assoc, ← G.map_comp,
    ← Functor.map_comp, ← F.map_comp, h.retract, F.map_id, Functor.map_id, G.map_id]

include h in
/-- The projection map is an isomorphism at a retract of an object at which it is one. This is
the first half of blueprint `lemma-weil-pbc-projection-formula-projective-summand`. -/
lemma isIso_rightAdjointProjectionMap_app_app_of_retract :
    IsIso (((adj.rightAdjointProjectionMap φ).app M).app X) :=
  ⟨⟨_, adj.rightAdjointProjectionMap_comp_invOfRetract φ h M,
    adj.rightAdjointProjectionMapInvOfRetract_comp φ h M⟩⟩

/-- **Finite-projective summand equations** (blueprint
`lemma-weil-pbc-projection-formula-projective-summand`). For a retract `X` of `Y` at which the
projection map is an isomorphism, the explicit arrow
`CategoryTheory.Adjunction.rightAdjointProjectionMapInvOfRetract` is the inverse of the
projection map at `X`. In particular it does not depend on the chosen retraction. -/
lemma rightAdjointProjectionMapInvOfRetract_eq :
    haveI := adj.isIso_rightAdjointProjectionMap_app_app_of_retract φ h M
    adj.rightAdjointProjectionMapInvOfRetract φ h M =
      inv (((adj.rightAdjointProjectionMap φ).app M).app X) := by
  have := adj.isIso_rightAdjointProjectionMap_app_app_of_retract φ h M
  rw [← cancel_epi (((adj.rightAdjointProjectionMap φ).app M).app X),
    rightAdjointProjectionMap_comp_invOfRetract, IsIso.hom_inv_id]

/-- The arrows `rightAdjointProjectionMapInvOfRetract` built from two presentations of `X` as a
retract agree. -/
lemma rightAdjointProjectionMapInvOfRetract_eq_of_retract {Y' : D} (h' : Retract X Y')
    [IsIso (((adj.rightAdjointProjectionMap φ).app M).app Y')] :
    adj.rightAdjointProjectionMapInvOfRetract φ h M =
      adj.rightAdjointProjectionMapInvOfRetract φ h' M := by
  have := adj.isIso_rightAdjointProjectionMap_app_app_of_retract φ h M
  rw [← cancel_epi (((adj.rightAdjointProjectionMap φ).app M).app X),
    rightAdjointProjectionMap_comp_invOfRetract, rightAdjointProjectionMap_comp_invOfRetract]

end Retract

section Triangulated

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated]
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
  [∀ M : C, ((curriedTensor C).obj M).CommShift ℤ]
  [∀ M : C, ((curriedTensor C).obj M).IsTriangulated]
  [∀ L : D, ((curriedTensor D).obj L).CommShift ℤ]
  [∀ L : D, ((curriedTensor D).obj L).IsTriangulated]
  [∀ {M M' : C} (f : M ⟶ M'), NatTrans.CommShift ((curriedTensor C).map f) ℤ]
  [∀ K : D, NatTrans.CommShift (F₁ := (curriedTensor D).obj K ⋙ F)
    (F₂ := F ⋙ (curriedTensor C).obj (F.obj K)) (φ.app K) ℤ]

instance commShift_rightAdjointProjectionMapApp (M : C) :
    NatTrans.CommShift (adj.rightAdjointProjectionMapApp φ M) ℤ :=
  adj.commShift_rightAdjointProjectionMap_app φ M

/-- The objects `L` at which the projection map `G M ⊗ L ⟶ G (M ⊗ F L)` is an isomorphism form a
triangulated subcategory, for a fixed `M`. It is also closed under isomorphisms and stable under
retracts, hence a thick triangulated subcategory. -/
instance isTriangulated_isoLocus_projectionMap (M : C) :
    (NatTrans.isoLocus (adj.rightAdjointProjectionMapApp φ M)).IsTriangulated :=
  NatTrans.isTriangulated_isoLocus _

variable [F.OplaxMonoidal] [IsIso (Functor.OplaxMonoidal.η F)]
  (hφ : ∀ X Y, (φ.app X).app Y = Functor.OplaxMonoidal.δ F X Y)
include hφ

/-- **Finite-free projection formula** (blueprint
`lemma-weil-pbc-projection-formula-finite-free`). The projection map
`G M ⊗ (⨁ 𝟙)⟦a⟧ ⟶ G (M ⊗ F ((⨁ 𝟙)⟦a⟧))` at a shifted finite sum of copies of the unit is an
isomorphism. -/
lemma isIso_rightAdjointProjectionMap_app_app_shift_biproduct_unit [HasFiniteBiproducts D]
    (M : C) (N : ℕ) (a : ℤ) :
    IsIso (((adj.rightAdjointProjectionMap φ).app M).app
      ((⨁ fun _ : Fin N ↦ 𝟙_ D)⟦a⟧)) := by
  let P := NatTrans.isoLocus (adj.rightAdjointProjectionMapApp φ M)
  have h : P (⨁ fun _ : Fin N ↦ 𝟙_ D) :=
    P.prop_of_isLimit_fan (biproduct.isLimit _)
      fun _ ↦ adj.isIso_rightAdjointProjectionMap_app_app_tensorUnit φ hφ M
  exact P.le_shift a _ h

end Triangulated

end CategoryTheory.Adjunction
