/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# The mate of an inverse projection map at a dualizable object

Let `L ⊣ R` be an adjunction with `L : 𝒳 ⥤ 𝒴` (think `f_! ⊣ f^!`), let `F : 𝒴 ⥤ 𝒳` be a monoidal
functor (think `f^*`) and let `π A B : L A ⊗ B ⟶ L (A ⊗ F B)` be a projection map compatible with
the unit and the tensor structure of `F` (the axioms of a module functor). Unlike
`CategoryTheory.Adjunction.isIso_tensorMapOfProjection`, the projection map is only assumed to be
invertible at a fixed object `K` and at a left dual `K'` of `K`.

For `a : L (A ⊗ K_X) ⟶ L A ⊗ K` given by `π⁻¹` and an isomorphism `F K ≅ K_X`, the mate
`R N ⊗ K_X ⟶ R (N ⊗ K)` of `a` along `L ⊣ R` is an isomorphism: up to `F K ≅ K_X` it is the
conjugate of the projection map at `K'`, for the adjunctions
`L ⋙ (- ⊗ K') ⊣ (- ⊗ K) ⋙ R` and `(- ⊗ F K') ⋙ L ⊣ R ⋙ (- ⊗ F K)`.

## Main results

- `CategoryTheory.Adjunction.mateEquiv_app_eq_conjugateEquiv_projection`: the identification of
  the mate with a conjugate.
- `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_projection`,
  `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_projection'`: the mate is an isomorphism
  (with the axioms of the projection map stated in terms of the monoidal, resp. comonoidal,
  structure of `F`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {𝒳 𝒴 : Type*} [Category* 𝒳] [Category* 𝒴] [MonoidalCategory 𝒳] [MonoidalCategory 𝒴]
  {F : 𝒴 ⥤ 𝒳} {L : 𝒳 ⥤ 𝒴} {R : 𝒴 ⥤ 𝒳} (adj : L ⊣ R)
  (π : ∀ (A : 𝒳) (B : 𝒴), L.obj A ⊗ B ⟶ L.obj (A ⊗ F.obj B))
  (hπ : ∀ {A A' : 𝒳} (φ : A ⟶ A') (B : 𝒴), L.map φ ▷ B ≫ π A' B = π A B ≫ L.map (φ ▷ F.obj B))

/-- The projection map `L A ⊗ B ⟶ L (A ⊗ F B)` at a fixed object `B`, as a natural
transformation `L ⋙ (- ⊗ B) ⟶ (- ⊗ F B) ⋙ L`. -/
@[simps]
def projectionNatTrans (B : 𝒴) : L ⋙ tensorRight B ⟶ tensorRight (F.obj B) ⋙ L where
  app A := π A B
  naturality _ _ φ := hπ φ B

variable {π}

lemma isIso_projectionNatTrans (B : 𝒴) [∀ A, IsIso (π A B)] :
    IsIso (projectionNatTrans π hπ B) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun A ↦ inferInstanceAs (IsIso (π A B))

/-- **The mate of the inverse projection map is a conjugate.** Let `K'` be a left dual of `K`,
and `a : (- ⊗ F K) ⋙ L ⟶ L ⋙ (- ⊗ K)` be the inverse of the projection map at `K`. If the
projection map is compatible with the unit and the tensor structure of `F`, the mate
`R N ⊗ F K ⟶ R (N ⊗ K)` of `a` along `L ⊣ R` is the conjugate of the projection map at `K'`. -/
lemma mateEquiv_app_eq_conjugateEquiv_projection [F.Monoidal]
    (hπr : ∀ (A : 𝒳) {B B' : 𝒴} (φ : B ⟶ B'),
      L.obj A ◁ φ ≫ π A B' = π A B ≫ L.map (A ◁ F.map φ))
    (hunit : ∀ A, π A (𝟙_ 𝒴) = (ρ_ (L.obj A)).hom ≫ L.map ((ρ_ A).inv ≫ A ◁ ε F))
    (hassoc : ∀ A B C, π A (B ⊗ C) = (α_ _ _ _).inv ≫ (π A B ▷ C) ≫
      π (A ⊗ F.obj B) C ≫ L.map ((α_ _ _ _).hom ≫ A ◁ μ F B C))
    (K' K : 𝒴) [ExactPairing K' K] [∀ A, IsIso (π A K)]
    (a : tensorRight (F.obj K) ⋙ L ⟶ L ⋙ tensorRight K) (ha : ∀ A, a.app A = inv (π A K))
    (N : 𝒴) :
    letI := ExactPairing.map F K' K
    (mateEquiv adj adj a).app N =
      (conjugateEquiv ((tensorRightAdjunction (F.obj K') (F.obj K)).comp adj)
        (adj.comp (tensorRightAdjunction K' K)) (projectionNatTrans π hπ K')).app N := by
  let := ExactPairing.map F K' K
  apply ((adj.comp (tensorRightAdjunction K' K)).homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit, conjugateEquiv_counit]
  have hev : ε_ (F.obj K') (F.obj K) = μ F K K' ≫ F.map (ε_ K' K) ≫ η F := rfl
  have h₁ : L.map ((mateEquiv adj adj a).app N) ≫ adj.counit.app (N ⊗ K) =
      inv (π (R.obj N) K) ≫ adj.counit.app N ▷ K := by
    have h := mateEquiv_counit adj adj a N
    dsimp at h
    rw [h, ha]
  have h₂ : π (R.obj N ⊗ F.obj K) K' ≫ L.map ((α_ _ _ _).hom ≫ R.obj N ◁ μ F K K') =
      inv (π (R.obj N) K) ▷ K' ≫ (α_ _ _ _).hom ≫ π (R.obj N) (K ⊗ K') := by
    rw [hassoc]
    simp
  have h₃ := (hπr (R.obj N) (ε_ K' K)).symm
  have h₄ : π (R.obj N) (𝟙_ 𝒴) ≫ L.map (R.obj N ◁ η F ≫ (ρ_ _).hom) = (ρ_ _).hom := by
    rw [hunit, Category.assoc, ← L.map_comp]
    simp
  dsimp
  simp only [comp_counit_app, projectionNatTrans_app, Functor.flip_obj_map, curriedTensor_map_app,
    Functor.flip_obj_obj, curriedTensor_obj_obj, tensorRightAdjunction_counit_app, hev,
    MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc]
  rw [← comp_whiskerRight_assoc, h₁, ← L.map_comp_assoc, reassoc_of% h₂, reassoc_of% h₃,
    ← L.map_comp_assoc, reassoc_of% h₄, comp_whiskerRight_assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]

/-- **The mate of the inverse projection map is an isomorphism at a dualizable object.** Let
`K'` be a left dual of `K` such that the projection map `π` is invertible at `K` and `K'`, and let
`a : L (A ⊗ K_X) ⟶ L A ⊗ K` be `L (A ◁ c⁻¹)` followed by `π⁻¹` for an isomorphism
`c : F K ≅ K_X`. If `π` is compatible with the unit and the tensor structure of `F`, the mate
`R N ⊗ K_X ⟶ R (N ⊗ K)` of `a` along `L ⊣ R` is an isomorphism. -/
theorem isIso_mateEquiv_app_of_projection [F.Monoidal]
    (hπ : ∀ {A A' : 𝒳} (φ : A ⟶ A') (B : 𝒴),
      L.map φ ▷ B ≫ π A' B = π A B ≫ L.map (φ ▷ F.obj B))
    (hπr : ∀ (A : 𝒳) {B B' : 𝒴} (φ : B ⟶ B'),
      L.obj A ◁ φ ≫ π A B' = π A B ≫ L.map (A ◁ F.map φ))
    (hunit : ∀ A, π A (𝟙_ 𝒴) = (ρ_ (L.obj A)).hom ≫ L.map ((ρ_ A).inv ≫ A ◁ ε F))
    (hassoc : ∀ A B C, π A (B ⊗ C) = (α_ _ _ _).inv ≫ (π A B ▷ C) ≫
      π (A ⊗ F.obj B) C ≫ L.map ((α_ _ _ _).hom ≫ A ◁ μ F B C))
    (K' K : 𝒴) [ExactPairing K' K] [∀ A, IsIso (π A K)] [∀ A, IsIso (π A K')] {KX : 𝒳}
    (c : F.obj K ≅ KX) (a : tensorRight KX ⋙ L ⟶ L ⋙ tensorRight K)
    (ha : ∀ A, a.app A = L.map (A ◁ c.inv) ≫ inv (π A K)) (N : 𝒴) :
    IsIso ((mateEquiv adj adj a).app N) := by
  let := ExactPairing.map F K' K
  let a₀ : tensorRight (F.obj K) ⋙ L ⟶ L ⋙ tensorRight K :=
    { app A := inv (π A K)
      naturality A A' φ := by
        have h := hπ φ K
        rw [← cancel_epi (inv (π _ K)), ← cancel_mono (inv (π _ K))] at h
        simp only [IsIso.inv_hom_id_assoc, Category.assoc, IsIso.hom_inv_id,
          Category.comp_id] at h
        exact h.symm }
  have e := mateEquiv_app_eq_conjugateEquiv_projection adj hπ hπr hunit hassoc K' K a₀
    (fun _ ↦ rfl) N
  have := isIso_projectionNatTrans hπ K'
  have : IsIso ((mateEquiv adj adj a₀).app N) := by
    rw [e]
    infer_instance
  have e' : (mateEquiv adj adj a).app N = R.obj N ◁ c.inv ≫ (mateEquiv adj adj a₀).app N := by
    apply (adj.homEquiv _ _).symm.injective
    simp only [homEquiv_counit, Functor.map_comp, Category.assoc, mateEquiv_counit, ha]
    dsimp [a₀]
  rw [e']
  infer_instance

/-- The unit axiom of a projection map, in the form `π A 𝟙 ≫ L (A ◁ η ≫ ρ) = ρ` involving the
comonoidal unit `η : F 𝟙 ⟶ 𝟙`, implies the form used in
`CategoryTheory.Adjunction.isIso_mateEquiv_app_of_projection`. -/
lemma projection_unit_of_comp_map [F.Monoidal]
    (hunit : ∀ A, π A (𝟙_ 𝒴) ≫ L.map (A ◁ Functor.OplaxMonoidal.η F ≫ (ρ_ A).hom) =
      (ρ_ (L.obj A)).hom) (A : 𝒳) :
    π A (𝟙_ 𝒴) = (ρ_ (L.obj A)).hom ≫ L.map ((ρ_ A).inv ≫ A ◁ ε F) := by
  rw [← cancel_mono (L.map (A ◁ Functor.OplaxMonoidal.η F ≫ (ρ_ A).hom)), hunit,
    Category.assoc, ← L.map_comp]
  simp

/-- The associativity axiom of a projection map, in the form
`π A B ▷ C ≫ π (A ⊗ F B) C ≫ L α = α ≫ π A (B ⊗ C) ≫ L (A ◁ δ)` involving the comonoidal structure
`δ` of `F`, implies the form used in
`CategoryTheory.Adjunction.isIso_mateEquiv_app_of_projection`. -/
lemma projection_tensor_of_comp_map [F.Monoidal]
    (hassoc : ∀ A B C, π A B ▷ C ≫ π (A ⊗ F.obj B) C ≫ L.map (α_ _ _ _).hom =
      (α_ _ _ _).hom ≫ π A (B ⊗ C) ≫ L.map (A ◁ Functor.OplaxMonoidal.δ F B C)) (A : 𝒳)
    (B C : 𝒴) :
    π A (B ⊗ C) = (α_ _ _ _).inv ≫ (π A B ▷ C) ≫
      π (A ⊗ F.obj B) C ≫ L.map ((α_ _ _ _).hom ≫ A ◁ μ F B C) := by
  rw [L.map_comp, reassoc_of% (hassoc A B C), Iso.inv_hom_id_assoc, ← L.map_comp,
    ← MonoidalCategory.whiskerLeft_comp, Functor.Monoidal.δ_μ, MonoidalCategory.whiskerLeft_id,
    L.map_id, Category.comp_id]

/-- **The mate of the inverse projection map is an isomorphism at a dualizable object**, with the
unit and tensor axioms of the projection map stated in terms of the comonoidal structure of `F`
(see `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_projection`). -/
theorem isIso_mateEquiv_app_of_projection' [F.Monoidal]
    (hπ : ∀ {A A' : 𝒳} (φ : A ⟶ A') (B : 𝒴),
      L.map φ ▷ B ≫ π A' B = π A B ≫ L.map (φ ▷ F.obj B))
    (hπr : ∀ (A : 𝒳) {B B' : 𝒴} (φ : B ⟶ B'),
      L.obj A ◁ φ ≫ π A B' = π A B ≫ L.map (A ◁ F.map φ))
    (hunit : ∀ A, π A (𝟙_ 𝒴) ≫ L.map (A ◁ Functor.OplaxMonoidal.η F ≫ (ρ_ A).hom) =
      (ρ_ (L.obj A)).hom)
    (hassoc : ∀ A B C, π A B ▷ C ≫ π (A ⊗ F.obj B) C ≫ L.map (α_ _ _ _).hom =
      (α_ _ _ _).hom ≫ π A (B ⊗ C) ≫ L.map (A ◁ Functor.OplaxMonoidal.δ F B C))
    (K' K : 𝒴) [ExactPairing K' K] [∀ A, IsIso (π A K)] [∀ A, IsIso (π A K')] {KX : 𝒳}
    (c : F.obj K ≅ KX) (a : tensorRight KX ⋙ L ⟶ L ⋙ tensorRight K)
    (ha : ∀ A, a.app A = L.map (A ◁ c.inv) ≫ inv (π A K)) (N : 𝒴) :
    IsIso ((mateEquiv adj adj a).app N) :=
  isIso_mateEquiv_app_of_projection adj hπ hπr (projection_unit_of_comp_map hunit)
    (projection_tensor_of_comp_map hassoc) K' K c a ha N

end CategoryTheory.Adjunction
