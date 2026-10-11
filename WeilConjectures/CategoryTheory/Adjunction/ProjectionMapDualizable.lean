/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# The projection map at a dualizable object

Let `adj : F ⊣ G` be an adjunction between monoidal categories, with `F : D ⥤ C` a monoidal
functor. The right adjoint projection map `G M ⊗ L ⟶ G (M ⊗ F L)` built from the comonoidal
structure `δ` of `F` (`CategoryTheory.Adjunction.rightAdjointProjectionMap`) is an isomorphism
as soon as `L` is dualizable. This is formal: if `Z` is a left dual of `L`, both sides are right
adjoints of `T ↦ F (T ⊗ Z) ≅ F T ⊗ F Z`, and the projection map is the conjugate of the monoidal
structure `μ` of `F`.

## Main statements

- `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_of_exactPairing`: the
  projection map is an isomorphism at `L` if `L` has a left dual.
- `CategoryTheory.Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isDualizable`: in a
  braided category, the projection map is an isomorphism at a dualizable `L`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))

/-- The monoidal structure `F T ⊗ F Z ⟶ F (T ⊗ Z)` of `F`, as a natural transformation in `T`. -/
@[simps]
def μTensorRight (Z : D) : F ⋙ tensorRight (F.obj Z) ⟶ tensorRight Z ⋙ F where
  app T := μ F T Z
  naturality _ _ f := by simp [μ_natural_left]

instance (Z : D) : IsIso (μTensorRight (F := F) Z) :=
  have (T : D) : IsIso ((μTensorRight (F := F) Z).app T) :=
    (Functor.Monoidal.μIso F T Z).isIso_hom
  NatIso.isIso_of_isIso_app _

/-- **The projection map at an object with a left dual.** Let `adj : F ⊣ G` be an adjunction
with `F` monoidal, and let `φ` be the comonoidal structure `δ` of `F`. If `L` has a left dual
`Z`, the projection map `G M ⊗ L ⟶ G (M ⊗ F L)` is an isomorphism. -/
theorem isIso_rightAdjointProjectionMap_app_app_of_exactPairing
    (hφ : ∀ a b, (φ.app a).app b = δ F a b) (M : C) (Z L : D) [ExactPairing Z L] :
    IsIso (((adj.rightAdjointProjectionMap φ).app M).app L) := by
  let := ExactPairing.map F Z L
  let adj₁ := (tensorRightAdjunction Z L).comp adj
  let adj₂ := adj.comp (tensorRightAdjunction (F.obj Z) (F.obj L))
  suffices h : ((adj.rightAdjointProjectionMap φ).app M).app L =
      (conjugateEquiv adj₁ adj₂ (μTensorRight Z)).app M by
    rw [h]
    infer_instance
  apply (adj₂.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit]
  refine Eq.trans ?_ (conjugateEquiv_counit adj₁ adj₂ (μTensorRight Z) M).symm
  have h := adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M L
  rw [hφ] at h
  simp only [adj₁, adj₂, comp_counit_app, tensorRightAdjunction_counit_app] at h ⊢
  dsimp at h ⊢
  rw [← comp_whiskerRight_assoc, h]
  have hε : ε_ (F.obj Z) (F.obj L) = μ F L Z ≫ F.map (ε_ Z L) ≫ η F := rfl
  rw [hε]
  rw [comp_whiskerRight, Category.assoc, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]
  simp only [← Category.assoc]
  congr 1
  simp only [Functor.map_comp, Functor.Monoidal.map_associator, Functor.Monoidal.map_whiskerLeft,
    Functor.Monoidal.map_rightUnitor, Category.assoc, Functor.Monoidal.μ_δ_assoc,
    MonoidalCategory.whiskerLeft_comp, μTensorRight_app]

/-- **The projection map at a dualizable object.** Let `adj : F ⊣ G` be an adjunction with `F`
monoidal, and let `φ` be the comonoidal structure `δ` of `F`. If `D` is braided and `L` is
dualizable, the projection map `G M ⊗ L ⟶ G (M ⊗ F L)` is an isomorphism. -/
theorem isIso_rightAdjointProjectionMap_app_app_of_isDualizable [BraidedCategory D]
    (hφ : ∀ a b, (φ.app a).app b = δ F a b) (M : C) {L : D} (hL : IsDualizable L) :
    IsIso (((adj.rightAdjointProjectionMap φ).app M).app L) := by
  obtain ⟨_⟩ := hL
  let := BraidedCategory.exactPairing_swap L Lᘁ
  exact adj.isIso_rightAdjointProjectionMap_app_app_of_exactPairing φ hφ M Lᘁ L

end CategoryTheory.Adjunction
