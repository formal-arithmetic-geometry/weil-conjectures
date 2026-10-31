/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-!
# The exceptional inverse image reflects isomorphisms between invertible objects

Let `u : U ⟶ X` be a morphism admitting a compactification and satisfying the projection
formula, and `G` a right adjoint of `Ru_!` (for finite coefficients, `Ru^!`). If `G` sends some
invertible object `T` to an invertible object (for instance `T = Λ_X(c)[2c]` for a closed section
`u` of a smooth morphism of relative dimension `c`, by purity), then `G` reflects isomorphisms
between invertible objects to the derived pullback `Lu^*`
(`isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map_of_isInvertible`):
through the tensor maps `G M ⊗ Lu^* N ≅ G(M ⊗ N)` at invertible `N`, both `G φ ▷ Lu^* T` and
`G T ◁ Lu^* φ` are identified with `G` of `φ ▷ T ≅ T ◁ φ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product (see `UpperShriekCanonicalMapsCoherence`).
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- Braid étale sheaves through `Etale.sheafBraidedCategory`, as the generic definitions of the
-- derived tensor product do.
attribute [local instance 20000] Etale.sheafBraidedCategory

variable {U X : Scheme.{u}} {u : U ⟶ X} [HasCompactification u] [IsIso (projectionMap A u)]
  {G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
    _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)}

include FC CC in
/-- **A right adjoint of `Ru_!` reflects isomorphisms between invertible objects to `Lu^*`**, as
soon as it sends some invertible object `T` to an invertible object: for `φ : P ⟶ Q` between
invertible objects, if `G φ` is an isomorphism, so is `Lu^* φ`. -/
theorem isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map_of_isInvertible
    (adj : R(u)_![A] ⊣ G) {T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hT : IsInvertible T)
    (hGT : IsInvertible (G.obj T)) {P Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hP : IsInvertible P) (hQ : IsInvertible Q) (φ : P ⟶ Q) (h : IsIso (G.map φ)) :
    IsIso ((L((u)^*[A])).map φ) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf U.smallEtaleTopology A)
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf X.smallEtaleTopology A)
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible adj P hT
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible adj Q hT
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible adj T hP
  have := isIso_lowerShriekRightAdjointTensorMap_of_isInvertible adj T hQ
  -- `G (φ ▷ T)` is an isomorphism
  have hl := Adjunction.projectionTensorMap_naturality_left adj _
    (projectionMap_app_app_naturality_left u) φ T
  have h₁ : IsIso (G.map (φ ▷ T)) := by
    have : IsIso (G.map φ ▷ (L((u)^*[A])).obj T ≫ lowerShriekRightAdjointTensorMap adj Q T) :=
      inferInstance
    erw [hl] at this
    exact IsIso.of_isIso_comp_left (lowerShriekRightAdjointTensorMap adj P T) _
  -- hence so is `G (T ◁ φ)`, through the braiding
  have h₂ : IsIso (G.map (T ◁ φ)) := by
    have e : T ◁ φ = (β_ P T).inv ≫ φ ▷ T ≫ (β_ Q T).hom := by
      rw [BraidedCategory.braiding_naturality_left, Iso.inv_hom_id_assoc]
    rw [e, G.map_comp, G.map_comp]
    infer_instance
  -- hence so is `G T ◁ Lu^* φ`
  have hr := Adjunction.projectionTensorMap_naturality_right adj _
    (projectionMap_app_app_naturality_right u) T φ
  have h₃ : IsIso (G.obj T ◁ (L((u)^*[A])).map φ) := by
    have : IsIso (lowerShriekRightAdjointTensorMap adj T P ≫ G.map (T ◁ φ)) := inferInstance
    erw [← hr] at this
    exact IsIso.of_isIso_comp_right _ (lowerShriekRightAdjointTensorMap adj T Q)
  exact hGT.isIso_of_isIso_whiskerLeft _

end Etale

end AlgebraicGeometry
