/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.CountableTensorStructures
public import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality

/-!
# Additive total tensor and mapping cones before localization

Total tensor with an arbitrary complex commutes with mapping cones naturally and preserves cone
inclusions; localization sends the same chain isomorphisms to derived isomorphisms.

## Implementation details

The total tensor is the binary signed direct-sum tensor. The cone is Mathlib's `mappingCone`: its
coordinates are ordered as `X[n+1]` then `Y[n]`, rather than `Y[n]` then `X[n+1]`.

The chain comparison and its naturality are taken from
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone` (second-variable cone
comparison) and `WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality`.

## References

* Stacks Project, Tag 0G6E (first exactness assertion)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

/-- Total tensor with an arbitrary complex commutes with cones naturally and preserves
cone inclusions; localization sends the same chain isomorphisms to derived isomorphisms. -/
theorem exists_totalTensorConeComparison (C : Type u) [Category.{v} C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [TensorPreservesCountableCoproducts C] [HasDerivedCategory.{w} C] :
    ∃ φ : ∀ (P X Y : CochainComplex C ℤ) (u : X ⟶ Y),
      HomologicalComplex.tensorObj P (mappingCone u) ≅
        mappingCone (HomologicalComplex.tensorHom (𝟙 P) u),
    (∀ (P P' X Y X' Y' : CochainComplex C ℤ)
        (f : P ⟶ P') (u : X ⟶ Y) (u' : X' ⟶ Y')
        (a : X ⟶ X') (b : Y ⟶ Y') (h : u ≫ b = a ≫ u'),
      HomologicalComplex.tensorHom f (mappingCone.map u u' a b h) ≫
          (φ P' X' Y' u').hom =
        (φ P X Y u).hom ≫
          mappingCone.map (HomologicalComplex.tensorHom (𝟙 P) u)
            (HomologicalComplex.tensorHom (𝟙 P') u')
            (HomologicalComplex.tensorHom f a) (HomologicalComplex.tensorHom f b)
            (mapBifunctorMap_comm (curriedTensor C) f u u' a b h)) ∧
    (∀ (P X Y : CochainComplex C ℤ) (u : X ⟶ Y),
      HomologicalComplex.tensorHom (𝟙 P) (mappingCone.inr u) ≫ (φ P X Y u).hom =
        mappingCone.inr (HomologicalComplex.tensorHom (𝟙 P) u)) ∧
    (∀ (P X Y : CochainComplex C ℤ) (u : X ⟶ Y),
      ∃ e : (DerivedCategory.Q (C := C)).obj
            (HomologicalComplex.tensorObj P (mappingCone u)) ≅
          (DerivedCategory.Q (C := C)).obj
            (mappingCone (HomologicalComplex.tensorHom (𝟙 P) u)),
        e.hom = (DerivedCategory.Q (C := C)).map (φ P X Y u).hom) := by
  refine ⟨fun P _ _ u ↦ mapBifunctorMappingCone₂Iso P u (curriedTensor C), ?_, ?_, ?_⟩
  · intro P P' X Y X' Y' f u u' a b h
    exact mapBifunctorMappingCone₂Iso_hom_naturality (curriedTensor C) f u u' a b h
  · intro P X Y u
    exact mapBifunctorMap_inr_mapBifunctorMappingCone₂Iso_hom P u (curriedTensor C)
  · intro P X Y u
    exact ⟨(DerivedCategory.Q (C := C)).mapIso
      (mapBifunctorMappingCone₂Iso P u (curriedTensor C)), rfl⟩

end CochainComplex
