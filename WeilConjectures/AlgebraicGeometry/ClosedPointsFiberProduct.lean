/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# Closed points of schemes of finite type over a field

## Main results

- `AlgebraicGeometry.Etale.locallyOfFinitePresentation_and_finiteType_comp` (blueprint
  `lem-kun-etale-lfp`): étale morphisms are locally of finite presentation, and a quasi-compact
  étale scheme over a scheme of finite type over a field is of finite type over the field.
- `AlgebraicGeometry.Scheme.Pullback.isClosed_singleton_iff` (blueprint
  `lem-kun-closed-points-of-product`): a point of `X ×_K Y` is closed if and only if both of its
  images are closed.
- `AlgebraicGeometry.Scheme.finite_of_isClosed_of_forall_isClosed_singleton` (blueprint
  `lem-kun-finite-closed-subscheme`): a closed subset of a scheme of finite type over a field
  consisting of closed points is finite.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- A scheme `T` locally of finite type over a field whose dimension is at most zero is
discrete. -/
theorem Scheme.discreteTopology_of_topologicalKrullDim_le_zero_of_field {K : Type u} [Field K]
    {T : Scheme.{u}} (a : T ⟶ Spec (.of K)) [LocallyOfFiniteType a]
    (h : topologicalKrullDim T ≤ 0) : DiscreteTopology T := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian a
  have := IsLocallyArtinian.of_topologicalKrullDim_le_zero h
  exact (IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.1 this).2

/-- Blueprint `lem-kun-closed-points-of-product`: **closed points of a product.** Let `X` and `Y`
be schemes locally of finite type over a field `K` and `z ∈ X ×_K Y`. Then `z` is a closed point
if and only if its images in `X` and `Y` are closed points. The projections are locally of finite
type with Jacobson targets, so they preserve closed points. Conversely, if `x` and `y` are closed,
then `Spec κ(x) ×_K Spec κ(y) ⟶ X ×_K Y` is a closed immersion whose image contains `z`, and its
source is zero-dimensional (`κ(x)` being finite over `K`), hence discrete. -/
theorem Scheme.Pullback.isClosed_singleton_iff {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (z : (pullback f g : Scheme.{u})) :
    IsClosed {z} ↔ IsClosed {pullback.fst f g z} ∧ IsClosed {pullback.snd f g z} := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace g
  refine ⟨fun hz ↦ ⟨(pullback.fst f g).closePoints_subset_preimage_closedPoints hz,
    (pullback.snd f g).closePoints_subset_preimage_closedPoints hz⟩, fun ⟨hx, hy⟩ ↦ ?_⟩
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := isClosed_singleton_iff_isClosedImmersion.mp hy
  set ix := X.fromSpecResidueField (pullback.fst f g z)
  set iy := Y.fromSpecResidueField (pullback.snd f g z)
  set m := pullback.map (ix ≫ f) (iy ≫ g) f g ix iy (𝟙 _) (by simp) (by simp)
  have hm : IsClosedImmersion m :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance rfl rfl
  obtain ⟨w, hw⟩ : z ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    simp [ix, iy]
  have hdim : topologicalKrullDim (pullback (ix ≫ f) (iy ≫ g) : Scheme.{u}) ≤ 0 := by
    rw [topologicalKrullDim_pullback_eq_of_field (ix ≫ f) (iy ≫ g)]
    exact ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans
      (ringKrullDim_eq_zero_of_field _)).le
  have := Scheme.discreteTopology_of_topologicalKrullDim_le_zero_of_field
    (pullback.fst (ix ≫ f) (iy ≫ g) ≫ ix ≫ f) hdim
  rw [← hw, ← Set.image_singleton]
  exact m.isClosedEmbedding.isClosedMap _ (isClosed_discrete _)

end AlgebraicGeometry
