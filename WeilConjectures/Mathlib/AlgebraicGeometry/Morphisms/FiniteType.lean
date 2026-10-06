/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Dimension of integral schemes locally of finite type over a field

An integral scheme locally of finite type over a field has the dimension of any of its nonempty
open subschemes (`AlgebraicGeometry.topologicalKrullDim_opens_eq`), which is finite
(`AlgebraicGeometry.topologicalKrullDim_ne_top`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An integral scheme `X` locally of finite type over a field `K` has the same dimension as each
of its nonempty open subschemes: both are the transcendence degree over `K` of the function
field of `X`. -/
theorem topologicalKrullDim_opens_eq {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsIntegral X] (U : X.Opens) [Nonempty U] :
    topologicalKrullDim (U : Set X) = topologicalKrullDim X :=
  sorry

/-- An integral scheme locally of finite type over a field has finite dimension: the dimension of
any nonempty affine open subscheme, the spectrum of a finitely generated algebra. -/
theorem topologicalKrullDim_ne_top {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsIntegral X] :
    topologicalKrullDim X ≠ ⊤ := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [← topologicalKrullDim_opens_eq f U]
  have hft : RingHom.FiniteType (f.appLE ⊤ U (by simp)).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  let φ : K →+* Γ(X, U) := (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  let := φ.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hφ
  have := IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  change topologicalKrullDim (U : Set X) = topologicalKrullDim (PrimeSpectrum Γ(X, U)) at this
  rw [this]
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_ne_top_of_finiteType K _

end AlgebraicGeometry
