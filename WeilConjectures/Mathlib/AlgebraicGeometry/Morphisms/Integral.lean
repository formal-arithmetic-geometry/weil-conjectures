/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Field

/-!
# Integral morphisms between varieties of the same dimension

An integral morphism between integral schemes of finite type over a field which have the same
dimension preserves the codimension of a point, hence the dimension of the local rings. Locally
the morphism is given by an integral algebra `A → B` of finitely generated domains over the field,
and a point upstairs and its image correspond to a prime of `B` and its contraction to `A`; those
two primes have the same height by the dimension formula.

## Main results

* `AlgebraicGeometry.coheight_eq_of_isIntegralHom`: for an integral morphism `f : X ⟶ Y` between
  integral schemes of finite type over a field with `dim X = dim Y`, a point `x` of `X` and its
  image have the same codimension.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_isIntegralHom`: equivalently, the local rings
  `𝒪_{X,x}` and `𝒪_{Y,f x}` have the same Krull dimension.
-/

@[expose] public section

universe u

open CategoryTheory Order

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
  [IsIntegralHom f] (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
  [LocallyOfFiniteType sY]

include sX sY in
/-- **An integral morphism between varieties of the same dimension preserves codimension.**

Let `f : X ⟶ Y` be an integral morphism between integral schemes of finite type over a field `k`,
and suppose `X` and `Y` have the same dimension. Then every point `x` of `X` has the same
codimension as its image.

Surjectivity of `f` is not needed: it is automatic, the image of `f` being a closed irreducible
subset of `Y` of the same dimension as `Y`. -/
theorem coheight_eq_of_isIntegralHom (hdim : topologicalKrullDim X = topologicalKrullDim Y)
    (x : X) : coheight x = coheight (f x) := by
  -- an affine open neighbourhood `V` of `f x`, whose preimage is affine since `f` is affine
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (f x))
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hxU : x ∈ f ⁻¹ᵁ V := hxV
  have : Nonempty V := ⟨⟨f x, hxV⟩⟩
  have : Nonempty (f ⁻¹ᵁ V) := ⟨⟨x, hxU⟩⟩
  -- the sections over `f ⁻¹ᵁ V` form an integral algebra over those over `V`
  let _ : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := ⟨f.isIntegral_app V hV⟩
  -- both are finitely generated domains over `k`, of the same dimension as the ambient scheme
  let _ := sY.sectionsAlgebra V
  let _ := sX.sectionsAlgebra (f ⁻¹ᵁ V)
  have : Algebra.FiniteType k Γ(Y, V) := sY.finiteType_sections hV
  have : Algebra.FiniteType k Γ(X, f ⁻¹ᵁ V) := sX.finiteType_sections hU
  have hAB : ringKrullDim Γ(Y, V) = ringKrullDim Γ(X, f ⁻¹ᵁ V) := by
    rw [hV.ringKrullDim_eq_topologicalKrullDim sY, hU.ringKrullDim_eq_topologicalKrullDim sX]
    exact hdim.symm
  -- so the prime of `x` and its contraction, the prime of `f x`, have the same height
  have hheight :=
    Ideal.height_under_eq_of_ringKrullDim_eq k hAB (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  rw [hV.under_primeIdealOf f hU hxU] at hheight
  rw [hU.coheight_eq_height_primeIdealOf ⟨x, hxU⟩,
    hV.coheight_eq_height_primeIdealOf ⟨f x, hxV⟩, hheight]

include sX sY in
/-- **An integral morphism between varieties of the same dimension preserves the dimension of the
local rings.**

Let `f : X ⟶ Y` be an integral morphism between integral schemes of finite type over a field `k`,
and suppose `X` and `Y` have the same dimension. Then `𝒪_{X,x}` and `𝒪_{Y,f x}` have the same
Krull dimension for every point `x` of `X`. -/
theorem ringKrullDim_stalk_eq_of_isIntegralHom
    (hdim : topologicalKrullDim X = topologicalKrullDim Y) (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
    coheight_eq_of_isIntegralHom f sX sY hdim x]

end AlgebraicGeometry
