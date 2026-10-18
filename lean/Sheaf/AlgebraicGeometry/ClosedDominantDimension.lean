/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback

/-!
# Dimension formula for a closed dominant morphism

Source: Stacks Project, Morphisms, Tag 02JX, lemma-alteration-dimension
(blueprint: lem-trf-closed-dominant-dimension).

The induced map of function fields `k(U) → k(V)` is the existing
`AlgebraicGeometry.Scheme.Hom.functionFieldMap` (the stalk map at the generic point), applied
to the identification `f (genericPoint V) = genericPoint U` given by
`AlgebraicGeometry.Scheme.Hom.apply_genericPoint_of_isDominant`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/--
Source: Stacks Project, Morphisms, Tag 02JX, lemma-alteration-dimension
(blueprint: lem-trf-closed-dominant-dimension).

Let `f : V ⟶ U` be a dominant morphism locally of finite type between integral schemes with
`U` locally Noetherian, and let `r = trdeg_{k(U)} k(V)` for the injection of function fields
induced by `f` (the stalk map at the generic point). Then `dim V ≤ dim U + r`; if the
underlying map of `f` is closed, `dim V = dim U + r`; and if `f` is proper and `k(V)` is
finite over `k(U)`, then `dim V = dim U`. Dimensions are topological Krull dimensions in
`WithBot ℕ∞`, so infinite values are allowed.

Proof (Tag 02JX):
1. Let `ξ₀ ⤳ ⋯ ⤳ ξₑ` be a chain of specializations in `V`, `x = ξₑ`, `y = f x`. By
   lem-sc-scheme-stalk-dimension-generalization-chains the chain lies in the local scheme at
   `x`, so `e ≤ dim 𝒪_{V,x}`. By lem-trf-local-dimension-formula,
   `dim 𝒪_{V,x} ≤ dim 𝒪_{U,y} + r - trdeg_{κ(y)} κ(x)`; drop the last term and use
   `dim 𝒪_{U,y} ≤ dim U`. Taking the supremum gives `dim V ≤ dim U + r`.
2. Assume `f` closed. Take a chain `η = ξ̄₀ ⤳ ⋯ ⤳ ξ̄_d` in `U` from the generic point. The
   generic fibre `V_η = V ×_U Spec k(U)` is nonempty, integral, locally of finite type over
   `k(U)`, with generic point that of `V` and function field `k(V)` (affine charts
   `Spec (S⁻¹B)`, `S = A \ {0}`, `A → B` injective by dominance). By
   lem-trf-generic-fibre-closed-chain there is a closed point `ξ₀` of `V_η` and a chain of
   `r` specializations ending at `ξ₀`, with finite residue extension over `k(U)`.
3. Since `f` is closed, by lem-trf-closed-map-specializing specializations lift along `f`:
   starting from `ξ₀` one obtains `ξ₀ ⤳ ξ₁ ⤳ ⋯ ⤳ ξ_d` with `f ξᵢ = ξ̄ᵢ`.
4. Concatenating the generic-fibre chain of length `r` with the lifted chain of length `d`
   gives a chain of length `r + d` in `V`; the supremum over chains starting at the generic
   point of `U` gives `dim V ≥ dim U + r`, hence equality. Both schemes are nonempty since
   they are integral.
5. A proper `f` is closed by pqf-lem-proper-closed-map, and a finite extension
   `k(U) ⊆ k(V)` has transcendence degree zero, so the equality gives `dim V = dim U`.
-/
theorem closed_dominant_dimension
    (U V : Scheme.{u}) [IsIntegral U] [IsIntegral V]
    (f : V ⟶ U) [IsDominant f] [LocallyOfFiniteType f] [IsLocallyNoetherian U] :
    letI := (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.toAlgebra
    Function.Injective (algebraMap U.functionField V.functionField) ∧
      topologicalKrullDim V ≤ topologicalKrullDim U +
          (Cardinal.toENat (Algebra.trdeg U.functionField V.functionField) : WithBot ℕ∞) ∧
      (IsClosedMap f →
        topologicalKrullDim V = topologicalKrullDim U +
          (Cardinal.toENat (Algebra.trdeg U.functionField V.functionField) : WithBot ℕ∞)) ∧
      (IsProper f → Module.Finite U.functionField V.functionField →
        topologicalKrullDim V = topologicalKrullDim U) := by
  sorry

end AlgebraicGeometry
