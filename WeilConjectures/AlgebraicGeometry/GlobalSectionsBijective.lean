/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Schemes over a field whose global functions are the constants

A `k`-scheme `X` satisfies `AlgebraicGeometry.Scheme.GlobalSectionsBijective k X` if the
structure map `k → Γ(X, 𝒪_X)` is bijective, i.e. `H⁰(X, 𝒪_X) = k`. This is the hypothesis
under which Riemann–Roch on a curve takes the form `χ(𝒪_X) = 1 - g`.

It does not hold for every proper connected `X`: `ℙ¹_ℂ` viewed as an `ℝ`-scheme has
`H⁰(X, 𝒪_X) = ℂ`. It holds for proper `X` that is geometrically connected and geometrically
reduced (Stacks 0BUG), hence for proper geometrically integral `X`, and for smooth proper
connected `X` over a separably closed field.

## Main definitions

- `AlgebraicGeometry.Scheme.GlobalSectionsBijective`: the structure map `k → Γ(X, 𝒪_X)` is
  bijective.

## Main statements

- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyConnected`: a proper,
  geometrically connected and geometrically reduced `k`-scheme has `H⁰(X, 𝒪_X) = k`.
- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral` and
  `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_isSepClosed`: the geometrically integral
  case and the case of a smooth connected scheme over a separably closed field.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The structure map `k → Γ(X, 𝒪_X)` of a `k`-scheme `X` is bijective, i.e. `H⁰(X, 𝒪_X) = k`.

This is the hypothesis under which Riemann–Roch holds in the form `χ(𝒪_X) = 1 - g` with
`g = dim_k H¹(X, 𝒪_X)`. It fails for `ℙ¹_ℂ` viewed as an `ℝ`-scheme, which has `H⁰ = ℂ`, so
`χ(𝒪) = 2 ≠ 1 - 0` over `ℝ`. -/
class GlobalSectionsBijective : Prop where
  bijective_globalSectionsRingHom : Function.Bijective (globalSectionsRingHom k (X := X))

variable {k X}

/-- A proper `k`-scheme that is geometrically connected and geometrically reduced has
`H⁰(X, 𝒪_X) = k` (Stacks 0BUG). -/
instance GlobalSectionsBijective.of_geometricallyConnected [IsProper (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))] [GeometricallyReduced (X ↘ Spec (.of k))] :
    GlobalSectionsBijective k X :=
  sorry

/-- A proper geometrically integral `k`-scheme has `H⁰(X, 𝒪_X) = k`. -/
theorem GlobalSectionsBijective.of_geometricallyIntegral [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] : GlobalSectionsBijective k X :=
  inferInstance

/-- A smooth proper connected scheme over a separably closed field `k` has
`H⁰(X, 𝒪_X) = k`. -/
theorem GlobalSectionsBijective.of_isSepClosed [IsSepClosed k] [Smooth (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] : GlobalSectionsBijective k X :=
  have := GeometricallyConnected.of_isSepClosed (k := k) X
  inferInstance

end AlgebraicGeometry.Scheme
