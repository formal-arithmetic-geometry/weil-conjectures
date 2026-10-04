/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

/-!
# Relative effective Cartier divisors

Let `π : X ⟶ S` be a morphism of schemes. A closed subscheme `D ⊆ X`, given by a quasi-coherent
ideal `J`, is a *relative effective Cartier divisor on `X/S`* if `J` is invertible (`D` is an
effective Cartier divisor on `X`) and `D ⟶ S` is flat. Rather than a definition, this file uses
the two conditions `J.IsInvertible` and `Flat (J.subschemeι ≫ π)` directly.

We state the two criteria that the Picard framework needs:

* a locally principal closed subscheme of a flat, locally finitely presented `X/S` whose fibres
  are effective Cartier divisors is a relative effective Cartier divisor;
* on a proper smooth `X/S` of relative dimension `1`, a relative effective Cartier divisor is
  finite locally free over `S`.

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.IsLocallyPrincipal.isInvertible_and_flat`
  (blueprint `lem-pc-recd-locally-principal`).
- `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isFinite_and_locallyOfFinitePresentation`
  (blueprint `lem-pc-cartier-criterion`, `(2) ⇒ (1)` for proper `X/S`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- **Effective Cartier divisors from local equations.** Let `π : X ⟶ S` be flat and locally of
finite presentation and let `D ⊆ X` be a locally principal closed subscheme, with ideal `J`. If
every fibre `D_s ⊆ X_s` is an effective Cartier divisor, then `D` is a relative effective
Cartier divisor on `X/S`: `J` is invertible and `D ⟶ S` is flat.

(Stacks, Tag 062Y; blueprint: `lem-pc-recd-locally-principal`) -/
theorem IsLocallyPrincipal.isInvertible_and_flat (π : X ⟶ S) [Flat π]
    [LocallyOfFinitePresentation π] {J : X.IdealSheafData} (hJ : J.IsLocallyPrincipal)
    (hfib : ∀ s : S, (J.comap (π.fiberι s)).IsInvertible) :
    J.IsInvertible ∧ Flat (J.subschemeι ≫ π) :=
  sorry

/-- **The Cartier criterion on proper smooth curves.** Let `π : X ⟶ S` be proper and smooth of
relative dimension `1`, and let `D ⊆ X` be a relative effective Cartier divisor, i.e. its ideal
`J` is invertible and `D ⟶ S` is flat. Then `D ⟶ S` is finite locally free: finite, (flat) and
locally of finite presentation.

(Stacks, Tag 0B9D; blueprint: `lem-pc-cartier-criterion`, the implication `(2) ⇒ (1)` for
proper `X/S`) -/
theorem IsInvertible.isFinite_and_locallyOfFinitePresentation (π : X ⟶ S)
    [IsProper π] [SmoothOfRelativeDimension 1 π] {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hflat : Flat (J.subschemeι ≫ π)) :
    IsFinite (J.subschemeι ≫ π) ∧ LocallyOfFinitePresentation (J.subschemeι ≫ π) :=
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
