/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil Conjectures Formalization Project
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.BilinearMap

/-! # Gabber–Ramero obstruction ideal

Source: Temkin, Non-embedded desingularization, §3.2.2, conormal description
(blueprint: def-per-gabber-ramero-obstruction-ideal).

The conormal module and its quotient action are `Algebra.Extension.Cotangent`.
The canonical differential is expressed in polynomial coordinates. The presentation
ideal is the inverse image of the range of precomposition by this differential under
scalar multiplication on the conormal module. Finally take the intersection over
all finite generating tuples and their evaluation maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

namespace Algebra

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- The conormal differential `[f] ↦ (π(∂f/∂xᵢ))ᵢ` for a finite polynomial presentation.
Here `G.toExtension.Cotangent` is `L/L²`, with the quotient `B`-action, and
`cotangentSpaceBasis_repr_one_tmul` identifies the coordinates with partial derivatives.
Source: Temkin, Non-embedded desingularization, §3.2.2, conormal description
(blueprint: def-per-gabber-ramero-obstruction-ideal). -/
def Generators.gabberRameroDifferential {n : ℕ} (G : Generators R B (Fin n)) :
    G.toExtension.Cotangent →ₗ[B] (Fin n → B) :=
  Finsupp.lcoeFun.comp
    (G.cotangentSpaceBasis.repr.toLinearMap.comp G.toExtension.cotangentComplex)

/-- The presentation obstruction ideal consists exactly of scalars `b` for which
there is a `B`-linear map `h : Bⁿ → L/L²` with `h ∘ δ = b • id`.
It is the inverse image, under the linear scalar-multiplication map, of the range
of the linear precomposition map. This gives its ideal structure without choosing
factorizations or generators of the ideal.
Source: Temkin, Non-embedded desingularization, §3.2.2, conormal description
(blueprint: def-per-gabber-ramero-obstruction-ideal). -/
def Generators.gabberRameroPresentationIdeal {n : ℕ} (G : Generators R B (Fin n)) :
    Ideal B :=
  (LinearMap.range
    (LinearMap.lcomp B G.toExtension.Cotangent G.gabberRameroDifferential)).comap
      (LinearMap.lsmul B G.toExtension.Cotangent)

/-- The Gabber–Ramero obstruction ideal of a finitely presented commutative algebra:
the intersection of its presentation obstruction ideals over finite generating tuples.
Surjectivity of evaluation is precisely the condition that the tuple generates.
The index `n : ℕ` includes `n = 0`, so generating empty tuples are retained.
Source: Temkin, Non-embedded desingularization, §3.2.2, conormal description
(blueprint: def-per-gabber-ramero-obstruction-ideal). -/
def gabberRameroObstructionIdeal (R : Type u) (B : Type v)
    [CommRing R] [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B] : Ideal B :=
  ⨅ (n : ℕ) (x : Fin n → B)
    (hx : Function.Surjective (MvPolynomial.aeval (R := R) x)),
    (Generators.ofSurjective x hx).gabberRameroPresentationIdeal

end Algebra
