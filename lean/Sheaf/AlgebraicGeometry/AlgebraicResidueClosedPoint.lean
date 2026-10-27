module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Maximal
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField

/-! # Closed points with algebraic residue extensions

Source: Stacks Project, Morphisms, Tag 01TE, part (2)
(blueprint: lem-sfb-scheme-algebraic-residue-closed-point).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A point with algebraic residue extension over a closed image point is closed.
Source: Stacks Project, Morphisms, Tag 01TE, part (2)
(blueprint: lem-sfb-scheme-algebraic-residue-closed-point).

Proof:
1. If z specializes y, continuity and closedness of f(y) give f(z) = f(y).
   By `lem-weil-pbc-affine-opens-basis`, choose affine neighbourhoods V = Spec A of f(y)
   and U = Spec B of z inside the preimage of V. Since z specializes y, U contains y.
   By `def-weil-affine-spectrum`, the restriction is induced by a ring map A → B.
   Denote the primes for f(y), y, z by p, q, r respectively.
2. The closure formula in `lem-weil-pbc-spec-irreducible-closed-subsets-primes` gives
   V(p) = {p}. By `lem-weil-pbc-proper-ideal-contained-in-maximal`, choose a maximal
   ideal containing p; it belongs to V(p), hence equals p. Thus k = A/p is a field.
   By `lem-weil-pbc-spec-field-point-residue-field` and `def-weil-residue-field`,
   the canonical maps identify k with κ(f(y)) and embed C = B/q into κ(y),
   compatibly with the specified residue-field map; hence k ⊆ C ⊆ κ(y).
3. For nonzero b in C, `def-weil-algebraic-element` gives a nonzero polynomial relation
   over k. Divide out the initial power of b in κ(y) to obtain
   a₀ + a₁b + ⋯ + aₙbⁿ = 0 with a₀ ≠ 0. Consequently
   b⁻¹ = -a₀⁻¹(a₁ + ⋯ + aₙbⁿ⁻¹) lies in C. Thus C is a field and q is maximal.
   This is the elementary argument of Fields Tag 0BID used in Algebra Tag 00GA.
4. By `lem-weil-pbc-spec-irreducible-closed-subsets-primes`, specialization in U
   gives q ⊆ r. Maximality and properness force equality, so z = y.
   Therefore the closure of {y} is {y}, and {y} is closed.
-/
theorem isClosed_singleton_of_isAlgebraic_residueField
    {Y S : Scheme.{u}} (f : Y ⟶ S) (y : Y)
    (hs : IsClosed ({f y} : Set S))
    (halg : @Algebra.IsAlgebraic (S.residueField (f y)) (Y.residueField y) _ _
      (f.residueFieldMap y).hom.toAlgebra) :
    IsClosed ({y} : Set Y) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
