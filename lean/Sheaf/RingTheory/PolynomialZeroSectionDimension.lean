module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import WeilConjectures.RingTheory.DimensionAtPointComponents

/-!
# Topological dimension at the zero section of a polynomial algebra

Source: Stacks Project, Algebra, Tags 00OT and 00P0, applied componentwise to a
polynomial algebra (blueprint: lem-sfb-polynomial-zero-section-dimension).
-/

@[expose] public section

universe u v

set_option autoImplicit false

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Tags 00OT and 00P0, applied to polynomial components
(blueprint: lem-sfb-polynomial-zero-section-dimension).

For a finite type algebra `B` over a field, adjoining `r` variables increases the
open-neighbourhood dimension at the zero-section point over `q` by `r`. Both dimensions
are finite nonnegative integers, witnessed by `d` and `d + r`. The point upstairs is the
inverse image of `q` under evaluation at zero, hence has ideal `q B[X] + (X₁, …, Xᵣ)`.
No reducedness, equidimensionality or perfectness is required.

Proof:
1. Algebra generators of `B`, together with the `r` variables, generate the polynomial
   algebra over the field. Evaluation at zero followed by reduction modulo `q` has kernel
   `q B[X] + (X₁, …, Xᵣ)`: subtracting the constant term leaves an element of the variable
   ideal. The quotient is `B/q`, a domain, and the kernel contracts to `q`.
2. Coefficient reduction identifies `B[X]/a B[X]` with `(B/a)[X]` for every ideal `a`.
   For prime `a` this is a domain by `lem-weil-pbc-polynomial-ring-domain`. Given a minimal
   prime `P` of `B[X]`, choose a minimal prime `a` below its contraction using
   `lem-weil-pbc-prime-contains-minimal-prime`; then `a B[X]` is prime below `P`, hence
   equals `P`. Conversely contraction proves `a B[X]` minimal when `a` is minimal.
   Extension and contraction identify the minimal primes below the two specified points.
3. Each `B/a` is finite type over the field, hence Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`. Applying
   `lem-sf-noetherian-polynomial-dimension` to `(B/a)[X]` gives dimension `dim(B/a) + r`.
   Ring isomorphisms preserve prime chains and therefore ring Krull dimension.
4. Apply `lem-weil-pbc-dimension-at-point-components` to both finite type algebras.
   Their dimensions at the specified points are the maxima over the corresponding finite
   nonempty sets of minimal-prime components. Adding `r` commutes with this maximum,
   proving the formula. The same component theorem makes both dimensions nonnegative
   integers. For `r = 0` the formula persists; for the zero ring there is no point `q`. -/
theorem topologicalKrullDimAt_polynomial_zero_section
    {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (r : ℕ) (q : Spec (CommRingCat.of B)) :
    ∃ d : ℕ,
      topologicalKrullDimAt q = (d : WithBot ℕ∞) ∧
      topologicalKrullDimAt (X := Spec (CommRingCat.of (MvPolynomial (Fin r) B)))
        (PrimeSpectrum.comap (MvPolynomial.eval (fun _ : Fin r ↦ (0 : B))) q) =
          ((d + r : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
