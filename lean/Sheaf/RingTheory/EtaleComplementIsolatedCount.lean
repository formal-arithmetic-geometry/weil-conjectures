/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Isolated points in the complementary idempotent fibre

Source: Stacks Project, Algebra, Tag 00UK, the decrease in the induction parameter
(blueprint: lem-weil-pbc-etale-complement-isolated-count).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- (blueprint: lem-weil-pbc-etale-complement-isolated-count)
Source: Stacks Project, Algebra, Tag 00UK, proof, the complementary fibre after
splitting off the selected isolated point using Tag 00UJ.

Proof: Write `C = R₁ ⊗[R] S`. Bijectivity of the residue-field map gives an
isomorphism `κ(P) ⊗[R₁] C ≃ κ(p) ⊗[R] S`, by associativity of tensor products
and transport along the residue-field isomorphism. Passing to prime spectra gives
a homeomorphism of these fibres. Quotienting `C` by its idempotent `e` identifies
the fibre of `C/(e)` with the clopen subset of the fibre of `C` where `e` vanishes.
The clopen inclusion carries each isolated point to an isolated point and is
injective. The given prime `r` belongs to the other clopen factor, since `e` is
not in `r`. Under the fibre comparison it corresponds to `q`, which is isolated
by quasi-finiteness. Thus the injection on isolated points misses this point.
The original isolated-point set is finite: a finite-type algebra over the field
`κ(p)` is Noetherian; an isolated prime is minimal, and there are finitely many
minimal primes. An injection into this finite set minus one of its points gives
the asserted strict cardinal inequality. This argument does not construct any
étale extension or iterate the removal. -/
theorem fibre_ncard_quotient_idempotent_lt
    {R : Type u} {S : Type (max u v)} {R₁ : Type u}
    [CommRing R] [CommRing S] [CommRing R₁] [Algebra R S] [Algebra R R₁]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime]
    (P : Ideal R₁) [P.IsPrime] [P.LiesOver p]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R₁) (P.over_def p)))
    (e : R₁ ⊗[R] S) (he : IsIdempotentElem e)
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
    (r : Ideal (R₁ ⊗[R] S)) [r.IsPrime] [r.LiesOver P]
    (hrq : r.comap Algebra.TensorProduct.includeRight.toRingHom = q) (her : e ∉ r) :
    {z : PrimeSpectrum (P.Fiber ((R₁ ⊗[R] S) ⧸ Ideal.span {e})) |
      IsOpen ({z} : Set (PrimeSpectrum (P.Fiber ((R₁ ⊗[R] S) ⧸ Ideal.span {e}))))}.ncard <
    {z : PrimeSpectrum (p.Fiber S) |
      IsOpen ({z} : Set (PrimeSpectrum (p.Fiber S)))}.ncard := by sorry

end Algebra
