/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Spanning families of finite locally free quotients of polynomial rings

Let `A` be a commutative ring and `I ⊆ A[n]` an ideal such that `A[n] ⧸ I` is a finite locally
free `A`-module. This file collects the commutative algebra behind the openness and the covering
of the subfunctors `F_W` of the Hilbert functor of points of an affine space (blueprint
`lem-pc-hilb-representable`, Step 4 (2)(b) and (2)(c)):

* a spanning family of `d` elements of a finite locally free module of rank `d` is a basis;
* the images of a family `v` of polynomials span `B[n] ⧸ I B[n]` over an `A`-algebra `B` if and
  only if the annihilator `J` of the cokernel of `v` generates the unit ideal of `B`; hence the
  locus where they span is the open complement of `V(J)`;
* every prime of `A` lies in such a locus for some family of `d` monomials.

## Main statements

- `linearIndependent_of_span_eq_top_of_rankAtStalk`
- `MvPolynomial.span_range_mk_map_eq_top_iff`
- `MvPolynomial.exists_monomials_annihilator_not_le`
-/

@[expose] public section

/-- **A spanning family of the right size is a basis.** If `M` is a finitely presented flat
`A`-module of rank `d` at every prime, then a family of `d` elements spanning `M` is linearly
independent. -/
theorem linearIndependent_of_span_eq_top_of_rankAtStalk {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [Module.Flat A M] {d : ℕ}
    (v : Fin d → M) (hv : Submodule.span A (Set.range v) = ⊤)
    (hM : ∀ p, Module.rankAtStalk (R := A) M p = d) : LinearIndependent A v :=
  sorry

namespace MvPolynomial

variable {n A B : Type*} [CommRing A] [CommRing B]

/-- **Spanning after base change** (blueprint `lem-pc-hilb-representable`, Step 4 (2)(b)). Let
`I ⊆ A[n]` be an ideal with `A[n] ⧸ I` finite over `A`, let `φ : A →+* B` and let `v` be a family
of polynomials. The images of `v` span `B[n] ⧸ I B[n]` over `B` if and only if the annihilator
of the cokernel of `v` on `A[n] ⧸ I` generates the unit ideal of `B`. -/
theorem span_range_mk_map_eq_top_iff (φ : A →+* B) (I : Ideal (MvPolynomial n A))
    [Module.Finite A (MvPolynomial n A ⧸ I)] {ι : Type*} (v : ι → MvPolynomial n A) :
    Submodule.span B (Set.range fun i ↦ Ideal.Quotient.mk (I.map (map φ)) (map φ (v i))) = ⊤ ↔
      (Module.annihilator A ((MvPolynomial n A ⧸ I) ⧸
        Submodule.span A (Set.range fun i ↦ Ideal.Quotient.mk I (v i)))).map φ = ⊤ :=
  sorry

/-- **Monomial bases exist locally** (blueprint `lem-pc-hilb-representable`, Step 4 (2)(c)).
If `A[n] ⧸ I` is a finitely presented flat `A`-module of rank `d` at the prime `p`, then there
are `d` monomials whose images span `A[n] ⧸ I` near `p`: the annihilator of the cokernel of
their images is not contained in `p`. -/
theorem exists_monomials_annihilator_not_le (I : Ideal (MvPolynomial n A))
    [Module.FinitePresentation A (MvPolynomial n A ⧸ I)] [Module.Flat A (MvPolynomial n A ⧸ I)]
    (p : PrimeSpectrum A) {d : ℕ} (hp : Module.rankAtStalk (MvPolynomial n A ⧸ I) p = d) :
    ∃ v : Fin d → (n →₀ ℕ), ¬ Module.annihilator A ((MvPolynomial n A ⧸ I) ⧸
      Submodule.span A (Set.range fun l ↦ Ideal.Quotient.mk I (monomial (v l) 1))) ≤
        p.asIdeal :=
  sorry

end MvPolynomial
