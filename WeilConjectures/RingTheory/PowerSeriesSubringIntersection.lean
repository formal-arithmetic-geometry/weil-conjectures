/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The intersection of the p-basis coefficient subrings

Source: Stacks Project, More on Algebra, Tag 07P5, proof of the intersection,
with the coefficient argument of the parent node, steps 3(c) and 5.
-/

@[expose] public section

set_option autoImplicit false

universe u w

attribute [local instance] ZMod.algebra

namespace RingTheory

/-- The intersection of the coefficient subrings is precisely the pth powers in A.
Source: Stacks Project, More on Algebra, Tag 07P5, proof of (2), last sentence;
the coefficient argument is expanded in parent node steps 3(c) and 5.
(blueprint: lem-weil-pbc-power-series-subring-intersection).

Proof: The pth powers in k form a subfield, since Frobenius is an injective ring
homomorphism. For each finite J, the k^p-span of bounded p-basis monomials whose
supports avoid J equals kJ. Indeed it contains the stated generators and is closed
under multiplication by reducing exponents modulo p. A nonzero element lies in
the span on finitely many generators outside J; this is a finite-dimensional
subring, so its injective multiplication map is surjective and its inverse lies
in the same span. Conversely all those monomials and their k^p-linear combinations
belong to kJ. If c belongs to every kJ, let J be the union of the supports in its
finite p-basis expansion. Its expansion in monomials avoiding J has, by uniqueness,
no nonzero nonconstant coordinate. Thus c belongs to k^p.

If f belongs to every AJ, hAJ gives p-divisible x and y exponents and coefficients
in every kJ, hence in k^p by the preceding argument. At each pair of exponents
(pa,pg), take the unique pth root in k of that coefficient. Make the power series
with these coefficients, for each g. Only finitely many y-columns are nonzero,
because f is a polynomial and Frobenius is injective. They therefore define an
actual polynomial h in A. Coefficientwise Frobenius on power series and the
finite-sum Frobenius identity on polynomials give h^p = f. Conversely the same
identities show that every h^p has p-divisible exponents and coefficients in k^p,
which is contained in every kJ, so hAJ puts h^p in every AJ. The argument includes
empty J, empty I, and n=m=0; no uniform finite bound on power-series supports is used. -/
theorem powerSeriesSubringIntersection
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (I : Type w) (t : I → k)
    (hpb : ∃ b : Module.Basis
      {E : I →₀ ℕ // ∀ i : I, E i < p}
      (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k,
      ∀ E, b E = (E : I →₀ ℕ).prod (fun i e => t i ^ e))
    (n m : ℕ) (kJ : Finset I → Subfield k)
    (hkJ : ∀ J, kJ J = Subfield.closure
      (Set.range (fun x : k => x ^ p) ∪ {x : k | ∃ i : I, i ∉ J ∧ t i = x}))
    (AJ : Finset I → Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hAJ : ∀ J f, f ∈ AJ J ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (MvPolynomial.coeff g f) ∈ kJ J ∧
        (MvPowerSeries.coeff a (MvPolynomial.coeff g f) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j))) :
    ∀ f : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k),
      (∀ J, f ∈ AJ J) ↔ ∃ h, h ^ p = f := by
  sorry

end RingTheory
