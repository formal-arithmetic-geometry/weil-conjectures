/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.CharP.Frobenius

/-!
# Coefficient sections with prescribed p-basis lifts

Source: Illusie, Laszlo, Orgogozo, Travaux de Gabber, Expose IV, 2.1.4, printed p.50
(blueprint: lem-per-prescribed-pbasis-coefficient-section).

The p-basis condition is written inline. In characteristic p the pth powers form a
subfield, so their subfield closure is exactly the subfield of pth powers.
-/

@[expose] public section

universe u v

namespace IsLocalRing

/-- A residue-field p-basis and arbitrary lifts determine a unique coefficient section.

Source: Illusie, Laszlo, Orgogozo, Travaux de Gabber, Expose IV, 2.1.4, printed p.50,
which cites Bourbaki, Algebre commutative IX, section 2, no.2, Theorem 1(a).
(blueprint: lem-per-prescribed-pbasis-coefficient-section).

Proof (the node's explicit Frobenius-expansion argument):
1. Put q_n = p^n. The assumed p-monomial basis gives, by induction on n, a unique finite
   expansion x = sum_e a_(n,e)(x)^q_n b^e with exponents less than q_n. Expand each root
   coefficient at the next stage and use the unique base-p digit decomposition
   e + q_n f. Frobenius is injective on the residue field, so the roots are unique.
2. In R_n = A / m^q_n define t_n on the q_n-th-power subfield by taking the q_n-th
   power of any residue lift. The root is unique and two lifts differ in m, so their
   powers agree modulo m^q_n. Frobenius additivity and multiplicativity show t_n is a
   unital ring homomorphism (def-weil-ring-frobenius).
3. Define s_n(x) by applying t_n to the coefficients of the expansion in step 1 and
   replacing b by the prescribed lifts beta. Addition follows coefficientwise. For
   multiplication write e_i + f_i = g_i + q_n h_i and absorb the carries b_i^q_n into
   the coefficients; t_n(b_i^q_n) = beta_i^q_n proves multiplicativity. The expansion
   of 1 proves preservation of 1. Reduction gives x, and each b_i maps to beta_i.
   At n = 0 this is the identity of the residue field.
4. The maps s_n commute with R_(n+1) -> R_n: the level-n root coefficient is a sum
   of pth powers of level-(n+1) roots times b^f. The difference of a lift of that
   coefficient and the corresponding sum of lifted roots times beta^f lies in m.
   Raising to q_n puts the difference in m^q_n, giving precisely compatibility.
5. For each N reduce s_n to A / m^N using any q_n >= N. Compatibility makes the
   result independent of n. Completeness (def-weil-pbc-adically-complete-ring) lifts
   this compatible tuple uniquely to s(x) in A. Injectivity of the canonical map to
   the completion proves the ring identities, the residue-section identity and the
   prescribed values. The residue-section identity also proves injectivity of s.
6. For another section u with the prescribed values, apply u to the expansion in
   step 1. Its coefficient roots are residue lifts, so u and s agree modulo m^q_n
   for every n. Cofinality of p^n and adic separatedness give u = s.
All exponent families and sums are finitely supported, including for infinite E. -/
theorem existsUnique_coefficientSection_prescribed_pBasis
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CharP A p] [IsAdicComplete (maximalIdeal A) A]
    (E : Type v) (b : E → ResidueField A)
    (hpb : ∃ mon : Module.Basis {e : E →₀ ℕ // ∀ i : E, e i < p}
      (Subfield.closure (Set.range (fun x : ResidueField A ↦ x ^ p))) (ResidueField A),
      ∀ e, mon e = e.val.prod (fun i n ↦ b i ^ n))
    (beta : E → A) (hlift : ∀ i : E, residue A (beta i) = b i) :
    ∃! s : ResidueField A →+* A,
      (residue A).comp s = RingHom.id (ResidueField A) ∧ ∀ i : E, s (b i) = beta i := by
  sorry

end IsLocalRing
