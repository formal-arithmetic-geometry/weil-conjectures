/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial associated graded algebras after a prefix quotient

Source: Stacks Project, Algebra, Tags 061R (lemma-truncate-quasi-regular),
061P and 061N, specialized to the ring as its own module
(blueprint: lem-pur-quasi-regular-prefix-quotient).

Polynomial evaluation sends variables to degree-one initial forms and coefficients
into degree zero. Thus bijectivity expresses that this canonical graded algebra
map is an isomorphism. The coefficient identification in the conclusion is specified
on every representative in the original ring.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- The ideal of the first `i` generators, using zero-based indices. Source: Stacks,
Algebra, Tag 061R (blueprint: lem-pur-quasi-regular-prefix-quotient). -/
def quasiRegularPrefixIdeal {A : Type u} [CommRing A] {b : ℕ}
    (f : Fin b → A) (i : ℕ) : Ideal A :=
  Ideal.span (f '' {j : Fin b | j.val < i})

/-- The remaining generators in the quotient by the prefix. Source: Stacks,
Algebra, Tag 061R (blueprint: lem-pur-quasi-regular-prefix-quotient).
The subtype keeps precisely the original indices of the remaining variables. -/
def quasiRegularQuotientTail {A : Type u} [CommRing A] {b : ℕ}
    (f : Fin b → A) (i : ℕ) : {j : Fin b // i ≤ j.val} → A ⧸ quasiRegularPrefixIdeal f i :=
  fun j ↦ Ideal.Quotient.mk (quasiRegularPrefixIdeal f i) (f j.val)

/-- Quotienting by any prefix preserves the polynomial associated graded structure.
Source: Stacks, Algebra, Tags 061R, 061P and 061N, with `M = A`
(blueprint: lem-pur-quasi-regular-prefix-quotient).

Proof (the eight steps of the node):
1. For the one-generator quotient put t = f_1, B = A/(t), and K equal to the
   remaining-generator ideal. Expanding products gives q(J^n) = K^n, and the
   quotient-kernel calculation gives B/K = A/J
   (`def-weil-pbc-algebra-hom-quotient`).
2. Multiplication by the first variable shifts distinct monomials to distinct
   monomials, hence is injective (`def-weil-pbc-mv-polynomial-ring`). Transport
   through the assumed isomorphism and use the homogeneous product formula of
   `lem-weil-pbc-associated-graded-ring-structure`: if y lies in J^r but not
   J^(r+1), then ty does not lie in J^(r+2).
3. For n ≥ 1 this implies J^n ∩ tA = t J^(n-1). If ty belongs to J^n but y
   does not belong to J^(n-1), take the least failed filtration level m ≤ n-1.
   Step 2 contradicts ty belonging to J^n ⊆ J^(m+1). No separatedness is used.
4. The maps [x]_n ↦ [q(x)]_n are surjective and assemble to a graded algebra
   map rho by the representative formulas of
   `lem-weil-pbc-associated-graded-ring-structure`. Its kernel in degree n
   consists of the classes represented by J^(n+1) + (tA ∩ J^n).
5. By step 3 this kernel is [t]_1 G_(n-1) for n ≥ 1, and zero in degree zero.
   Under the polynomial isomorphism it is precisely the first-variable multiples.
6. Split any homogeneous polynomial as P + T_1 Q, with P involving only the
   remaining variables. This proves surjectivity there. Comparing first exponents
   proves injectivity, over any coefficient ring, including the zero ring.
7. Polynomial uniqueness identifies the restricted composite rho Phi with the
   canonical evaluation map. Finite homogeneous decompositions assemble the
   degreewise bijections; its inverse is an algebra map and preserves degrees.
8. Induct on i. The base i = 0 is the hypothesis. Apply the one-generator result
   over the current prefix quotient. The quotient by the next generator is the
   next prefix quotient, by representatives and kernels. The induced bijections
   on powers and successive quotients preserve the graded algebra operations.
   Both coefficient maps send a to a mod J, giving the specified identification.
   At i = b the remaining ideal is zero; b = 0 is the base case alone.
-/
theorem quasiRegular_prefix_quotient {A : Type u} [CommRing A]
    {b : ℕ} (f : Fin b → A)
    (hpoly : Function.Bijective
      (MvPolynomial.aeval (R := A ⧸ Ideal.span (Set.range f)) (fun j : Fin b ↦
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) 1
          (Submodule.Quotient.mk
            (⟨f j, by simpa using Ideal.subset_span (Set.mem_range_self j)⟩ :
              (Ideal.span (Set.range f) ^ 1 : Ideal A))))))
    (i : ℕ) (hi : i ≤ b) :
    ∃ e : ((A ⧸ quasiRegularPrefixIdeal f i) ⧸
        Ideal.span (Set.range (quasiRegularQuotientTail f i))) ≃+*
          (A ⧸ Ideal.span (Set.range f)),
      (∀ a : A, e (Ideal.Quotient.mk
          (Ideal.span (Set.range (quasiRegularQuotientTail f i)))
          (Ideal.Quotient.mk (quasiRegularPrefixIdeal f i) a)) =
        Ideal.Quotient.mk (Ideal.span (Set.range f)) a) ∧
      Function.Bijective
        (MvPolynomial.aeval
          (R := (A ⧸ quasiRegularPrefixIdeal f i) ⧸
            Ideal.span (Set.range (quasiRegularQuotientTail f i)))
          (fun j : {j : Fin b // i ≤ j.val} ↦
            DirectSum.of
              (associatedGradedPiece (Ideal.span (Set.range (quasiRegularQuotientTail f i))))
              1 (Submodule.Quotient.mk
                (⟨quasiRegularQuotientTail f i j,
                  by simpa using Ideal.subset_span (Set.mem_range_self j)⟩ :
                  (Ideal.span (Set.range (quasiRegularQuotientTail f i)) ^ 1 :
                    Ideal (A ⧸ quasiRegularPrefixIdeal f i)))))) := by
  sorry

end Ideal
