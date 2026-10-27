/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-! # Finite polynomial extension and zero-section contraction

Source: Stacks Project, Tag 051P, `lemma-refined-Noether-normalization`, final
extension of the inductively obtained finite map by a variable mapping to a variable.
(blueprint: lem-trf-finite-polynomial-coordinate-lift)

## Main statements

- `Polynomial.finite_mapRingHom_and_comap_zero_section`: specified module generators,
  finiteness, ideal contraction and its constant-term membership criterion.
- `Polynomial.finite_mapAlgHom_and_comap_coordinate_ideal`: the polynomial-coordinate
  specialization, with the last variable represented by the outer polynomial variable.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Polynomial

/-- Extending a finite ring map coefficientwise preserves the specified finite
module generators and contracts the ideal of the zero section by contracting its
coefficient ideal.

Source: Stacks Project, Tag 051P, `lemma-refined-Noether-normalization`, final paragraph.
(blueprint: lem-trf-finite-polynomial-coordinate-lift)

Proof:
1. For any generating list b, expand each coefficient s_i of F as
   sum_j beta(a_ij) b_j (def-weil-finitely-generated-module). Group the finite sums
   by j to obtain F = sum_j map beta (sum_i a_ij Z^i) C(b_j). Polynomial expansion
   and coefficient comparison use def-weil-pbc-mv-polynomial-ring. This proves that
   the same constants generate and hence that the extension is finite.
2. Write any polynomial P as C(P(0)) + T Q by shifting its positive-degree
   coefficients down one degree. Thus P lies in I[T] + (T) if P(0) lies in I.
   Conversely evaluate a sum of ideal generators at zero: constant ideal generators
   give elements of I and T gives zero. This proves the membership criterion.
3. The constant coefficient of map beta H is beta(H(0)). Apply step 2 over S
   with p and over R with comap beta p to obtain both the displayed contraction
   and the elementwise equivalence. Neither primality nor injectivity is used;
   empty generating lists force S to be the zero ring and the same identities hold.
-/
theorem finite_mapRingHom_and_comap_zero_section
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (β : R →+* S) (hβ : β.Finite) (p : Ideal S) :
    (∀ (s : ℕ) (b : Fin s → S),
      (∀ y : S, ∃ a : Fin s → R, ∑ j, β (a j) * b j = y) →
      ∀ F : Polynomial S, ∃ A : Fin s → Polynomial R,
        ∑ j, mapRingHom β (A j) * C (b j) = F) ∧
    (mapRingHom β).Finite ∧
    Ideal.comap (mapRingHom β) (Ideal.map C p ⊔ Ideal.span {X}) =
      Ideal.map C (Ideal.comap β p) ⊔ Ideal.span {X} ∧
    (∀ H : Polynomial R,
      mapRingHom β H ∈ Ideal.map C p ⊔ Ideal.span {X} ↔ β (H.eval 0) ∈ p) := by
  sorry

/-- For two polynomial algebras in m variables, adjoining one last variable to a
finite k-algebra map adds that variable to the contracted coordinate ideal.

The iterated polynomial rings here are k[z_1,...,z_m][z_(m+1)] and
k[y_1,...,y_m][y_(m+1)]. Thus `C (MvPolynomial.X i)` denotes an old variable,
whereas `X` denotes the new last variable. An index i of value r denotes z_(r+1).
`mapAlgHom β` is the canonical coefficientwise k-algebra extension sending X to X.

Source: Stacks Project, Tag 051P, `lemma-refined-Noether-normalization`, final paragraph.
(blueprint: lem-trf-finite-polynomial-coordinate-lift)

Proof:
4. Group each monomial by its exponent in the last variable to identify the
   (m+1)-variable polynomial rings with the displayed iterated polynomial rings
   (def-weil-pbc-mv-polynomial-ring). Apply steps 1--3 above to beta.toRingHom.
   Substitute the given coordinate contraction. Extension of the span of old
   variables is the span of their constants; adding (X) gives the displayed
   span of the union with the last variable. This also covers m = 0 and r = m,
   when the old-variable list is empty, and does not require p to be prime.
-/
theorem finite_mapAlgHom_and_comap_coordinate_ideal
    {k : Type u} [Field k] (m r : ℕ) (hr : r ≤ m)
    (β : MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k)
    (hβ : β.Finite) (p : Ideal (MvPolynomial (Fin m) k))
    (hp : Ideal.comap β.toRingHom p =
      Ideal.span (MvPolynomial.X '' {i : Fin m | r ≤ i.val})) :
    (mapAlgHom β).Finite ∧
    Ideal.comap (mapAlgHom β).toRingHom (Ideal.map C p ⊔ Ideal.span {X}) =
      Ideal.span (insert X
        ((fun i : Fin m ↦ C (MvPolynomial.X i)) '' {i : Fin m | r ≤ i.val})) := by
  sorry

end Polynomial
