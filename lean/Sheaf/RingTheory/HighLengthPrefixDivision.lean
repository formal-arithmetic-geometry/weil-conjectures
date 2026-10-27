/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.RingTheory.PositiveMonoidConvolutionLength
public import Mathlib.Data.Fintype.Pi

/-!
# Finite-prefix division of high-length monoid series

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70 (PDF p. 76), formal monoid models; the auxiliary coefficient argument
in the DAG, not a theorem asserted in ILO
(blueprint: lem-trf-high-length-prefix-division).
-/

@[expose] public section

universe u v

namespace AddMonoidAlgebra

/-- The exponent `s_I` of a generator prefix.

Source: ILO, Exposé VI, §1.6(i)–(ii), formal monoid models; auxiliary coefficient
argument, old steps 6–7 (blueprint: lem-trf-high-length-prefix-division).
-/
def positiveMonoid_prefixSum {G : Type u} [AddCommGroup G] {P : AddSubmonoid G}
    {s n : ℕ} (g : Fin s → P) (I : Fin n → Fin s) : P :=
  ∑ j, g (I j)

/-- The high-length exponents for which `I` is the first eligible prefix.
Eligibility is subtraction in the ambient group, with the difference in `P`.
The fixed total order `ord` is passed explicitly: the pointwise order on functions
is not a total order and must not be used here.

Source: ILO, Exposé VI, §1.6(i)–(ii), formal monoid models; auxiliary coefficient
argument, old steps 6–7 (blueprint: lem-trf-high-length-prefix-division).
-/
def positiveMonoid_prefixCell {G : Type u} [AddCommGroup G] {P : AddSubmonoid G}
    (ν : P → ℕ) {s : ℕ} (g : Fin s → P) (n : ℕ)
    (ord : LinearOrder (Fin n → Fin s)) (I : Fin n → Fin s) : Set P :=
  {p | n ≤ ν p ∧ (p : G) - (positiveMonoid_prefixSum g I : G) ∈ P ∧
    ∀ J : Fin n → Fin s, (p : G) - (positiveMonoid_prefixSum g J : G) ∈ P →
      @LE.le (Fin n → Fin s) ord.toLE I J}

open Classical in
/-- The unrestricted residual family `c^I`, shifted back from the cell `E_I`.

Source: ILO, Exposé VI, §1.6(i)–(ii), formal monoid models; auxiliary coefficient
argument, old steps 6–7 (blueprint: lem-trf-high-length-prefix-division).
-/
noncomputable def positiveMonoid_prefixResidual
    {G : Type u} [AddCommGroup G] {P : AddSubmonoid G}
    {A : Type v} [CommRing A] (ν : P → ℕ) {s : ℕ} (g : Fin s → P) (n : ℕ)
    (ord : LinearOrder (Fin n → Fin s)) (a : P → A) (I : Fin n → Fin s) : P → A :=
  fun q ↦ if positiveMonoid_prefixSum g I + q ∈ positiveMonoid_prefixCell ν g n ord I
    then a (positiveMonoid_prefixSum g I + q) else 0

open Classical in
/-- The first eligible prefixes partition the high-length exponents and divide
any coefficient family into a finite sum of monomial shifts.

Source: ILO, Exposé VI, §1.6(i)–(ii), printed p. 70 (PDF p. 76), formal monoid
models; auxiliary coefficient argument, old steps 6–7
(blueprint: lem-trf-high-length-prefix-division).

`ν` and `ring` are the length and convolution ring characterized by
`positiveMonoid_convolution_length`. The generators are bundled as elements of
`P`; their ambient images generate exactly `P`. The four operation formulas
specify the convolution ring rather than the pointwise multiplication on functions.
The ring `ring` and the order `ord` are explicit arguments and are used through `@`:
as instance arguments they would be shadowed by the global pointwise `Pi` instances,
so every product, unit, zero, finite sum and finite product on `P → A` below is
that of `ring`. The arbitrary linear order on `Fin n → Fin s` is the fixed order in the node.
The high-length tail is the displayed function, and the cells and residual families
are the explicit definitions above. Neither `a` nor a residual has restricted support.

Proof plan:
1. By `lem-trf-positive-monoid-convolution-length`, the maximal length is attained.
   For `ν p ≥ n`, choose a decomposition into `ν p` nonzero summands.
2. Expand each summand into generators using `hgen`. Each generator word is
   nonempty because that summand is nonzero. Concatenation has at least `n`
   letters; its first `n` letters give `I`, and the remaining sum gives `q`.
3. The finite set of eligible tuples is nonempty by step 2. Its unique least
   member places each high-length exponent in exactly one cell. No other
   exponent lies in a cell, proving disjointness and the union identity.
4. Use the monomial shift formula from
   `lem-trf-positive-monoid-convolution-length`. At `p = s_I + q` the coefficient
   is the residual at `q`, namely `a p` on the cell and zero off it. If no such
   `q` exists, the coefficient is zero and the exponent is outside the cell.
   Cancellation in `G` gives uniqueness of the residual exponent.
5. Addition is componentwise. Exactly one summand contributes `a p` on the
   high-length set, and all summands vanish elsewhere. Function extensionality
   proves the finite-sum identity; no convergence is involved.
6. Induct on the prefix length using `z^u * z^v = z^(u+v)` from
   `lem-trf-positive-monoid-convolution-length` to obtain the monomial product.
7. If `s = 0`, generation gives `P = {0}`. Since `ν 0 = 0` and `n ≥ 1`, the
   high-length set is empty. There are no positive-length tuples on the empty
   alphabet. Thus the tail and its empty sum are zero; individual cells are vacuous.
-/
theorem positiveMonoid_high_length_prefix_division
    (G : Type u) [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G]
    (P : AddSubmonoid G) (s : ℕ) (g : Fin s → P)
    (hg : ∀ i : Fin s, g i ≠ 0)
    (hgen : AddSubmonoid.closure (Set.range (fun i : Fin s ↦ (g i : G))) = P)
    (wgt : G →+ ℤ) (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (p : G))
    (A : Type v) [CommRing A] (ring : CommRing (P → A))
    (hzero : ∀ p : P, (@Zero.zero (P → A) ring.toZero) p = 0)
    (hone : (@One.one (P → A) ring.toOne) = Pi.single (0 : P) (1 : A))
    (hadd : ∀ (a c : P → A) (p : P), (@Add.add (P → A) ring.toAdd a c) p = a p + c p)
    (hmul : ∀ (a c : P → A) (p : P), (@Mul.mul (P → A) ring.toMul a c) p =
      ∑ᶠ q : {q : P × P // q.1 + q.2 = p}, a q.1.1 * c q.1.2)
    (ν : P → ℕ)
    (hν : ∀ p : P, IsGreatest {l : ℕ | ∃ f : Fin l → P,
      (∀ j : Fin l, f j ≠ 0) ∧ (∑ j, f j) = p} (ν p))
    (hνzero : ν 0 = 0) (n : ℕ) (hn : 1 ≤ n) (ord : LinearOrder (Fin n → Fin s)) :
    (∀ p : P, n ≤ ν p → ∃ (I : Fin n → Fin s) (q : P),
      p = positiveMonoid_prefixSum g I + q) ∧
    (∀ I J : Fin n → Fin s, I ≠ J → Disjoint (positiveMonoid_prefixCell ν g n ord I)
      (positiveMonoid_prefixCell ν g n ord J)) ∧
    (⋃ I : Fin n → Fin s, positiveMonoid_prefixCell ν g n ord I) = {p : P | n ≤ ν p} ∧
    (∀ (a : P → A) (I : Fin n → Fin s) (p : P),
      (@Mul.mul (P → A) ring.toMul (Pi.single (positiveMonoid_prefixSum g I) (1 : A))
        (positiveMonoid_prefixResidual ν g n ord a I)) p =
          if p ∈ positiveMonoid_prefixCell ν g n ord I then a p else 0) ∧
    (∀ a : P → A, (fun p ↦ if n ≤ ν p then a p else 0) =
      @Finset.sum (Fin n → Fin s) (P → A) ring.toAddCommMonoid Finset.univ (fun I ↦
        @Mul.mul (P → A) ring.toMul (Pi.single (positiveMonoid_prefixSum g I) (1 : A))
          (positiveMonoid_prefixResidual ν g n ord a I))) ∧
    (∀ I : Fin n → Fin s, (Pi.single (positiveMonoid_prefixSum g I) (1 : A) : P → A) =
      @Finset.prod (Fin n) (P → A) ring.toCommMonoid Finset.univ
        (fun j ↦ Pi.single (g (I j)) (1 : A))) ∧
    (s = 0 → P = ⊥ ∧ {p : P | n ≤ ν p} = ∅ ∧ IsEmpty (Fin n → Fin s) ∧
      ∀ a : P → A, (fun p ↦ if n ≤ ν p then a p else 0) = @Zero.zero (P → A) ring.toZero ∧
        @Finset.sum (Fin n → Fin s) (P → A) ring.toAddCommMonoid Finset.univ (fun I ↦
          @Mul.mul (P → A) ring.toMul (Pi.single (positiveMonoid_prefixSum g I) (1 : A))
            (positiveMonoid_prefixResidual ν g n ord a I)) = @Zero.zero (P → A) ring.toZero) := by
  sorry

end AddMonoidAlgebra
