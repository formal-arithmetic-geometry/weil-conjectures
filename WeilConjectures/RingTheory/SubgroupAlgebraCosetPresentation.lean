/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.AdjoinRoot

/-! # Coset bases and subgroup group-algebra presentations

Source: Milne, Algebraic Groups (2017), Theorem 12.9(b), pp.233–234, with the relative
coset and Laurent normal-form strengthening in the DAG proof
(blueprint: lem-sfb-subgroup-algebra-coset-presentation).

Laurent polynomials are group algebras of integer exponent vectors. The normalization on
all coefficient monomials specifies the displayed evaluation and the base-change map uniquely.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AddMonoidAlgebra

/-- The scalar action given by the subgroup inclusion, not the base-ring scalar action.
Source: Milne, Theorem 12.9(b), relative coset calculation, DAG proof step 1
(blueprint: lem-sfb-subgroup-algebra-coset-presentation). -/
noncomputable instance subgroupAlgebra (R : Type u) [CommRing R]
    {M : Type v} [AddCommGroup M] (L : AddSubgroup M) :
    Algebra (AddMonoidAlgebra R L) (AddMonoidAlgebra R M) :=
  (mapDomainRingHom R L.subtype).toAlgebra

/-- The finite Laurent ring over R[L], with one integer exponent for each X and Y.
Source: Milne, Theorem 12.9(b), relative strengthening, DAG proof steps 4–5
(blueprint: lem-sfb-subgroup-algebra-coset-presentation). -/
abbrev subgroupLaurentRing (R : Type u) [CommRing R]
    {M : Type v} [AddCommGroup M] (L : AddSubgroup M) (r s : ℕ) :=
  AddMonoidAlgebra (AddMonoidAlgebra R L) ((Fin r ⊕ Fin s) → ℤ)

/-- The binomial relation ideal (Y_j^d_j - e_(l_j)) in the Laurent ring.
Source: Milne, Theorem 12.9(b), relative strengthening, DAG proof steps 4–5
(blueprint: lem-sfb-subgroup-algebra-coset-presentation). -/
noncomputable def subgroupLaurentRelations (R : Type u) [CommRing R]
    {M : Type v} [AddCommGroup M] (L : AddSubgroup M) (r s : ℕ)
    (d : Fin s → ℕ) (l : Fin s → L) : Ideal (subgroupLaurentRing R L r s) :=
  Ideal.span (Set.range (fun j : Fin s ↦
    single (Pi.single (Sum.inr j) (d j : ℤ)) (1 : AddMonoidAlgebra R L) -
      single 0 (single (l j) (1 : R))))

/-- The literal Laurent quotient in the subgroup presentation.
Source: Milne, Theorem 12.9(b), relative strengthening, DAG proof steps 4–5
(blueprint: lem-sfb-subgroup-algebra-coset-presentation). -/
abbrev subgroupLaurentQuotient (R : Type u) [CommRing R]
    {M : Type v} [AddCommGroup M] (L : AddSubgroup M) (r s : ℕ)
    (d : Fin s → ℕ) (l : Fin s → L) :=
  subgroupLaurentRing R L r s ⧸ subgroupLaurentRelations R L r s d l

/-- Normalization of the displayed isomorphism on every Laurent coefficient monomial.
In particular coefficients follow the subgroup inclusion and X_i,Y_j go to e_(a_i),e_(b_j).
Source: Milne, Theorem 12.9(b), relative strengthening, DAG proof step 6
(blueprint: lem-sfb-subgroup-algebra-coset-presentation). -/
def IsSubgroupLaurentEvaluation {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] (L : AddSubgroup M) (r s : ℕ)
    (d : Fin s → ℕ) (l : Fin s → L) (a : Fin r → M) (b : Fin s → M)
    (e : subgroupLaurentQuotient R L r s d l ≃ₐ[AddMonoidAlgebra R L]
      AddMonoidAlgebra R M) : Prop :=
  ∀ (n : (Fin r ⊕ Fin s) → ℤ) (c : AddMonoidAlgebra R L),
    e (Ideal.Quotient.mk (subgroupLaurentRelations R L r s d l) (single n c)) =
      mapDomainRingHom R L.subtype c *
        single ((∑ i : Fin r, n (Sum.inl i) • a i) +
          ∑ j : Fin s, n (Sum.inr j) • b j) 1

/-- Coefficient base change fixes every exponent and every group index.
Source: Milne, Theorem 12.9(b), relative strengthening, DAG proof step 8
(blueprint: lem-sfb-subgroup-algebra-coset-presentation). -/
def IsSubgroupLaurentBaseChange {R : Type u} [CommRing R]
    {R' : Type w} [CommRing R'] {M : Type v} [AddCommGroup M]
    (L : AddSubgroup M) (r s : ℕ) (d : Fin s → ℕ) (l : Fin s → L) (f : R →+* R')
    (g : subgroupLaurentQuotient R L r s d l →+*
      subgroupLaurentQuotient R' L r s d l) : Prop :=
  ∀ (n : (Fin r ⊕ Fin s) → ℤ) (c : AddMonoidAlgebra R L),
    g (Ideal.Quotient.mk (subgroupLaurentRelations R L r s d l) (single n c)) =
      Ideal.Quotient.mk (subgroupLaurentRelations R' L r s d l)
        (single n (mapRingHom L f c))

/-- Subgroup inclusion is injective, arbitrary coset representatives give a basis, and a
finitely generated quotient gives the stated binomial Laurent presentation, finite presentation,
and compatibility with every coefficient ring homomorphism.

Source: Milne, Algebraic Groups (2017), Theorem 12.9(b), pp.233–234; the relative strengthening
and its complete normal-form proof are in the DAG
(blueprint: lem-sfb-subgroup-algebra-coset-presentation).

Proof: (1) The inclusion simply reindexes distinct basis elements, hence is injective.
(2) The bijection L × (M/L) → M, (l,c) ↦ l+t_c, regroups each finite sum uniquely, giving
exactly the claimed basis without a finiteness assumption on M/L.
(3) The finitely generated abelian group structure theorem gives a free part and cyclic
factors; discard trivial factors and lift their generators. The bounded cyclic exponents,
together with arbitrary integer free exponents, give one representative of every coset.
(4) Handle the zero ring separately. Otherwise iterating the monic quotient power basis for
Y_j^d_j-e_(l_j) gives the basis with 0 ≤ q_j < d_j over the free-variable Laurent ring.
(5) Each Y_j becomes invertible, with inverse e_(-l_j) Y_j^(d_j-1). Thus the iterated monic
quotient is the displayed Laurent quotient, with basis X^n Y^q.
(6) Evaluation sends this basis to the coset basis of (2), so is an algebra isomorphism.
(7) Replace every Laurent variable by two polynomial variables with product-one relation.
There are 2(r+s) variables and r+2s relations, proving finite presentation, including r=s=0.
(8) Applying any coefficient map fixes all exponents and group indices, carries each relation
to the identically indexed relation, and commutes with evaluation. Repeat the same normal
form over the new ring, including the zero ring. This gives the asserted commuting square;
no torsion cancellation or inversion of d_j is used. -/
theorem subgroup_algebra_coset_presentation (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] (L : AddSubgroup M) :
    Function.Injective (mapDomainRingHom R L.subtype) ∧
    (∀ (t : M ⧸ L → M), (∀ c : M ⧸ L, (t c : M ⧸ L) = c) →
      ∃ B : Module.Basis (M ⧸ L) (AddMonoidAlgebra R L) (AddMonoidAlgebra R M),
        ∀ c : M ⧸ L, B c = single (t c) 1) ∧
    (AddGroup.FG (M ⧸ L) →
      Algebra.FinitePresentation (AddMonoidAlgebra R L) (AddMonoidAlgebra R M) ∧
      ∀ (r s : ℕ) (d : Fin s → ℕ), (∀ j : Fin s, 2 ≤ d j) →
      ∀ (D : (M ⧸ L) ≃+ ((Fin r → ℤ) × ((j : Fin s) → ZMod (d j))))
        (a : Fin r → M) (b : Fin s → M),
      (∀ i : Fin r, D (a i : M ⧸ L) = (Pi.single i 1, 0)) →
      (∀ j : Fin s, D (b j : M ⧸ L) = (0, Pi.single j 1)) →
      ∀ l : Fin s → L, (∀ j : Fin s, (l j : M) = d j • b j) →
      ∃ e : subgroupLaurentQuotient R L r s d l ≃ₐ[AddMonoidAlgebra R L]
          AddMonoidAlgebra R M,
        IsSubgroupLaurentEvaluation L r s d l a b e ∧
        ∀ (R' : Type w) [CommRing R'] (f : R →+* R'),
          ∃ e' : subgroupLaurentQuotient R' L r s d l ≃ₐ[AddMonoidAlgebra R' L]
              AddMonoidAlgebra R' M,
            IsSubgroupLaurentEvaluation L r s d l a b e' ∧
            ∃ g : subgroupLaurentQuotient R L r s d l →+*
                subgroupLaurentQuotient R' L r s d l,
              IsSubgroupLaurentBaseChange L r s d l f g ∧
              ∀ x : subgroupLaurentQuotient R L r s d l,
                e' (g x) = mapRingHom M f (e x)) := by
  sorry

end AddMonoidAlgebra
