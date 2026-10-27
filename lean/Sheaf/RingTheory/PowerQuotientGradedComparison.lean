module

public import Sheaf.RingTheory.FormallyEtaleAssociatedGraded

/-!
# Canonical graded comparison from ideal-power quotient maps

Source: Stacks Project, Algebra, Tag 0H1D (associated-graded conclusion)
(blueprint: lem-sfb-power-quotient-graded-comparison).

## Main statements

- `Ideal.powerQuotient_graded_comparison` states the canonical quotient and graded
  maps, their scalar compatibility, the isomorphism criterion, and functoriality.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open DirectSum

namespace Ideal

/-- The representative maps on all ideal-power quotients and on the associated graded
ring have the formulas `[a] ↦ [φ a]`.  They are multiplicative and unital, are linear
for the degree-zero quotient action, and become isomorphisms when every positive
power quotient map is bijective.  The same representative formulas prove the stated
naturality, composition, and identity laws.  This is the explicit representative
argument for Stacks Project, Algebra, Tag 0H1D; the quotient and graded constructions
are `powerQuotientMap`, `associatedGradedPieceMap`, and `associatedGradedMap`.

Proof plan: ideal powers are preserved by a ring homomorphism, so the quotient and
piece representative formulas are well defined.  The existing associated-graded
ring structure gives multiplicativity, the unit, and the quotient-scalar formula.
Injectivity of the degree `r` piece follows from injectivity of `Q_(r+1)`: if its
image is zero, the representative lies in `I^(r+1)`.  In degree zero, surjectivity
is that of `Q_1`.  In positive degree `r`, lift a representative in `J^r` using
surjectivity of `Q_(r+1)`.  Its image lies in `J^r` because `J^(r+1) ≤ J^r`;
injectivity of `Q_r` then puts the lift in `I^r`.  The direct sum is injective
componentwise and surjective by choosing preimages on the finite support.  Its inverse
preserves products and one by injectivity, and preserves degree componentwise.  Transport
the quotient scalars along `Q_1`; the scalar formula makes this a graded algebra
isomorphism.  The power and quotient conventions are
`def-weil-pbc-algebra-hom-quotient`, the piece quotients are
`def-weil-pbc-quotient-module`, the finite-support argument is
`def-weil-pbc-direct-sum-modules`, and the product, unit, and scalar formulas are
`lem-weil-pbc-associated-graded-ring-structure`.  All
naturality, composition, and identity claims follow by applying the same formulas to
representatives. (blueprint: lem-sfb-power-quotient-graded-comparison) -/
theorem powerQuotient_graded_comparison
    {A : Type u} {C : Type v} [CommRing A] [CommRing C]
    (φ : A →+* C) (I : Ideal A) (J : Ideal C) (hI : I ≤ J.comap φ) :
    (∀ n : ℕ, 1 ≤ n →
      ∃ Q : A ⧸ I ^ n →+* C ⧸ J ^ n,
        Q = powerQuotientMap φ I J hI n ∧
          ∀ a : A, Q (Ideal.Quotient.mk (I ^ n) a) =
            Ideal.Quotient.mk (J ^ n) (φ a)) ∧
    (∃ G : associatedGraded I →+* associatedGraded J,
      G.toAddMonoidHom = associatedGradedMap φ I J hI ∧
      (∀ (n : ℕ) (x : associatedGradedPiece I n),
        G (DirectSum.of (fun k : ℕ => associatedGradedPiece I k) n x) =
          DirectSum.of (fun k : ℕ => associatedGradedPiece J k) n
            (associatedGradedPieceMap φ I J hI n x)) ∧
      ∀ (a : A) (x : associatedGraded I),
        G ((Ideal.Quotient.mk I a) • x) =
          (Ideal.Quotient.mk J (φ a)) • G x) ∧
    ((∀ n : ℕ, 1 ≤ n →
        Function.Bijective (powerQuotientMap φ I J hI n)) →
      (∀ n : ℕ, Function.Bijective (associatedGradedPieceMap φ I J hI n)) ∧
      ∃ e : associatedGraded I ≃+* associatedGraded J,
        e.toAddMonoidHom = associatedGradedMap φ I J hI ∧
        ∀ (a : A) (x : associatedGraded I),
          e ((Ideal.Quotient.mk I a) • x) =
            (Ideal.Quotient.mk J (φ a)) • e x) ∧
    (∀ {A' : Type w} {C' : Type t} [CommRing A'] [CommRing C']
      (φ' : A' →+* C') (α : A →+* A') (γ : C →+* C')
      (I' : Ideal A') (J' : Ideal C')
      (hI' : I' ≤ J'.comap φ') (hα : I ≤ I'.comap α) (hγ : J ≤ J'.comap γ)
      (hcomm : γ.comp φ = φ'.comp α),
      (∀ n : ℕ, 1 ≤ n →
        (powerQuotientMap γ J J' hγ n).comp (powerQuotientMap φ I J hI n) =
          (powerQuotientMap φ' I' J' hI' n).comp
            (powerQuotientMap α I I' hα n)) ∧
      (associatedGradedMap γ J J' hγ).comp (associatedGradedMap φ I J hI) =
        (associatedGradedMap φ' I' J' hI').comp
          (associatedGradedMap α I I' hα)) ∧
    (∀ {D : Type w} [CommRing D] (K : Ideal C) (L : Ideal D)
      (u : A →+* C) (v : C →+* D) (hu : I ≤ K.comap u) (hv : K ≤ L.comap v),
      (∀ n : ℕ, 1 ≤ n →
        powerQuotientMap (v.comp u) I L (hu.trans (Ideal.comap_mono hv)) n =
          (powerQuotientMap v K L hv n).comp (powerQuotientMap u I K hu n)) ∧
      associatedGradedMap (v.comp u) I L (hu.trans (Ideal.comap_mono hv)) =
        (associatedGradedMap v K L hv).comp (associatedGradedMap u I K hu)) ∧
    (∀ n : ℕ, 1 ≤ n →
      powerQuotientMap (RingHom.id A) I I le_rfl n = RingHom.id (A ⧸ I ^ n)) ∧
    associatedGradedMap (RingHom.id A) I I le_rfl = AddMonoidHom.id (associatedGraded I) := by
  sorry

end Ideal
