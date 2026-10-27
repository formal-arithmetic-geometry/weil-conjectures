module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct

/-! # Conjugacy of normalized branches over a complete normal base extension

Source: Stacks Project, More on Algebra, Tags 09EU and 09F8
(blueprint: lem-sfb-epp-normal-base-branch-conjugacy).

The actions and the normalization map are characterized inside the ambient fields and
reduced tensor algebra. All rings below are the actual Mathlib integral closures and
quotient by the nilradical, rather than unspecified normalization models.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- A finite normal, possibly inseparable, extension gives conjugate normalized branches
and a common ramification index for a local injection of complete DVRs.

Source: Stacks Project, More on Algebra, Tag 09EU, lemma-galois-relative, and Tag 09F8,
lemma-special-case (blueprint: lem-sfb-epp-normal-base-branch-conjugacy).

Proof:
1. Apply lem-sfb-dvr-algebraic-normalization-structure in its finite case to decompose
   the reduced tensor into a nonempty finite product of finite extensions of L.
   A DVR is Noetherian (lem-weil-pbc-pid-noetherian-normal), and a complete local
   Noetherian ring is Nagata (lem-weil-pbc-complete-local-nagata). By
   def-weil-pbc-nagata-ring and def-weil-pbc-japanese-domain its integral closures in
   these fields are finite. Apply lem-weil-pbc-finite-over-complete-local-product:
   each domain factor is local and complete. By lem-sc-dvr-dimension-one and
   lem-sfb-finite-normalization-local-dvr, each factor and the lower closure are DVRs.
   The upper closure is the product of the factor closures: project a monic equation
   in one direction and multiply the finitely many coordinate monic equations in the
   other. Its maximal ideals are the coordinate maximal ideals; they contract to the
   unique lower maximal ideal. The localized normalization maps are local injections.
2. The tensor universal property (lem-weil-pbc-algebra-tensor-pushout-universal-property)
   gives the action 1 tensor sigma and its inverse. Automorphisms preserve nilpotents,
   so it descends to the reduction. Applying an automorphism to a monic equation
   restricts these actions to the integral closures. Their square with the canonical
   normalization map commutes. Each lower automorphism fixes its unique maximal ideal.
3. The automorphisms permute the primitive coordinate idempotents. If there were two
   orbits, the characteristic idempotent of one orbit would be invariant and different
   from zero and one. By lem-sfb-normal-tensor-invariant-powers, a positive power of it
   comes from L. It equals that power, hence is a scalar idempotent. The map from L to
   the nonzero reduced tensor is injective, so it must be zero or one, a contradiction.
   The coordinate maximal ideals of the upper closure are therefore conjugate.
4. For sigma sending q to q', localize to the isomorphism b/s maps to sigma(b)/sigma(s).
   It sends the extended lower maximal ideal and the localized upper maximal ideal
   to their counterparts. For lower and upper uniformizers a,t, the image of a is a
   nonzero nonunit; lem-weil-pbc-dvr-unit-times-uniformizer-power writes it as u*t^e
   with e positive. This exponent is unique: equality of two powers of the principal
   maximal ideal, followed by cancellation, would otherwise make t a unit. Transport
   this ideal equality along the localization isomorphism. Thus e is independent of
   the maximal ideal, and e=1 at one branch implies e=1 at every branch.

The first four existential maps are pinned by their displayed formulas; in particular
neither the group action nor the lower-to-upper map is an arbitrary choice. The ideal m
is characterized as the unique maximal ideal of the lower closure. -/
theorem epp_normal_base_branch_conjugacy
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type v) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type x) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    (E : Type y) [Field E] [Algebra K E] [FiniteDimensional K E] [Normal K E]
    [Algebra A E] [IsScalarTower A K E] :
    ∃ (lowerAction : (E ≃ₐ[K] E) →*
        (integralClosure A E ≃+* integralClosure A E))
      (tensorAction : (E ≃ₐ[K] E) →*
        (((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) ≃+*
          ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))))
      (upperAction : (E ≃ₐ[K] E) →*
        (integralClosure B ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) ≃+*
          integralClosure B ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))))
      (f : integralClosure A E →+*
        integralClosure B ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))),
      (∀ (σ : E ≃ₐ[K] E) (a : integralClosure A E),
        (lowerAction σ a : E) = σ (a : E)) ∧
      (∀ (σ : E ≃ₐ[K] E) (l : L) (a : E),
        tensorAction σ (Ideal.Quotient.mk _ (l ⊗ₜ[K] a)) =
          Ideal.Quotient.mk _ (l ⊗ₜ[K] σ a)) ∧
      (∀ (σ : E ≃ₐ[K] E)
          (b : integralClosure B ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))),
        (upperAction σ b : (L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) =
          tensorAction σ (b : (L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))) ∧
      (∀ a : integralClosure A E,
        (f a : (L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) =
          Ideal.Quotient.mk _ ((1 : L) ⊗ₜ[K] (a : E))) ∧
      (∀ (σ : E ≃ₐ[K] E) (a : integralClosure A E),
        upperAction σ (f a) = f (lowerAction σ a)) ∧
      (∀ (q q' : Ideal
          (integralClosure B ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)))),
        q.IsMaximal → q'.IsMaximal →
          ∃ σ : E ≃ₐ[K] E, Ideal.map (upperAction σ).toRingHom q = q') ∧
      ∃ m : Ideal (integralClosure A E),
        m.IsMaximal ∧
        (∀ n : Ideal (integralClosure A E), n.IsMaximal → n = m) ∧
        (∀ σ : E ≃ₐ[K] E, Ideal.map (lowerAction σ).toRingHom m = m) ∧
        ∃ e : ℕ, 0 < e ∧
          (∀ (q : Ideal
              (integralClosure B ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))))
              [q.IsMaximal],
            ∀ n : ℕ,
              Ideal.map ((algebraMap _ (Localization.AtPrime q)).comp f) m =
                (Ideal.map (algebraMap _ (Localization.AtPrime q)) q) ^ n ↔ n = e) ∧
          ((∃ (q : Ideal
              (integralClosure B ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))))
              (_ : q.IsMaximal),
            Ideal.map ((algebraMap _ (Localization.AtPrime q)).comp f) m =
              Ideal.map (algebraMap _ (Localization.AtPrime q)) q) → e = 1) := by
  sorry

end IsDiscreteValuationRing
