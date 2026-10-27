module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.Ideal.Over
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.QuotientBaseChangeIdeal
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-!
# Lifting an étale neighbourhood across a nilpotent base quotient

Source: Stacks Project, Algebraization of Formal Spaces, Tag 0ALT, lemma-lift-approximation
(blueprint: lem-per-nilpotent-etale-neighbourhood-pushout-lift).

All quotients, algebra structures, spectra and restrictions are Mathlib constructions.
The quotient isomorphism hypothesis is characterized on the images of elements of `B₀`;
the prescribed reduction in the conclusion is characterized on elements of `B`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Lift an étale neighbourhood with its prescribed reduction through a nilpotent base ideal.
Source: Stacks Project, Tag 0ALT, lemma-lift-approximation
(blueprint: lem-per-nilpotent-etale-neighbourhood-pushout-lift).

Proof:
1. Write X = Spec A, X₀ = Spec (A/J), Z = Spec C, Z₀ = Spec (C/JC), Y₀ = Spec B₀.
   Let U be the complement of V(I), and use subscripts for the corresponding open parts.
   Quotient base change identifies Z₀ with Z over X₀
   (lem-weil-pbc-quotient-base-change-closed-immersion-ideal). Nilpotence makes X₀ → X a
   thickening, and the same holds after base change (lem-sfb-space-thickening-base-change).
   The given étale map and quotient isomorphism make the square W₀, Z₀, V₀, Y₀ elementary
   distinguished: its étale leg is an isomorphism over the reduced closed complement.
2. Lift the étale U₀-scheme V₀ to V over U by thickening invariance and lift W₀ → V₀
   uniquely to q : W → V (lem-sfb-space-thickening-etale-scheme-equivalence).
   Étale cancellation makes q étale (lem-weil-pbc-etale-composition-cancellation).
3. The affine morphism Z₀ → Y₀ is separated, hence so is its base change W₀ → V₀
   (lem-weil-pbc-affine-source-morphism-separated, lem-weil-pbc-separated-base-change).
   Invariance under thickenings makes q separated as well
   (lem-sfb-space-thickening-topological-properties).
4. Form the algebraic-space pushout of W → Z and q : W → V
   (lem-per-open-separated-etale-pushout). Its base change to X₀ and the original square
   are both pushouts, so uniqueness gives a specified isomorphism Y over X₀ ≅ Y₀,
   compatible with Z₀ (lem-per-elementary-distinguished-universal-pushout).
5. The base change Y₀ → Y is a closed thickening. It is finite on scheme tests
   (lem-weil-pbc-closed-immersion-finite) and surjective; its affine source implies that
   Y is affine (lem-sfb-finite-surjective-affine-space-target). Write Y = Spec B.
6. Affine contravariance and quotient base change give h and β with the asserted
   commutation. Scheme étaleness agrees with the chartwise condition
   (lem-trf-space-chartwise-etale-permanence), so h is étale. Lift finitely many algebra
   generators of B₀ to B and let D be their A-subalgebra. Then B = D + JB; inductively
   B = D + JⁿB. Nilpotence gives B = D, proving finite type, also for no generators.
7. Base change the pushout to U. Its span is W ← W → V with identity left leg, so its
   pushout is V (lem-per-elementary-distinguished-universal-pushout). Thus Y over U is
   V, and is étale over U, as required. -/
theorem exists_nilpotent_etale_neighbourhood_pushout_lift
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
    (hJ : ∃ N : ℕ, 1 ≤ N ∧ J ^ N = ⊥)
    (C : Type u) [CommRing C] [Algebra A C]
    (hCft : (algebraMap A C).FiniteType)
    (B₀ : Type u) [CommRing B₀] [Algebra (A ⧸ J) B₀]
    (hB₀ft : (algebraMap (A ⧸ J) B₀).FiniteType)
    (hC : Etale ((Spec.map (CommRingCat.ofHom (algebraMap A C))) ∣_
      ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
        (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩))
    (hB₀ : Etale ((Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ J) B₀))) ∣_
      ⟨(PrimeSpectrum.zeroLocus (I.map (Ideal.Quotient.mk J) : Set (A ⧸ J)))ᶜ,
        (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩))
    (h₀ : B₀ →ₐ[A ⧸ J] C ⧸ J.map (algebraMap A C))
    (hh₀ : Etale (Spec.map (CommRingCat.ofHom h₀.toRingHom)))
    (hI : ∃ e :
        (B₀ ⧸ (I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) B₀)) ≃ₐ[A ⧸ J]
          ((C ⧸ J.map (algebraMap A C)) ⧸
            (I.map (Ideal.Quotient.mk J)).map
              (algebraMap (A ⧸ J) (C ⧸ J.map (algebraMap A C)))),
      ∀ b : B₀, e (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (h₀ b)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      (algebraMap A B).FiniteType ∧
      ∃ (h : B →ₐ[A] C) (β : (B ⧸ J.map (algebraMap A B)) ≃ₐ[A ⧸ J] B₀),
        Etale (Spec.map (CommRingCat.ofHom h.toRingHom)) ∧
        (∀ b : B, Ideal.Quotient.mk (J.map (algebraMap A C)) (h b) =
          h₀ (β (Ideal.Quotient.mk (J.map (algebraMap A B)) b))) ∧
        Etale ((Spec.map (CommRingCat.ofHom (algebraMap A B))) ∣_
          ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
            (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩) := by
  sorry

end AlgebraicGeometry
