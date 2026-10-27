module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.RingTheory.PrimeLocalizationEtaleAlgebraModel
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Defs
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Etale.Basic

/-! # Globalizing a pointed étale polynomial solution

Source: Stacks Project, Tag 0CAR, proof of lemma-approximation-property-variant,
last paragraph (blueprint: lem-trf-pointed-etale-polynomial-solution-globalization).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite polynomial solution in an étale algebra over a prime localization spreads
out to an étale algebra over the original ring, with the canonical pointed local-ring
isomorphism and its induced residue-field isomorphism. The displayed commutation identity
with `Localization.localRingHom p.asIdeal p'.asIdeal a hp'` expresses linearity over
`Localization.AtPrime p.asIdeal` for the canonical algebra structures.

Source: Stacks Project, Tag 0CAR, proof of lemma-approximation-property-variant,
last paragraph (blueprint: lem-trf-pointed-etale-polynomial-solution-globalization).

Proof:
1. Apply `new-lem-sbc-prime-localization-etale-algebra-model` to obtain an étale
   A-algebra C and a map C → E realizing E as an M-localization of C. This uses only
   the given étaleness, with no Noetherian or G-ring hypothesis.
2. By `lem-weil-pbc-localization-of-localization`, represent each c_i as u_i/v_i.
   Put d = ∏ v_i, D = C[1/d], and x_i = u_i(∏_{k ≠ i} v_k)/d. The universal property
   `lem-weil-pbc-ring-localization-universal-property` extends C → E to D → E,
   carrying x_i to c_i; localization-of-localization makes this another localization.
   For n = 0 use d = 1 and the empty tuple.
3. Each f_j(x) maps to zero in E. The localization kernel criterion supplies a
   denominator w_j annihilating f_j(x). Set t = ∏ w_j and A' = D[1/t]. The images b_i
   now satisfy all equations. For m = 0 use t = 1. This uses no cancellation.
4. Since t maps to a unit, the localization universal property extends D → E to
   j : A' → E and gives j(b_i) = c_i. Localization-of-localization makes j a
   localization. Applying `lem-weil-pbc-etale-algebra-finite-presentation-localization`
   twice shows that D and A' are étale over A.
5. Apply `lem-weil-pbc-localization-prime-residue-field-iso` to j and q. It gives
   p' = j⁻¹(q), the canonical local-ring isomorphism θ, and its induced residue-field
   isomorphism. The contraction of q to A_p is its maximal ideal, whose contraction
   to A is p, so p' contracts to p (`def-weil-pbc-localization-at-prime`).
6. The canonical map A_p → A'_p' exists because p' contracts to p. Both maps
   A_p → E_q extend the same map from A, so localization uniqueness gives the
   displayed commutation identity for θ. Its fraction formula gives θ(b_i/1) = c_i/1.
   Passing to residue fields gives the identity over κ(p) for the induced
   `IsLocalRing.ResidueField.mapEquiv θ`, with the original structural map to κ(q).
-/
theorem pointedEtalePolynomialSolutionGlobalization
    (A E : CommRingCat.{u}) (p : PrimeSpectrum A)
    (α : Localization.AtPrime p.asIdeal →+* E)
    (hα : Etale (Spec.map (CommRingCat.ofHom α)))
    (q : PrimeSpectrum E)
    (hq : IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) = q.asIdeal.comap α)
    (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) A) (c : Fin n → E)
    (hc : ∀ k, MvPolynomial.eval₂
      (α.comp (algebraMap A (Localization.AtPrime p.asIdeal))) c (f k) = 0) :
    ∃ (A' : CommRingCat.{u}) (a : A →+* A') (j : A' →+* E) (b : Fin n → A'),
      Etale (Spec.map (CommRingCat.ofHom a)) ∧
      j.comp a = α.comp (algebraMap A (Localization.AtPrime p.asIdeal)) ∧
      (∀ k, MvPolynomial.eval₂ a b (f k) = 0) ∧
      (∀ i, j (b i) = c i) ∧
      ∃ (p' : PrimeSpectrum A') (hpq : p'.asIdeal = q.asIdeal.comap j)
        (hp' : p.asIdeal = p'.asIdeal.comap a),
        ∃ θ : Localization.AtPrime p'.asIdeal ≃+* Localization.AtPrime q.asIdeal,
          θ.toRingHom = Localization.localRingHom p'.asIdeal q.asIdeal j hpq ∧
          θ.toRingHom.comp (Localization.localRingHom p.asIdeal p'.asIdeal a hp') =
            (algebraMap E (Localization.AtPrime q.asIdeal)).comp α ∧
          (∀ i, θ (algebraMap A' (Localization.AtPrime p'.asIdeal) (b i)) =
            algebraMap E (Localization.AtPrime q.asIdeal) (c i)) ∧
          (IsLocalRing.ResidueField.mapEquiv θ).toRingHom.comp
              (Ideal.ResidueField.map p.asIdeal p'.asIdeal a hp') =
            Ideal.ResidueField.map p.asIdeal q.asIdeal
              (α.comp (algebraMap A (Localization.AtPrime p.asIdeal)))
              ((Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)).symm.trans
                ((congrArg (Ideal.comap (algebraMap A (Localization.AtPrime p.asIdeal)))
                  hq).trans (Ideal.comap_comap _ _))) := by
  sorry

end AlgebraicGeometry.Scheme
