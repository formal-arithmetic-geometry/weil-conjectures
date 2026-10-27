module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.RingTheory.CompletionMapForLocalHom
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.AlgebraicGeometry.SmoothSectionEtaleLift

/-!
# Étale approximation of a smooth formal point

Source: Stacks Project, Smoothing Ring Maps, Tag 07QZ, smooth-factorization paragraph;
More on Algebra, Tag 07M7, applied modulo a prescribed maximal-ideal power
(blueprint: lem-trf-smooth-formal-point-etale-approximation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A smooth formal point has an étale approximation at every positive precision.
The quotient algebra map `α` is necessarily the structural map. The equation for `ρ`
likewise fixes the structural residue-field isomorphism. The local ring is the actual
localization at `q`, and the completion map is the unique coordinatewise map supplied
by `RingHom.exists_adicCompletion_map_of_local`.

Source: Stacks Project, Tag 07QZ, smooth-factorization paragraph, refined using Tag 07M7
with the ideal `m ^ N`, and Algebra, Tag 05GG (2)
(blueprint: lem-trf-smooth-formal-point-etale-approximation).

Proof:
1. Apply `lem-weil-pbc-smooth-section-etale-lift` to `J = m ^ N` and the composite of
   `w` with `AdicCompletion.evalₐ m N`. This yields `E`, `t`, the structural quotient
   isomorphism `α`, and the required lifting identity. No henselian or G-ring hypothesis
   is needed: Tag 07M7 allows any ideal.
2. Reduce `α` modulo `m`. It gives `R/m ≅ E/mE`, so `q = mE` is maximal and contracts
   to `m`. By `def-weil-pbc-localization-at-prime`, `T = E_q` has maximal ideal
   `n = qT = mT`. Its residue field is `E/q`, giving the structural isomorphism `ρ`.
   The structure map `λ : R → T` is local.
3. Locality induces maps `R/m^r → T/n^r`. Their compatibility gives the coordinatewise
   completion map (`def-weil-pbc-adic-completion`). Localizing the lifting identity in
   step 1 shows that the N-th coordinates of the two displayed completed elements agree.
4. Noetherianity makes `m` finitely generated, hence `n = mT` is finitely generated.
   Apply `lem-weil-pbc-adic-completion-mod-power` at `(T,n)`: the kernel of the N-th
   projection is `n^N` extended to the completion. The coordinate equality from step 3
   is therefore precisely the final congruence, for every `z : B`. -/
theorem smooth_formal_point_etale_approximation
    (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B]
    (hB : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (w : B →ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (E : CommAlgCat.{u} R),
      Etale (Spec.map (CommRingCat.ofHom (algebraMap R E))) ∧
      ∃ (α : R ⧸ (IsLocalRing.maximalIdeal R) ^ N →ₐ[R]
          E ⧸ (((IsLocalRing.maximalIdeal R) ^ N).map (algebraMap R E))),
        Function.Bijective α ∧
        ∃ (t : B →ₐ[R] E),
          (∀ z : B,
            Ideal.Quotient.mk (((IsLocalRing.maximalIdeal R) ^ N).map
                (algebraMap R E)) (t z) =
              α (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) N (w z))) ∧
          ∃ (q : PrimeSpectrum E),
            q.asIdeal = (IsLocalRing.maximalIdeal R).map (algebraMap R E) ∧
            q.asIdeal.IsMaximal ∧
            q.asIdeal.comap (algebraMap R E) = IsLocalRing.maximalIdeal R ∧
            (∃ (ρ : R ⧸ IsLocalRing.maximalIdeal R ≃+* q.asIdeal.ResidueField),
              ∀ r : R, ρ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) r) =
                algebraMap E q.asIdeal.ResidueField (algebraMap R E r)) ∧
            IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) =
              q.asIdeal.map (algebraMap E (Localization.AtPrime q.asIdeal)) ∧
            IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) =
              (IsLocalRing.maximalIdeal R).map
                ((algebraMap E (Localization.AtPrime q.asIdeal)).comp (algebraMap R E)) ∧
            ∃ (hlocal : IsLocalHom
                ((algebraMap E (Localization.AtPrime q.asIdeal)).comp (algebraMap R E))),
              ∀ z : B,
                Classical.choose (@RingHom.exists_adicCompletion_map_of_local
                    R (Localization.AtPrime q.asIdeal) _ _ _ _
                    ((algebraMap E (Localization.AtPrime q.asIdeal)).comp (algebraMap R E))
                    hlocal) (w z) -
                  AdicCompletion.of
                    (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
                    (Localization.AtPrime q.asIdeal)
                    (algebraMap E (Localization.AtPrime q.asIdeal) (t z)) ∈
                  ((IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) ^ N).map
                    (algebraMap (Localization.AtPrime q.asIdeal)
                      (AdicCompletion
                        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
                        (Localization.AtPrime q.asIdeal))) := by
  sorry

end AlgebraicGeometry
