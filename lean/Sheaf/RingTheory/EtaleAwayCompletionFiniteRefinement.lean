module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.PairHenselization
import WeilConjectures.RingTheory.PairHenselizationNoetherianCompletion
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.RingTheory.BijectiveQuotientMapPowOfFlat
import WeilConjectures.RingTheory.PairHenselizationCompletionData

/-!
# Realizing a completion map in an étale neighbourhood

Source: Stacks Project, restricted.tex, Tag 0AKJ,
`lemma-fully-faithful-etale-over-complement`, existence and final assertion
(blueprint: lem-per-etale-away-completion-finite-refinement).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RingTheory

/-- A map of completions from an algebra étale away from the completion ideal is realized
in an étale finitely presented neighbourhood of the target, identical modulo that ideal.
Source: Stacks Project, restricted.tex, Tag 0AKJ,
`lemma-fully-faithful-etale-over-complement`, existence and final assertion
(blueprint: lem-per-etale-away-completion-finite-refinement).

The étaleness hypothesis tests primes of `D` above the complement of `V(I)`.
Since `A` is Noetherian and `D` is of finite type, it is finitely presented; thus
`Algebra.IsEtaleAt` is precisely étaleness of the scheme map at that point.
The final clause writes `û = ĵ ∘ φ` on every quotient coordinate: if `d` represents
`x` modulo `I^n D` and `r` represents `φ x` modulo `I^n R`, their images in
`R' / I^n R'` agree. Quotient projections are surjective and jointly injective on
completions, so this is exactly equality of the canonical completion maps.
The ideal `IR'` is written as the successive extension `(IR)R'`; the scalar tower
identifies it with extension directly from `A`. No henselian hypothesis on `R` is used.

Proof:
1. Put `J = IR` and henselize `(R,J)`, obtaining `η : R → H`. By
   lem-weil-pbc-pair-henselization, `H` is the filtered colimit of étale `R`-algebras
   identical modulo `J`. By lem-weil-pbc-henselization-noetherian-completion, `H` is
   Noetherian and `η` induces the canonical isomorphism `θ : R̂ → Ĥ`. Apply
   lem-per-etale-away-completion-hom-lifting to `θ ∘ φ` and the henselian pair
   `(H,IH)`, obtaining `w : D → H` with completion `θ ∘ φ`.
2. By lem-weil-pbc-finite-type-noetherian-finite-presentation, `D` is finitely
   presented over `A`. Apply
   lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit to factor `w`
   through an étale stage `R'`, with map `u : D → R'` and coprojection `k : R' → H`.
   Its structure map `j` is an isomorphism modulo `J` by the stage definition, and
   lem-weil-pbc-etale-algebra-finite-presentation-localization gives finite presentation.
3. By lem-weil-pbc-etale-algebra-flat, `j` is flat. Apply
   lem-weil-pbc-flat-iso-mod-ideal-powers and
   lem-weil-pbc-henselization-completion-data: all quotient maps of `j`, and hence
   its canonical completion map `ĵ`, are isomorphisms.
4. Functoriality of completion gives `k̂ ĵ = θ` and `k̂ û = θ φ` from `kj = η` and
   `ku = w`. Therefore `k̂ = θ ĵ⁻¹` is an isomorphism. Cancel it to obtain
   `û = ĵ φ`, which is the displayed identity on quotient representatives. -/
theorem etale_away_completion_finite_refinement
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (D : Type v) [CommRing D] [Algebra A D]
    (hD : (algebraMap A D).FiniteType)
    (R : Type w) [CommRing R] [Algebra A R] [IsNoetherianRing R]
    (hEtale : ∀ q : PrimeSpectrum D,
      ¬ I ≤ q.asIdeal.comap (algebraMap A D) → Algebra.IsEtaleAt A q.asIdeal)
    (φ : AdicCompletion (I.map (algebraMap A D)) D →ₐ[A]
      AdicCompletion (I.map (algebraMap A R)) R) :
    ∃ (R' : Type w) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra A R')
      (_ : IsScalarTower A R R'),
      Algebra.Etale R R' ∧ Algebra.FinitePresentation R R' ∧
      ∃ u : D →ₐ[A] R',
        Function.Bijective
          (Ideal.quotientMap ((I.map (algebraMap A R)).map (algebraMap R R'))
            (algebraMap R R') Ideal.le_comap_map) ∧
        ∀ (n : ℕ) (x : AdicCompletion (I.map (algebraMap A D)) D) (d : D) (r : R),
          AdicCompletion.evalₐ (I.map (algebraMap A D)) n x =
            Ideal.Quotient.mk ((I.map (algebraMap A D)) ^ n) d →
          AdicCompletion.evalₐ (I.map (algebraMap A R)) n (φ x) =
            Ideal.Quotient.mk ((I.map (algebraMap A R)) ^ n) r →
          Ideal.Quotient.mk (((I.map (algebraMap A R)).map (algebraMap R R')) ^ n)
            (u d) =
          Ideal.Quotient.mk (((I.map (algebraMap A R)).map (algebraMap R R')) ^ n)
            (algebraMap R R' r) := by
  sorry

end RingTheory
