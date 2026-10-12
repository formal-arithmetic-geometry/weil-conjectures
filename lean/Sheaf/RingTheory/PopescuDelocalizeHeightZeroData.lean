module

public import Sheaf.RingTheory.PopescuDelocalizeWeak

@[expose] public section

universe u v t

namespace Algebra

/-- The construction in Stacks Project, Lemma 07FA, produces a finite presentation
factorization whose extended singular ideal contains the original one and escapes `q`.
The detailed construction uses the weak delocalization lemma, nilpotence in the
zero-dimensional localization, and the auxiliary polynomial algebra localizations.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07FA.
(blueprint: lem-weil-pbc-popescu-delocalize-height-zero-data)
-/
theorem exists_popescu_resolution_data_of_local_height_zero
    {R : Type u} {A : Type v} {Λ : Type t}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)
    (hlocal :
      letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
      CanBePopescuResolved
        (Algebra.TensorProduct.lift
          (Algebra.ofId (Localization.AtPrime (q.asIdeal.under R))
            (Localization.AtPrime q.asIdeal))
          ((IsScalarTower.toAlgHom R Λ (Localization.AtPrime q.asIdeal)).comp α)
          (fun _ _ => Commute.all _ _))
        ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal), inferInstance⟩)
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      ∃ (β : A →ₐ[R] B) (γ : B →ₐ[R] Λ),
        FinitePresentation R B ∧ γ.comp β = α ∧
          popescuIdeal α ≤ popescuIdeal γ ∧ ¬ popescuIdeal γ ≤ q.asIdeal := by
  sorry

end Algebra
