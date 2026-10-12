module

public import Mathlib.RingTheory.Smooth.Locus
public import Sheaf.RingTheory.SingularIdeal

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- The localized cotangent conditions descend along the field extension.
The proof is the faithful-flat cotangent descent argument of Stacks, Tag 00TG:
flat base change identifies the localized cotangent homology and differentials, and
faithful-flat descent reflects vanishing and finite projectivity.
(blueprint: lem-weil-pbc-formally-smooth-at-prime-field-extension-descent-cotangent-conditions) -/
theorem fieldExtension_cotangent_conditions
    {k : Type u} {K : Type v} {S : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] [FiniteType k S]
    (qK : PrimeSpectrum (K ⊗[k] S)) (hsmooth : IsSmoothAtPrime K qK) :
    Module.Projective (Localization.AtPrime
      (PrimeSpectrum.comap
        (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK).asIdeal)
      (KaehlerDifferential k (Localization.AtPrime
        (PrimeSpectrum.comap
          (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK).asIdeal)) ∧
      Subsingleton (H1Cotangent k (Localization.AtPrime
        (PrimeSpectrum.comap
          (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK).asIdeal)) := by
  sorry

/-- (blueprint: lem-weil-pbc-formally-smooth-at-prime-field-extension-descent)
Formal smoothness at the contracted local ring descends from a smooth tensor-product
localization.  This is the local cotangent descent step in the proof of field-extension
descent; it packages faithful-flat descent of the localized cotangent homology and
finite projectivity of differentials.  The proof uses finite presentation over the field,
faithful flatness after tensoring and localizing, flat base change for cotangent homology
and Kähler differentials, faithful-flat descent of vanishing and finite projectivity, and
the naive cotangent criterion for formal smoothness. -/
theorem formallySmoothAtPrime_of_fieldExtension
    {k : Type u} {K : Type v} {S : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] [FiniteType k S]
    (qK : PrimeSpectrum (K ⊗[k] S)) (hsmooth : IsSmoothAtPrime K qK) :
    Algebra.IsSmoothAt k
      (PrimeSpectrum.comap
        (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK).asIdeal := by
  obtain ⟨hp, h₁⟩ := fieldExtension_cotangent_conditions qK hsmooth
  exact ⟨hp, h₁⟩

end Algebra
