module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.LocalProperties.Reduced
import WeilConjectures.RingTheory.EtaleNormalRing
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions

/-!
# Finite normal-domain factors of an étale algebra over a normal domain

Source: literature/stacks-project/algebra.tex, Tag 030C (lemma-characterize-reduced-ring-normal),
implication (1) to (3), applied to an étale algebra over a domain; the finite generic-fibre
argument uses Tags 00FN, 00FR, 00HS and 00E3.
(blueprint: lem-trf-etale-normal-domain-finite-factors)
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry

/--
If `A` is a normal integral domain and `B` is an étale `A`-algebra, then `B` is a finite
product of normal integral domains as an `A`-algebra. The proof combines Stacks Tag 030C
with a finite-type generic fibre and flat tensor injectivity:

1. Étale ascent of normality and detection by maximal localizations show that `B` is
   reduced and normal, including when `B` is the zero ring.
2. The affine étale dictionary makes `B` a finitely presented, hence finite-type and flat,
   `A`-algebra.
3. The generic fibre `Frac A ⊗[A] B` is finite type over `Frac A`, so it is Noetherian
   and has finitely many minimal primes.
4. Flatness makes the map from `B` to the generic fibre injective. Every minimal prime
   of `B` is the contraction of a minimal prime of that fibre. Thus there are finitely many.
5. The reduced-normal finite-minimal-prime criterion (Tag 030C, (1) to (3)) gives a finite
   product of normal integral domains.  Transporting the `A`-algebra structure along the ring
   isomorphism makes it an `A`-algebra isomorphism.  This also covers the empty product and
   imposes no Noetherian hypothesis on either ring.

Source: literature/stacks-project/algebra.tex, Tag 030C (lemma-characterize-reduced-ring-normal),
implication (1) to (3), with finite-type Noetherianity and finite minimal primes from
Tags 00FN and 00FR, and minimal-prime lifting from Tag 00FK.
(blueprint: lem-trf-etale-normal-domain-finite-factors)
-/
theorem etale_normal_domain_finite_factors
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hA : IsDomain A ∧ IsIntegrallyClosed A)
    (hEtale : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    ∃ (n : ℕ) (B₁ : Fin n → Type u) (_ : ∀ j, CommRing (B₁ j))
      (_ : ∀ j, Algebra A (B₁ j)),
      ∃ (_ : ∀ j, IsDomain (B₁ j) ∧ IsIntegrallyClosed (B₁ j)),
        Nonempty (B ≃ₐ[A] (∀ j, B₁ j)) := by
  let : IsDomain A := hA.1
  let : IsIntegrallyClosed A := hA.2
  have he : (algebraMap A B).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hEtale
  let : Algebra.Etale A B := RingHom.etale_algebraMap.mp he
  have hn : ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
    apply he.isNormalRing
    intro p hp
    exact ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
        p.primeCompl_le_nonZeroDivisors⟩
  let : _root_.IsReduced B := by
    apply isReduced_ofLocalizationMaximal
    intro p hp
    let : p.IsMaximal := hp
    let : IsDomain (Localization.AtPrime p) := (hn p).1
    infer_instance
  -- Flatness embeds B into the generic fibre; minimal primes lift along injections.
  let K := FractionRing A
  let C := TensorProduct A K B
  let f : B →ₐ[A] C := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective A K)
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing K C
  have hfin : (minimalPrimes B).Finite := by
    apply ((minimalPrimes.finite_of_isNoetherianRing C).image
      (Ideal.comap f.toRingHom)).subset
    intro p hp
    apply Ideal.minimalPrimes_comap_subset f.toRingHom (⊥ : Ideal C)
    rwa [Ideal.comap_bot_of_injective f.toRingHom hf]
  obtain ⟨n, D, hD, ⟨e⟩⟩ :=
    (reduced_normal_iff_integrallyClosed_totalFractions B hfin).2.mp
      ((reduced_normal_iff_integrallyClosed_totalFractions B hfin).1.mp hn)
  let alg (i : Fin n) : Algebra A (D i) :=
    ((Pi.evalRingHom (fun j ↦ D j) i).comp (e.toRingHom.comp (algebraMap A B))).toAlgebra
  let : ∀ i, Algebra A (D i) := alg
  refine ⟨n, (fun i ↦ (D i : Type u)), (fun i ↦ inferInstance), alg, hD, ?_⟩
  exact ⟨AlgEquiv.ofRingEquiv (f := e) (fun a ↦ rfl)⟩

end AlgebraicGeometry
