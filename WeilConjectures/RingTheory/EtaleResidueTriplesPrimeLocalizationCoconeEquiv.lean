/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeExtension
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRestriction

/-! # Cocones on pointed étale diagrams under prime localization

Cocones on the pointed étale ring diagram over `(R, p)` correspond naturally to cocones on
the pointed étale ring diagram over the localization `R_p`.

## Implementation details

The equivalence combines the unique extension of an `R`-cocone to an `R_p`-cocone
(`etaleResidueTriples_primeLocalization_cocone_extension`) with the restriction in the other
direction (`etaleResidueTriples_primeLocalization_cocone_restriction`). No universal cocone
or algebra structure on the vertex is assumed.

## References

* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks: Tag 00CR](https://stacks.math.columbia.edu/tag/00CR)
* [Stacks: Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks: Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Cocones on the pointed étale ring diagrams before and after prime localization are
naturally equivalent, with the same vertex and the same restricted base map on `R`. -/
theorem etaleResidueTriples_primeLocalization_coconeEquiv
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    : ∃ E : ∀ V : CommRingCat.{u},
        (etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V) ≃
        (etaleResidueTriplesRingDiagram
          (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
            (Functor.const _).obj V),
      (∀ (V W : CommRingCat.{u}) η (f : V ⟶ W),
        E W (η ≫ (Functor.const _).map f) =
          E V η ≫ (Functor.const _).map f) ∧
      ∀ (V : CommRingCat.{u}) η
          (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
          (r : R),
        (t.α ≫ (E V η).app t).hom (algebraMap R (Localization.AtPrime p.asIdeal) r) =
          (η.app ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩).hom r := by
  classical
  let F := fun V η ↦
    (etaleResidueTriples_primeLocalization_cocone_extension R p K χ q ψ hψ hK V η).choose
  have hF : ∀ V η,
      etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η (F V η) :=
    fun V η ↦
      (etaleResidueTriples_primeLocalization_cocone_extension
        R p K χ q ψ hψ hK V η).choose_spec.1
  have uniqueF : ∀ V η θ,
      etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η θ →
      θ = F V η :=
    fun V η θ h ↦
      (etaleResidueTriples_primeLocalization_cocone_extension
        R p K χ q ψ hψ hK V η).choose_spec.2 θ h
  have bijectiveF : ∀ V, Function.Bijective (F V) := by
    intro V
    constructor
    · intro η η' he
      obtain ⟨η₀, hη₀, hu⟩ :=
        etaleResidueTriples_primeLocalization_cocone_restriction
          R p K χ q ψ hψ hK V (F V η)
      have hη' := hF V η'
      rw [← he] at hη'
      exact (hu η (hF V η)).trans (hu η' hη').symm
    · intro θ
      obtain ⟨η, hη, _⟩ :=
        etaleResidueTriples_primeLocalization_cocone_restriction R p K χ q ψ hψ hK V θ
      exact ⟨η, (uniqueF V η θ hη).symm⟩
  let E := fun V ↦ Equiv.ofBijective (F V) (bijectiveF V)
  refine ⟨E, ?_, ?_⟩
  · intro V W η f
    change F W (η ≫ (Functor.const _).map f) = F V η ≫ (Functor.const _).map f
    symm
    apply uniqueF
    intro s t β hb hp
    change β ≫ (F V η).app t ≫ f = η.app s ≫ f
    rw [← Category.assoc, hF V η s t β hb hp]
  · intro V η t r
    let s : EtaleResidueTriples R p K χ :=
      ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
    let β := CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α
    have hb : s.α ≫ β =
        CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α := by
      simp [s, β]
    have hp : β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ := by
      dsimp [β, s]
      rw [Category.assoc, t.compatible, hψ, hK]
    have h := ConcreteCategory.congr_hom (hF V η s t β hb hp) r
    exact h


end AlgebraicGeometry.Scheme
