/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionExists
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationExtensionUnique

/-! # Extension of a single pointed étale cocone leg

A cocone over `(R, p)` determines a unique compatible leg on each pointed étale triple over
`R_p`.

## References

* [Stacks: Tag 00CR](https://stacks.math.columbia.edu/tag/00CR)
* [Stacks: Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks: Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks: Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A cocone on the pointed étale ring diagram over `(R, p)` determines, on each pointed étale
triple over `R_p`, a unique ring map to its vertex compatible with all pointed maps from
triples over `(R, p)`. -/
theorem etaleResidueTriples_primeLocalization_component_extension
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (V : CommRingCat.{u})
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ) :
    ∃! b : t.B ⟶ V,
      ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
        s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
          t.α →
        β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        β ≫ b = η.app s := by
  obtain ⟨b, hb⟩ :=
    etaleResidueTriples_primeLocalization_component_extension_exists
      R p K χ q ψ hψ hK V η t
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  exact (etaleResidueTriples_primeLocalization_component_extension_unique
    R p K χ q ψ hψ hK V η t b b' hb hb').symm

end AlgebraicGeometry.Scheme
