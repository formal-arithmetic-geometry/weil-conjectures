/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRelation
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCompatibleMapExists

/-! # Uniqueness of restricted pointed étale cocones across prime localization

A cocone on the pointed étale ring diagram over `R_p` has at most one compatible cocone on
the pointed étale ring diagram over `(R, p)`.

## References

* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks: Tag 00U2](https://stacks.math.columbia.edu/tag/00U2), part (3)
* Stacks Project, Section 10.9 (localization)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- A cocone on the pointed étale ring diagram over `R_p` has at most one compatible cocone
on the pointed étale ring diagram over `(R, p)` with the same vertex. -/
theorem etaleResidueTriples_primeLocalization_cocone_restriction_unique
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
    (θ : etaleResidueTriplesRingDiagram
      (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
        (Functor.const _).obj V)
    (η η' : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (hη : etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η θ)
    (hη' : etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η' θ) :
    η = η' := by
  apply NatTrans.ext
  funext s
  obtain ⟨t, β, hα, hφ⟩ :=
    etaleResidueTriples_primeLocalization_compatible_map_exists
      R p K χ q ψ hψ hK s
  have eη := hη s t β hα hφ
  have eη' := hη' s t β hα hφ
  rw [← eη, ← eη']

end AlgebraicGeometry.Scheme
