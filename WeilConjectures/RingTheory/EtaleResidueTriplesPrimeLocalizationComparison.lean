/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeEquiv

/-! # Comparison of residue-triple colimits across prime localization

The ring colimit of pointed étale triples over `(R, p)` is also a colimit of the pointed étale
triples over the localization `R_p`.

## Implementation details

The comparison transports the colimit cocone through the natural equivalence of cocones
`etaleResidueTriples_primeLocalization_coconeEquiv`. It requires no separable-closure
hypothesis, and the supplied `R_p`-algebra structure on `C` is kept fixed throughout.

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

/-- Localization of the base preserves the ring colimit of pointed étale triples: if `c` is a
colimit cocone over `(R, p)` with vertex isomorphic to `C`, then `C` is the vertex of a colimit
cocone on the pointed étale ring diagram over `R_p` whose legs restrict to the given
`R_p`-algebra map on `R_p`. -/
theorem etaleResidueTriples_primeLocalization_comparison
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (c : Cocone (etaleResidueTriplesRingDiagram R p K χ)) (hc : IsColimit c)
    (C : CommRingCat.{u}) (e : c.pt ≅ C)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    [Algebra (Localization.AtPrime p.asIdeal) C]
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (hC : ∀ r : R, algebraMap (Localization.AtPrime p.asIdeal) C
      (algebraMap R (Localization.AtPrime p.asIdeal) r) =
        (c.ι.app ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩ ≫ e.hom).hom r) :
    ∃ (ι : etaleResidueTriplesRingDiagram
        (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
        (Functor.const _).obj C),
      Nonempty (IsColimit (Cocone.mk C ι)) ∧
      ∀ t, t.α ≫ ι.app t =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) C) := by
  classical
  obtain ⟨E, hE, hR⟩ :=
    etaleResidueTriples_primeLocalization_coconeEquiv R p K χ q ψ hψ hK
  let η := c.ι ≫ (Functor.const _).map e.hom
  let ι := E C η
  have hη : IsColimit (Cocone.mk C η) := IsColimit.extendIso e.hom hc
  have hι : IsColimit (Cocone.mk C ι) :=
    { desc := fun s ↦ hη.desc (Cocone.mk s.pt ((E s.pt).symm s.ι))
      fac := fun s t ↦ by
        have h : η ≫ (Functor.const _).map
            (hη.desc (Cocone.mk s.pt ((E s.pt).symm s.ι))) = (E s.pt).symm s.ι := by
          apply NatTrans.ext
          funext j
          exact hη.fac _ j
        have h' := congrArg (E s.pt) h
        rw [hE, (E s.pt).apply_symm_apply] at h'
        exact congrArg (fun x ↦ x.app t) h'
      uniq := fun s m hm ↦ by
        apply hη.uniq (Cocone.mk s.pt ((E s.pt).symm s.ι)) m
        have h : ι ≫ (Functor.const _).map m = s.ι := by
          apply NatTrans.ext
          funext t
          exact hm t
        have h' : η ≫ (Functor.const _).map m = (E s.pt).symm s.ι := by
          apply (E s.pt).injective
          rw [hE, (E s.pt).apply_symm_apply]
          exact h
        intro t
        exact congrArg (fun x ↦ x.app t) h' }
  refine ⟨ι, ⟨hι⟩, ?_⟩
  intro t
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (p.asIdeal.primeCompl)
  ext r
  exact (hR C η t r).trans (hC r).symm

end AlgebraicGeometry.Scheme
