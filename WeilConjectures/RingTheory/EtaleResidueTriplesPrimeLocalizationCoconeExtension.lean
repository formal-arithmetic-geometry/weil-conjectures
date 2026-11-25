/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRelation
import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtension

/-! # Compatible cocone legs across prime localization

Every cocone on the pointed étale ring diagram over `(R, p)` extends uniquely to a compatible
cocone on the pointed étale ring diagram over `R_p`.

## References

* [Stacks: Tag 00CR](https://stacks.math.columbia.edu/tag/00CR)
* [Stacks: Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks: Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Every cocone on the pointed étale ring diagram over `(R, p)` has a unique cocone on the
pointed étale ring diagram over `R_p` with the same vertex and compatible legs. -/
theorem etaleResidueTriples_primeLocalization_cocone_extension
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
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V) :
    ∃! θ : etaleResidueTriplesRingDiagram
      (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
        (Functor.const _).obj V,
      etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η θ := by
  classical
  have H := etaleResidueTriples_primeLocalization_component_extension R p K χ q ψ hψ hK V η
  choose b hb hu using H
  let θ : etaleResidueTriplesRingDiagram
      (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ ⟶
        (Functor.const _).obj V :=
    { app := b
      naturality := by
        intro t t' f
        change f.hom.right.left ≫ b t' = b t
        apply hu t
        intro s β hα hφ
        have ha : t.α ≫ f.hom.right.left = t'.α :=
          congrArg CommaMorphism.left (Under.w f.hom)
        have hp : f.hom.right.left ≫ (ΓSpecIso t'.B).inv ≫
            (Spec t'.B).Γevaluation t'.q ≫ t'.φ =
            (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ :=
          Over.w f.hom.right
        rw [← Category.assoc]
        apply hb t' s (β ≫ f.hom.right.left)
        · rw [← Category.assoc, hα, Category.assoc, ha]
        · simpa only [Category.assoc, hp] using hφ }
  refine ⟨θ, ?_, ?_⟩
  · intro s t β hα hφ
    exact hb t s β hα hφ
  · intro θ' hθ'
    apply NatTrans.ext
    funext t
    exact hu t (θ'.app t) (fun s β hα hφ ↦ hθ' s t β hα hφ)

end AlgebraicGeometry.Scheme
