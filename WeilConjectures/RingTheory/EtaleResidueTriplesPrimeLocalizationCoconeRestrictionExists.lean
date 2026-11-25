/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EtaleResidueTriplesPrimeLocalizationCoconeRelation
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Restriction of pointed étale cocones across prime localization

Every cocone on the pointed étale ring diagram over `R_p` restricts to a compatible cocone on
the pointed étale ring diagram over `(R, p)`.

## Implementation details

The base change of a pointed triple is constructed as a pushout of rings. The field-point
correspondence supplies its residue-field pointing, and the pushout universal property gives
compatible arrows and hence naturality of the restricted cocone, without choosing
denominators.

## References

* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks: Tag 00U2](https://stacks.math.columbia.edu/tag/00U2), part (3)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
private lemma pointing_spec_map (B : CommRingCat.{u}) (r : Spec B)
    (K : Type u) [Field K] (φ : (Spec B).residueField r ⟶ CommRingCat.of K) :
    Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation r ≫ φ) =
      Spec.map φ ≫ (Spec B).fromSpecResidueField r := by
  simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

private lemma exists_pointing (B : CommRingCat.{u}) (K : Type u) [Field K]
    (b : B ⟶ CommRingCat.of K) :
    ∃ (r : Spec B) (φ : (Spec B).residueField r ⟶ CommRingCat.of K),
      (ΓSpecIso B).inv ≫ (Spec B).Γevaluation r ≫ φ = b := by
  generalize he : (SpecToEquivOfField K (Spec B)) (Spec.map b) = z
  obtain ⟨r, φ⟩ := z
  refine ⟨r, φ, ?_⟩
  apply Spec.map_injective
  rw [pointing_spec_map]
  have h := (SpecToEquivOfField K (Spec B)).symm_apply_apply (Spec.map b)
  rw [he] at h
  exact h

private lemma pointing_over (A B : CommRingCat.{u}) (q : Spec A)
    (K : Type u) [Field K] (ψ : (Spec A).residueField q ⟶ CommRingCat.of K)
    (a : A ⟶ B) (r : Spec B) (φ : (Spec B).residueField r ⟶ CommRingCat.of K)
    (hc : a ≫ (ΓSpecIso B).inv ≫ (Spec B).Γevaluation r ≫ φ =
      (ΓSpecIso A).inv ≫ (Spec A).Γevaluation q ≫ ψ) :
    Spec.map a r = q := by
  have h := congrArg Spec.map hc
  rw [Spec.map_comp, pointing_spec_map, pointing_spec_map] at h
  have h' := congrArg
    (fun f : Spec (CommRingCat.of K) ⟶ Spec A ↦ f (IsLocalRing.closedPoint K)) h
  simpa using h'

-- The pushout is the base change of one pointed triple. Its universal property
-- supplies the arrows needed for cocone naturality, without choosing denominators.
private lemma exists_base_change_triple
    (R A : CommRingCat.{u}) (p : Spec R) (q : Spec A)
    (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (ψ : (Spec A).residueField q ⟶ CommRingCat.of K)
    (ℓ : R ⟶ A)
    (hℓ : ℓ ≫ (ΓSpecIso A).inv ≫ (Spec A).Γevaluation q ≫ ψ =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (s : EtaleResidueTriples R p K χ) :
    ∃ (t : EtaleResidueTriples A q K ψ) (ι : s.B ⟶ t.B),
      s.α ≫ ι = ℓ ≫ t.α ∧
      ι ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ ∧
      ∀ (t' : EtaleResidueTriples A q K ψ) (β : s.B ⟶ t'.B),
        s.α ≫ β = ℓ ≫ t'.α →
        β ≫ (ΓSpecIso t'.B).inv ≫ (Spec t'.B).Γevaluation t'.q ≫ t'.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        ∃ a : t ⟶ t', ι ≫ (etaleResidueTriplesRingDiagram A q K ψ).map a = β := by
  classical
  let bs := (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ
  let ba := (ΓSpecIso A).inv ≫ (Spec A).Γevaluation q ≫ ψ
  let P := pushout s.α ℓ
  let ι : s.B ⟶ P := pushout.inl s.α ℓ
  let α : A ⟶ P := pushout.inr s.α ℓ
  let b : P ⟶ CommRingCat.of K := pushout.desc bs ba (s.compatible.trans hℓ.symm)
  obtain ⟨r, φ, hφ⟩ := exists_pointing P K b
  have hc : α ≫ (ΓSpecIso P).inv ≫ (Spec P).Γevaluation r ≫ φ = ba := by
    rw [hφ]
    exact pushout.inr_desc _ _ _
  have hetale : Etale (Spec.map α) :=
    MorphismProperty.of_isPullback (isPullback_SpecMap_pushout s.α ℓ) s.etale
  let t : EtaleResidueTriples A q K ψ :=
    ⟨P, α, hetale, r, pointing_over A P q K ψ α r φ hc, φ, hc⟩
  have ht : (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ = b := hφ
  refine ⟨t, ι, pushout.condition, ?_, ?_⟩
  · rw [ht]
    exact pushout.inl_desc _ _ _
  · intro t' β hα hβ
    let bt := (ΓSpecIso t'.B).inv ≫ (Spec t'.B).Γevaluation t'.q ≫ t'.φ
    let δ : P ⟶ t'.B := pushout.desc β t'.α hα
    have hδ : δ ≫ bt = b := by
      apply pushout.hom_ext
      · simpa only [Category.assoc, δ, b, pushout.inl_desc_assoc,
          pushout.inl_desc] using hβ
      · simpa only [Category.assoc, δ, b, pushout.inr_desc_assoc,
          pushout.inr_desc] using t'.compatible
    have ha : α ≫ δ = t'.α := pushout.inr_desc _ _ _
    have hp : δ ≫ (ΓSpecIso t'.B).inv ≫ (Spec t'.B).Γevaluation t'.q ≫ t'.φ =
        (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ := by
      rw [ht]
      exact hδ
    let a : t ⟶ t' := ⟨Under.homMk (Over.homMk δ hp) (by
      apply Over.OverMorphism.ext
      exact ha)⟩
    exact ⟨a, pushout.inl_desc _ _ _⟩

private lemma restrict_base_change_cocone
    (R A : CommRingCat.{u}) (p : Spec R) (q : Spec A)
    (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (ψ : (Spec A).residueField q ⟶ CommRingCat.of K)
    (ℓ : R ⟶ A)
    (hℓ : ℓ ≫ (ΓSpecIso A).inv ≫ (Spec A).Γevaluation q ≫ ψ =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (V : CommRingCat.{u})
    (θ : etaleResidueTriplesRingDiagram A q K ψ ⟶ (Functor.const _).obj V) :
    ∃ η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V,
      ∀ (s : EtaleResidueTriples R p K χ) (t : EtaleResidueTriples A q K ψ)
        (β : s.B ⟶ t.B),
        s.α ≫ β = ℓ ≫ t.α →
        β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        β ≫ θ.app t = η.app s := by
  classical
  have H := exists_base_change_triple R A p q K χ ψ ℓ hℓ
  choose t ι hα hφ hf using H
  let η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V :=
    { app := fun s ↦ ι s ≫ θ.app (t s)
      naturality := by
        intro s s' f
        let β : s.B ⟶ s'.B := f.hom.right.left
        have ha : s.α ≫ β = s'.α :=
          congrArg CommaMorphism.left (Under.w f.hom)
        have hp : β ≫ (ΓSpecIso s'.B).inv ≫ (Spec s'.B).Γevaluation s'.q ≫ s'.φ =
            (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ :=
          Over.w f.hom.right
        obtain ⟨a, hea⟩ := hf s (t s') (β ≫ ι s')
          (by rw [← Category.assoc, ha, hα s'])
          (by simpa only [Category.assoc, hφ s'] using hp)
        change β ≫ (ι s' ≫ θ.app (t s')) = (ι s ≫ θ.app (t s)) ≫ 𝟙 V
        calc
          β ≫ (ι s' ≫ θ.app (t s')) = (β ≫ ι s') ≫ θ.app (t s') :=
            (Category.assoc _ _ _).symm
          _ = (ι s ≫ (etaleResidueTriplesRingDiagram A q K ψ).map a) ≫
              θ.app (t s') := congrArg (· ≫ θ.app (t s')) hea.symm
          _ = ι s ≫ ((etaleResidueTriplesRingDiagram A q K ψ).map a ≫
              θ.app (t s')) := Category.assoc _ _ _
          _ = ι s ≫ (θ.app (t s) ≫ 𝟙 V) :=
            congrArg (ι s ≫ ·) (θ.naturality a)
          _ = (ι s ≫ θ.app (t s)) ≫ 𝟙 V := (Category.assoc _ _ _).symm }
  refine ⟨η, ?_⟩
  intro s t' β ha hp
  obtain ⟨a, hea⟩ := hf s t' β ha hp
  change β ≫ θ.app t' = ι s ≫ θ.app (t s)
  have hn : (etaleResidueTriplesRingDiagram A q K ψ).map a ≫ θ.app t' =
      θ.app (t s) := (θ.naturality a).trans (Category.comp_id _)
  calc
    β ≫ θ.app t' = (ι s ≫ (etaleResidueTriplesRingDiagram A q K ψ).map a) ≫
        θ.app t' := congrArg (· ≫ θ.app t') hea.symm
    _ = ι s ≫ ((etaleResidueTriplesRingDiagram A q K ψ).map a ≫ θ.app t') :=
      Category.assoc _ _ _
    _ = ι s ≫ θ.app (t s) := congrArg (ι s ≫ ·) hn

/-- Every cocone on the pointed étale ring diagram over `R_p` admits a compatible cocone on
the pointed étale ring diagram over `(R, p)` with the same vertex. -/
theorem etaleResidueTriples_primeLocalization_cocone_restriction_exists
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
        (Functor.const _).obj V) :
    ∃ η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V,
      etaleResidueTriples_primeLocalization_coconeRelation R p K χ q ψ V η θ := by
  apply restrict_base_change_cocone R
    (CommRingCat.of (Localization.AtPrime p.asIdeal)) p q K χ ψ
    (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal))) _ V θ
  rw [hψ]
  exact hK

end AlgebraicGeometry.Scheme
