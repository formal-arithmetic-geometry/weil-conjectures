/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Compatible maps to prime-localized pointed etale triples

Every pointed étale triple over `(R, p)` maps compatibly into a pointed étale triple over the
localization `R_p`.

## Implementation details

The target triple is the base change of the given triple along `R → R_p`, constructed as a
pushout of rings; its pointing is obtained from the field-point correspondence. No
separable-closure hypothesis on `K` is needed.

## References

* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks: Tag 00CP](https://stacks.math.columbia.edu/tag/00CP)
* [Stacks: Tag 00U2](https://stacks.math.columbia.edu/tag/00U2), part (3)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The spectrum map of the pointing `B → K` given by a point `r` and a residue-field
embedding `φ` is `Spec.map φ` followed by `fromSpecResidueField r`. -/
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

/-- Every pointed étale triple over `(R, p)` admits a compatible pointed map into a pointed
étale triple over `R_p`, for any field `K`. -/
theorem etaleResidueTriples_primeLocalization_compatible_map_exists
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
    (s : EtaleResidueTriples R p K χ) :
    ∃ (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ)
      (β : s.B ⟶ t.B),
      s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ := by
  classical
  let bs := (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ
  let ba := (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
    (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ
  let P := pushout s.α (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)))
  let β : s.B ⟶ P := pushout.inl s.α _
  let α : CommRingCat.of (Localization.AtPrime p.asIdeal) ⟶ P := pushout.inr s.α _
  let b : P ⟶ CommRingCat.of K :=
    pushout.desc bs ba (s.compatible.trans (by
      change (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ =
        CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ ba
      rw [← hK]
      congr 1
      exact hψ.symm))
  obtain ⟨r, φ, hφ⟩ := exists_pointing P K b
  have hc : α ≫ (ΓSpecIso P).inv ≫ (Spec P).Γevaluation r ≫ φ = ba := by
    rw [hφ]
    exact pushout.inr_desc _ _ _
  have hetale : Etale (Spec.map α) :=
    MorphismProperty.of_isPullback
      (isPullback_SpecMap_pushout s.α (CommRingCat.ofHom (algebraMap R
        (Localization.AtPrime p.asIdeal)))) s.etale
  have hα : s.α ≫ β = CommRingCat.ofHom (algebraMap R
      (Localization.AtPrime p.asIdeal)) ≫ α := pushout.condition
  have hpoint : β ≫ (ΓSpecIso P).inv ≫ (Spec P).Γevaluation r ≫ φ = bs := by
    rw [hφ]
    exact pushout.inl_desc _ _ _
  have hover : Spec.map α r = q := by
    apply pointing_over (CommRingCat.of (Localization.AtPrime p.asIdeal)) P q K ψ α r φ
    exact hc
  let t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ :=
    ⟨P, α, hetale, r, hover, φ, hc⟩
  refine ⟨t, β, hα, ?_⟩
  exact hpoint

end AlgebraicGeometry.Scheme
