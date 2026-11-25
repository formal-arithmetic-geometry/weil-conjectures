/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.PrimeLocalizationEtaleAlgebraModel

/-! # Epic global models of pointed étale triples over a prime localization

Every pointed étale triple over `R_p` is the target of an epic compatible pointed map from a
pointed étale triple over `(R, p)`.

## Implementation details

The model is obtained by descending the étale `R_p`-algebra to an affine étale model `C` over
some principal localization `R_s`, so that the given algebra is a localization of `C`. Keeping
this localization property during descent is essential: it is what makes the map epic.

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

/-- Every pointed étale triple over `R_p` receives a compatible pointed map from some pointed
étale triple over `(R, p)` whose underlying ring map is an epimorphism. -/
theorem etaleResidueTriples_primeLocalization_component_extension_unique_aux
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
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ) :
    ∃ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
      s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ ∧
      Epi β := by
  obtain ⟨C, a, i, he, ha, M, hlocal⟩ :=
    primeLocalization_etale_algebra_model R p t.B t.α t.etale
  let b : C ⟶ CommRingCat.of K :=
    i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
  obtain ⟨r, φ, hφ⟩ := exists_pointing C K b
  have hc : a ≫ (ΓSpecIso C).inv ≫ (Spec C).Γevaluation r ≫ φ =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ := by
    rw [hφ]
    change a ≫ i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ = _
    rw [← Category.assoc a i, ha, Category.assoc, t.compatible, hψ, hK]
  have hover : Spec.map a r = p := pointing_over R C p K χ a r φ hc
  let c : EtaleResidueTriples R p K χ := ⟨C, a, he, r, hover, φ, hc⟩
  let := i.hom.toAlgebra
  let : IsLocalization M t.B := hlocal
  have hi : Epi i := by
    change Epi (CommRingCat.ofHom (algebraMap C t.B))
    exact IsLocalization.epi M t.B
  exact ⟨c, i, ha, hφ.symm, hi⟩

end AlgebraicGeometry.Scheme
