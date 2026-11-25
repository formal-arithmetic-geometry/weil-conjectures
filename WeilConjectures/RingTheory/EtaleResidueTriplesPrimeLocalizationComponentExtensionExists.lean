/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.PrimeLocalizationEtaleAlgebraModel
import WeilConjectures.RingTheory.EtaleResidueTripleUnitRefinement
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Extending cocone legs to pointed etale algebras over a prime localization

Every cocone leg over `(R, p)` extends to a compatible leg on each pointed étale triple over
`R_p`.

## Implementation details

The proof passes through the localization of a descended model at its pointed prime.
Unit refinement extends the model's cocone leg to that local ring. Finite presentation
factors each compatible map through a principal localization, where naturality applies.

## References

* [Stacks: Tag 00U2](https://stacks.math.columbia.edu/tag/00U2), part (10)
* [Stacks: Tag 00CR](https://stacks.math.columbia.edu/tag/00CR)
* [Stacks: Tag 00QO](https://stacks.math.columbia.edu/tag/00QO)
* [Stacks: Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks: Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks: Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
* [Stacks: Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private lemma pointing_spec (B : CommRingCat.{u}) (z : Spec B)
    (K : Type u) [Field K] (φ : (Spec B).residueField z ⟶ CommRingCat.of K) :
    Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation z ≫ φ) =
      Spec.map φ ≫ (Spec B).fromSpecResidueField z := by
  simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

private lemma field_point_factorization (B : CommRingCat.{u}) (K : Type u) [Field K]
    (b : B ⟶ CommRingCat.of K) :
    let z := SpecToEquivOfField K (Spec B) (Spec.map b)
    (ΓSpecIso B).inv ≫ (Spec B).Γevaluation z.1 ≫ z.2 = b := by
  apply Spec.map_injective
  rw [pointing_spec]
  exact (SpecToEquivOfField K (Spec B)).symm_apply_apply (Spec.map b)

private noncomputable abbrev triple_of_point {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    (B : CommRingCat.{u}) (a : R ⟶ B) (b : B ⟶ CommRingCat.of K)
    (ha : Etale (Spec.map a))
    (hc : a ≫ b = (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ) :
    EtaleResidueTriples R p K χ where
  B := B
  α := a
  etale := ha
  q := (SpecToEquivOfField K (Spec B) (Spec.map b)).1
  φ := (SpecToEquivOfField K (Spec B) (Spec.map b)).2
  over := by
    have h := congrArg Spec.map hc
    rw [Spec.map_comp, pointing_spec] at h
    have h' := congrArg
      (fun f : Spec (CommRingCat.of K) ⟶ Spec R ↦ f (IsLocalRing.closedPoint K)) h
    simpa using h'
  compatible := by rw [field_point_factorization]; exact hc

private lemma triple_of_point_point {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    (B : CommRingCat.{u}) (a : R ⟶ B) (b : B ⟶ CommRingCat.of K)
    (ha : Etale (Spec.map a))
    (hc : a ≫ b = (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ) :
    let c := triple_of_point B a b ha hc
    (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ = b :=
  field_point_factorization B K b

private noncomputable def triple_hom {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    {s t : EtaleResidueTriples R p K χ} (f : s.B ⟶ t.B)
    (ha : s.α ≫ f = t.α)
    (hb : f ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
      (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) : s ⟶ t :=
  InducedCategory.homMk (Under.homMk (Over.homMk f hb) (by
    apply Over.OverMorphism.ext
    exact ha))

private lemma pointing_zero_iff {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    (c : EtaleResidueTriples R p K χ) (x : c.B) :
    ((ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ).hom x = 0 ↔
      x ∈ c.q.asIdeal := by
  change c.φ.hom (((ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q).hom x) = 0 ↔ _
  rw [map_eq_zero]
  have h := Spec.algebraMap_residueFieldIso_inv c.B c.q
  change CommRingCat.ofHom (algebraMap c.B c.q.asIdeal.ResidueField) ≫
    (Spec.residueFieldIso c.B c.q).inv =
      (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q at h
  rw [← h]
  change (Spec.residueFieldIso c.B c.q).inv.hom
    (algebraMap c.B c.q.asIdeal.ResidueField x) = 0 ↔ _
  rw [map_eq_zero]
  exact show x ∈ RingHom.ker (algebraMap c.B c.q.asIdeal.ResidueField) ↔
    x ∈ c.q.asIdeal by rw [Ideal.ker_algebraMap_residueField]

private lemma cocone_leg_isUnit {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    {V : CommRingCat.{u}}
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (c : EtaleResidueTriples R p K χ) (x : c.B) (hx : x ∉ c.q.asIdeal) :
    IsUnit ((η.app c).hom x) := by
  obtain ⟨d, a, ha⟩ := etaleResidueTriple_unit_refinement R p K χ c x hx
  have hη : (etaleResidueTriplesRingDiagram R p K χ).map a ≫ η.app d = η.app c := by
    exact (η.naturality a).trans (Category.comp_id _)
  rw [← hη]
  exact ha.map (η.app d).hom

private lemma cocone_leg_atPrime {R : CommRingCat.{u}} {p : Spec R}
    {K : Type u} [Field K] {χ : (Spec R).residueField p ⟶ CommRingCat.of K}
    {V : CommRingCat.{u}}
    (η : etaleResidueTriplesRingDiagram R p K χ ⟶ (Functor.const _).obj V)
    (c : EtaleResidueTriples R p K χ)
    (δ : CommRingCat.of (Localization.AtPrime c.q.asIdeal) ⟶ CommRingCat.of K)
    (hδ : CommRingCat.ofHom (algebraMap c.B (Localization.AtPrime c.q.asIdeal)) ≫ δ =
      (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ)
    (v : CommRingCat.of (Localization.AtPrime c.q.asIdeal) ⟶ V)
    (hv : CommRingCat.ofHom (algebraMap c.B (Localization.AtPrime c.q.asIdeal)) ≫ v =
      η.app c)
    (s : EtaleResidueTriples R p K χ)
    (f : s.B ⟶ CommRingCat.of (Localization.AtPrime c.q.asIdeal))
    (hfα : s.α ≫ f = c.α ≫
      CommRingCat.ofHom (algebraMap c.B (Localization.AtPrime c.q.asIdeal)))
    (hfφ : f ≫ δ = (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) :
    f ≫ v = η.app s := by
  classical
  -- Finite presentation factors f through a principal localization of the model.
  let F := CommRingCat.awayProdDiagram c.q.asIdeal
  let D := CommRingCat.awayProdCocone c.q.asIdeal
  let a (z : Finset c.q.asIdeal.primeCompl) : c.B ⟶ F.obj z :=
    CommRingCat.ofHom (algebraMap c.B (CommRingCat.AwayProd c.q.asIdeal z))
  have ha (z : Finset c.q.asIdeal.primeCompl) : a z ≫ D.ι.app z =
      CommRingCat.ofHom (algebraMap c.B (Localization.AtPrime c.q.asIdeal)) :=
    CommRingCat.ofHom_algebraMap_comp_awayProdCocone_ι_app c.q.asIdeal z
  let α : (Functor.const _).obj R ⟶ F :=
    { app := fun z ↦ c.α ≫ a z
      naturality := by
        intro z z' h
        change (𝟙 R) ≫ (c.α ≫ a z') = (c.α ≫ a z) ≫ F.map h
        rw [Category.id_comp, Category.assoc]
        exact congrArg (fun k ↦ c.α ≫ k)
          (CommRingCat.ofHom_algebraMap_comp_awayProdDiagram_map c.q.asIdeal h).symm }
  have hfp : s.α.hom.FinitePresentation := by
    let : Algebra R s.B := s.α.hom.toAlgebra
    have : Algebra.Etale R s.B :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mp s.etale
    exact (RingHom.finitePresentation_algebraMap).mpr inferInstance
  obtain ⟨z, g, hgα, hg⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R F α s.α D
      (CommRingCat.isColimitAwayProdCocone c.q.asIdeal) hfp f (by
        intro z
        change s.α ≫ f = (c.α ≫ a z) ≫ D.ι.app z
        rw [Category.assoc, ha]
        exact hfα)
  have het : Etale (Spec.map (c.α ≫ a z)) := by
    have := c.etale
    have : Algebra.Etale c.B (CommRingCat.AwayProd c.q.asIdeal z) :=
      Algebra.Etale.of_isLocalizationAway (∏ x ∈ z, (x : c.B))
    have : Etale (Spec.map (a z)) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    rw [Spec.map_comp]
    infer_instance
  have hc : (c.α ≫ a z) ≫ (D.ι.app z ≫ δ) =
      (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ := by
    rw [Category.assoc, ← Category.assoc (a z), ha, hδ]
    exact c.compatible
  let d := triple_of_point (F.obj z) (c.α ≫ a z) (D.ι.app z ≫ δ) het hc
  have hd : (ΓSpecIso d.B).inv ≫ (Spec d.B).Γevaluation d.q ≫ d.φ =
      D.ι.app z ≫ δ := triple_of_point_point _ _ _ het hc
  let ac : c ⟶ d := triple_hom (a z) rfl (by rw [hd, ← Category.assoc, ha, hδ])
  let as : s ⟶ d := triple_hom g hgα (by rw [hd, ← Category.assoc, ← hg, hfφ])
  have hηc : a z ≫ η.app d = η.app c := by
    exact (η.naturality ac).trans (Category.comp_id _)
  have hηs : g ≫ η.app d = η.app s := by
    exact (η.naturality as).trans (Category.comp_id _)
  have hdv : D.ι.app z ≫ v = η.app d := by
    -- The two maps agree on c.B, so principal-localization extensionality applies.
    apply CommRingCat.hom_ext
    apply CommRingCat.awayProd_ringHom_ext c.q.asIdeal
    intro x
    have H : a z ≫ D.ι.app z ≫ v = a z ≫ η.app d := by
      rw [← Category.assoc, ha, hv, hηc]
    exact congrArg (fun k : c.B ⟶ V ↦ k.hom x) H
  rw [hg, Category.assoc, hdv, hηs]

/-- Given a cocone `η` on the pointed étale ring diagram over `(R, p)` and a pointed étale
triple `t` over `R_p`, there is a ring map `b : t.B ⟶ V` with `β ≫ b = η.app s` for every
compatible pointed map `β` from a triple `s` over `(R, p)` to `t`. -/
theorem etaleResidueTriples_primeLocalization_component_extension_exists
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
    ∃ b : t.B ⟶ V,
      ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
        s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
          t.α →
        β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
        β ≫ b = η.app s := by
  classical
  -- Descend the algebra first, then construct its pointing from the given map to K.
  obtain ⟨C, a, i, ha, hai, M, hM⟩ :=
    primeLocalization_etale_algebra_model R p t.B t.α t.etale
  let τ := (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ
  have hc : a ≫ (i ≫ τ) = (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ := by
    rw [← Category.assoc, hai, Category.assoc]
    change CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      t.α ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ = _
    rw [t.compatible, hψ, hK]
  let c := triple_of_point C a (i ≫ τ) ha hc
  have hcp : (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ = i ≫ τ :=
    triple_of_point_point C a (i ≫ τ) ha hc
  let : Algebra C t.B := i.hom.toAlgebra
  have : IsLocalization M t.B := hM
  let L := Localization.AtPrime c.q.asIdeal
  let l : c.B ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap c.B L)
  have hm (m : M) : (m : C) ∉ c.q.asIdeal := by
    have hu : IsUnit ((i ≫ τ).hom m) :=
      (IsLocalization.map_units t.B m).map τ.hom
    intro hmem
    have hz := (pointing_zero_iff c (m : C)).mpr hmem
    rw [hcp] at hz
    exact hu.ne_zero hz
  -- Every denominator is outside the pointed prime, giving t.B → C at that prime.
  let j : t.B ⟶ CommRingCat.of L := CommRingCat.ofHom
    (IsLocalization.lift (S := t.B) (g := algebraMap C L)
      (fun m : M ↦ IsLocalization.map_units (M := c.q.asIdeal.primeCompl)
        L ⟨(m : C), hm m⟩))
  have hij : i ≫ j = l := by
    apply CommRingCat.hom_ext
    exact IsLocalization.lift_comp _
  let δ : CommRingCat.of L ⟶ CommRingCat.of K := CommRingCat.ofHom
    (IsLocalization.lift (S := L)
      (g := ((ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ).hom)
      (fun m : c.q.asIdeal.primeCompl ↦ IsUnit.mk0 _
        (fun H ↦ m.property ((pointing_zero_iff c m).mp H))))
  have hδ : l ≫ δ = (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ := by
    apply CommRingCat.hom_ext
    exact IsLocalization.lift_comp _
  let v : CommRingCat.of L ⟶ V := CommRingCat.ofHom
    (IsLocalization.lift (R := c.B) (S := L) (g := (η.app c).hom)
      (fun m : c.q.asIdeal.primeCompl ↦ cocone_leg_isUnit η c m m.property))
  have hv : l ≫ v = η.app c := by
    apply CommRingCat.hom_ext
    exact IsLocalization.lift_comp _
  have hj : j ≫ δ = τ := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext M (S := t.B)
    have H : i ≫ j ≫ δ = i ≫ τ := by
      rw [← Category.assoc, hij, hδ, hcp]
    exact congrArg CommRingCat.Hom.hom H
  refine ⟨j ≫ v, ?_⟩
  intro s β hβα hβφ
  rw [← Category.assoc]
  apply cocone_leg_atPrime η c δ hδ v hv s (β ≫ j)
  · change s.α ≫ β ≫ j = a ≫ l
    rw [← Category.assoc, hβα, ← hai, Category.assoc, hij]
  · rw [Category.assoc, hj]
    exact hβφ

end AlgebraicGeometry.Scheme

