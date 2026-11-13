/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation

/-! # Surjectivity of pointed evaluation

## References

* [Stacks Project, Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public section

universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The codomain-restricted pointed evaluation ring homomorphism. -/
noncomputable def strictHenselizationPointEvaluationToSep
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (descResidueField (stalkClosedPointTo barY)).hom) :
    strictHenselization barY →+*
      separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω :=
  (strictHenselizationPointEvaluation barY).codRestrict _
    (strictHenselizationPointEvaluation_mem barY hΩ)

/-- The codomain-restricted pointed evaluation map is surjective. -/
theorem strictHenselizationPointEvaluationToSep_surjective
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (descResidueField (stalkClosedPointTo barY)).hom) :
    Function.Surjective (strictHenselizationPointEvaluationToSep barY hΩ) := by
  classical
  obtain ⟨A, i, hi, hx, _⟩ := exists_affine_mem_range_and_range_subset
    (x := barY (IsLocalRing.closedPoint Ω)) (U := ⊤) (by simp)
  let := hi
  have hrange : Set.range barY ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint Ω)] using hx
  let xU := IsOpenImmersion.lift i barY hrange
  have hfac : xU ≫ i = barY := IsOpenImmersion.lift_fac i barY hrange
  let p := (SpecToEquivOfField Ω (Spec A) xU).1
  let F := (Spec A).residueField p
  let emb := (SpecToEquivOfField Ω (Spec A) xU).2
  let : Algebra F Ω := emb.hom.toAlgebra
  let K := separableClosure F Ω
  obtain ⟨_, c, ⟨hc⟩, _, _, ψ, _, hψ, hsurj, _⟩ :=
    strictHenselization_triples A p K
  obtain ⟨e, he⟩ := strictHenselizationPointEvaluation_comparison A i xU c hc ψ hψ
  let G := Y.residueField (barY (IsLocalRing.closedPoint Ω))
  have hp : i p = barY (IsLocalRing.closedPoint Ω) :=
    congrArg (fun f : Spec (.of Ω) ⟶ Y ↦ f (IsLocalRing.closedPoint Ω)) hfac
  let b : G ≅ F := (Y.residueFieldCongr hp).symm ≪≫ asIso (i.residueFieldMap p)
  have hmaps : (algebraMap F Ω).comp b.hom.hom = algebraMap G Ω := by
    obtain ⟨_, hh⟩ := SpecToEquivOfField_eq_iff.mp
      (congrArg (SpecToEquivOfField Ω Y) hfac)
    dsimp [SpecToEquivOfField] at hh
    rw [descResidueField_stalkClosedPointTo_comp] at hh
    have hh' := congrArg (fun f ↦ (Y.residueFieldCongr hp).inv ≫ f) hh
    simp only [Iso.inv_hom_id_assoc] at hh'
    change emb.hom.comp b.hom.hom = _
    rw [hΩ]
    exact congrArg CommRingCat.Hom.hom hh'
  intro y
  have hy : IsSeparable G (y : Ω) := mem_separableClosure_iff.mp y.property
  have hyF : IsSeparable F (y : Ω) :=
    hy.of_equiv_equiv b.commRingCatIsoToRingEquiv (RingEquiv.refl Ω) hmaps
  obtain ⟨z, hz⟩ := hsurj (⟨y, mem_separableClosure_iff.mpr hyF⟩ : K)
  let a := e.inv z
  have hval : strictHenselizationPointEvaluation (xU ≫ i) a = (y : Ω) := by
    rw [← he a]
    have hez : e.hom (e.inv z) = z := ConcreteCategory.congr_hom e.inv_hom_id z
    change (ψ (e.hom (e.inv z)) : Ω) = (y : Ω)
    rw [hez]
    exact congrArg Subtype.val hz
  refine ⟨(hfac ▸ a), ?_⟩
  apply Subtype.ext
  change strictHenselizationPointEvaluation barY (hfac ▸ a) = (y : Ω)
  have transport : ∀ (s t : Spec (.of Ω) ⟶ Y) (h : s = t)
      (a : strictHenselization s),
      strictHenselizationPointEvaluation t (h ▸ a) =
        strictHenselizationPointEvaluation s a := by
    intro s t h a
    cases h
    rfl
  exact (transport _ _ hfac a).trans hval

end AlgebraicGeometry.Scheme
