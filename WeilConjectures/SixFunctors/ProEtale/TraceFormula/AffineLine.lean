/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep

/-!
# The trace formula on the affine line and its closed subschemes

Steps 2 and 3 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`. For the
affine line, push forward along the open immersion `𝔸¹_k ⊆ ℙ¹_k`
(`traceFormulaHolds_comp_of_traceFormulaHolds_fibre`): the trace formula holds on the proper
smooth curve `ℙ¹_k` (`traceFormulaHolds_of_smoothOfRelativeDimension_one`), and the fibres of
`𝔸¹ ⊆ ℙ¹` over points with values in finite fields are a point or empty, hence finite (Step 1).
A closed subscheme of `𝔸¹_k` is the line itself or finite over `k`.

## Main results

- `AlgebraicGeometry.ProEtale.traceFormulaHolds_affineLine`: Step 2.
- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isClosedImmersion_affineLine`: Step 3.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {k : Type u} [Field k] [Finite k]

/-- An open immersion into the spectrum of a field is finite: its source is empty, or it is
surjective onto the single point of `Spec K`, hence an isomorphism. -/
lemma _root_.AlgebraicGeometry.isFinite_of_isOpenImmersion_spec {K : Type u} [Field K]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) [IsOpenImmersion f] : IsFinite f := by
  cases isEmpty_or_nonempty U
  · infer_instance
  · obtain ⟨x⟩ := ‹Nonempty U›
    have : IsIso f := isIso_of_isOpenImmersion_of_opensRange_eq_top f
      (eq_top_iff.mpr fun y _ ↦ ⟨x, Subsingleton.elim _ _⟩)
    infer_instance

/-- Step 2 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace
formula for the affine line `𝔸¹_k`, by the Weil `!`-pushforward along the open immersion
`𝔸¹_k ⊆ ℙ¹_k`, from the trace formula on the proper smooth curve `ℙ¹_k` (Lefschetz–Verdier
formula and Frobenius local terms) and on the fibres, which are a point or empty (Step 1). -/
theorem traceFormulaHolds_affineLine :
    TraceFormulaHolds A (𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) := by
  have : QuasiCompact (ProjectiveLine.affineChart (Spec (.of k))) := by
    have : QuasiCompact (ProjectiveLine.affineChart (Spec (.of k)) ≫
        ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
      rw [ProjectiveLine.affineChart_over]
      infer_instance
    exact QuasiCompact.of_comp _ (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  rw [← ProjectiveLine.affineChart_over]
  apply traceFormulaHolds_comp_of_traceFormulaHolds_fibre
  · apply traceFormulaHolds_of_smoothOfRelativeDimension_one
  · intro k' _ _ y₀
    have := isFinite_of_isOpenImmersion_spec
      (pullback.snd (ProjectiveLine.affineChart (Spec (.of k))) y₀)
    apply traceFormulaHolds_of_isFinite

/-- Step 3 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace
formula for closed subschemes of the affine line `𝔸¹_k`. A closed subscheme `Spec k[t]/I` is the
line itself if `I = 0` (Step 2), and finite over `k` otherwise (Step 1). -/
theorem traceFormulaHolds_of_isClosedImmersion_affineLine {Z₀ : Scheme.{u}}
    (i : Z₀ ⟶ 𝔸(PUnit.{u + 1}; Spec (.of k))) [IsClosedImmersion i] :
    TraceFormulaHolds A (i ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) := by
  have := isAffine_of_isAffineHom i
  obtain hinj | hinj := em (Function.Injective (MvPolynomial.eval₂Hom
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)).appTop).hom
      fun j ↦ i.appTop (AffineSpace.coord (Spec (.of k)) j)))
  · rw [AffineSpace.eval₂Hom_appTop_coord, RingHom.coe_comp] at hinj
    have : IsIso i := IsClosedImmersion.isIso_of_injective_of_isAffine
      (hinj.of_comp_right (AffineSpace.bijective_eval₂Hom_coord _).2)
    apply TraceFormulaHolds.of_iso (asIso i)
    apply traceFormulaHolds_affineLine
  rw [injective_iff_map_eq_zero] at hinj
  push Not at hinj
  obtain ⟨p, hp, hp0⟩ := hinj
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (i ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)).appTop).hom.toAlgebra
  set x := i.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)
  have hx : _root_.IsIntegral k x := by
    refine IsAlgebraic.isIntegral ⟨MvPolynomial.uniqueAlgEquiv k PUnit p, 
      (map_ne_zero_iff _ (AlgEquiv.injective _)).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def]
    exact (MvPolynomial.eval₂_uniqueAlgEquiv (a := fun _ ↦ x)).trans hp
  have hadj : Algebra.adjoin k {x} = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨q, rfl⟩ := AffineSpace.surjective_eval₂Hom_appTop_coord i y
    exact Algebra.adjoin_mono (Set.range_subset_singleton.mpr rfl)
      ((Algebra.adjoin_range_eq_range_aeval k fun _ : PUnit.{u + 1} ↦ x).ge ⟨q, rfl⟩)
  have hfin : ((Scheme.ΓSpecIso (.of k)).inv ≫
      (i ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)).appTop).hom.Finite := by
    rw [RingHom.Finite, Module.finite_def, ← Algebra.top_toSubmodule, ← hadj]
    exact hx.fg_adjoin_singleton
  have : IsFinite (i ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)) := by
    refine (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr ⟨inferInstance, ?_⟩
    rw [← (Scheme.ΓSpecIso (.of k)).hom_inv_id_assoc
      (i ≫ 𝔸(PUnit.{u + 1}; Spec (.of k)) ↘ Spec (.of k)).appTop, CommRingCat.hom_comp]
    exact hfin.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom).2)
  apply traceFormulaHolds_of_isFinite


end AlgebraicGeometry.ProEtale
