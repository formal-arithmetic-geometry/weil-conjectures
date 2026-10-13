/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine

/-!
# The trace formula for affine models

Step 4 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace formula
holds for closed subschemes of `𝔸ⁿ_k`, by induction on `n` through `𝔸ⁿ⁺¹_k ≅ 𝔸¹_{𝔸ⁿ_k}`, and
hence for every affine model of finite type over `k`.

## Main results

- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isClosedImmersion_affineSpace`: closed
  subschemes of affine space.
- `AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isAffine`: affine models.
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

/-- The trace formula for an affine model `f₀ : X₀ ⟶ Spec k` whose ring of global sections is
generated over `k` by `n` elements `t`, by induction on `n`: the morphism `X₀ ⟶ 𝔸¹_{𝔸ⁿ_k}` given
by `t` is a closed immersion, so `traceFormulaHolds_of_isClosedImmersion_relativeAffineLine`
applies, with the induction hypothesis for the closed subschemes of `𝔸ⁿ_k`. For `n = 0`, `f₀` is
a closed immersion, hence finite. -/
theorem traceFormulaHolds_of_surjective_eval₂Hom (n : ℕ) {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k)) [IsAffine X₀] (t : ULift.{u} (Fin n) → Γ(X₀, ⊤))
    (ht : Function.Surjective
      (MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of k)).inv ≫ f₀.appTop).hom t)) :
    TraceFormulaHolds A f₀ := by
  induction n generalizing X₀ with
  | zero =>
    have : IsClosedImmersion f₀ := by
      refine IsClosedImmersion.of_surjective_of_isAffine _ fun y ↦ ?_
      obtain ⟨p, rfl⟩ := ht y
      refine ⟨(Scheme.ΓSpecIso (.of k)).inv (MvPolynomial.coeff 0 p), ?_⟩
      conv_rhs => rw [MvPolynomial.eq_C_of_isEmpty p]
      simp
    apply traceFormulaHolds_of_isFinite
  | succ n ih =>
    have hY {Z₀ : Scheme.{u}} (i : Z₀ ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k)))
        [IsClosedImmersion i] :
        TraceFormulaHolds A (i ≫ 𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) := by
      have := isAffine_of_isAffineHom i
      apply ih
      exact AffineSpace.surjective_eval₂Hom_appTop_coord i
    let j' := AffineSpace.homOfVector f₀ fun l : ULift.{u} (Fin n) ↦ t ⟨l.down.succ⟩
    have : IsClosedImmersion (AffineSpace.homOfVector j' fun _ : PUnit.{u + 1} ↦ t ⟨0⟩) := by
      refine AffineSpace.isClosedImmersion_homOfVector j' _ ((Subring.eq_top_iff' _).mpr fun y ↦ ?_)
      obtain ⟨p, rfl⟩ := ht y
      induction p using MvPolynomial.induction_on with
      | C a =>
        refine Subring.subset_closure (Or.inl ⟨(𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘
          Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv a), ?_⟩)
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over]
        simp
      | add p q hp hq =>
        rw [map_add]
        exact add_mem hp hq
      | mul_X p l hp =>
        rw [map_mul, MvPolynomial.eval₂Hom_X']
        refine mul_mem hp (Subring.subset_closure ?_)
        obtain ⟨l⟩ := l
        induction l using Fin.cases with
        | zero => exact Or.inr ⟨PUnit.unit, rfl⟩
        | succ l =>
          exact Or.inl ⟨AffineSpace.coord _ ⟨l⟩, AffineSpace.homOfVector_appTop_coord _ _ _⟩
    rw [← AffineSpace.homOfVector_over f₀ fun l : ULift.{u} (Fin n) ↦ t ⟨l.down.succ⟩,
      ← AffineSpace.homOfVector_over (AffineSpace.homOfVector f₀ fun l : ULift.{u} (Fin n) ↦
        t ⟨l.down.succ⟩) fun _ : PUnit.{u + 1} ↦ t ⟨0⟩, Category.assoc]
    apply traceFormulaHolds_of_isClosedImmersion_relativeAffineLine
    · intro Z₀ i _
      apply hY
    · intro k' _ _ Z₀ i _
      apply traceFormulaHolds_of_isClosedImmersion_affineLine

/-- Step 4 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace
formula for closed subschemes of the affine space `𝔸ⁿ_k`, by induction on `n` through
`𝔸ⁿ⁺¹_k ≅ 𝔸¹_{𝔸ⁿ_k}` (`traceFormulaHolds_of_isClosedImmersion_relativeAffineLine`), starting
from closed subschemes of `𝔸⁰_k = Spec k`, which are finite over `k`. -/
theorem traceFormulaHolds_of_isClosedImmersion_affineSpace (n : ℕ) {Z₀ : Scheme.{u}}
    (i : Z₀ ⟶ 𝔸(ULift.{u} (Fin n); Spec (.of k))) [IsClosedImmersion i] :
    TraceFormulaHolds A (i ≫ 𝔸(ULift.{u} (Fin n); Spec (.of k)) ↘ Spec (.of k)) := by
  have := isAffine_of_isAffineHom i
  apply traceFormulaHolds_of_surjective_eval₂Hom
  exact AffineSpace.surjective_eval₂Hom_appTop_coord i

/-- The trace formula for affine models of finite type over `k`: an affine `X₀` of finite type is
a closed subscheme of some `𝔸ⁿ_k` (Steps 1–4 of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`). -/
theorem traceFormulaHolds_of_isAffine {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k)) [IsAffine X₀]
    [LocallyOfFiniteType f₀] : TraceFormulaHolds A f₀ := by
  have hft : ((Scheme.ΓSpecIso (.of k)).inv ≫ f₀.appTop).hom.FiniteType := by
    rw [CommRingCat.hom_comp]
    exact (HasRingHomProperty.appTop @LocallyOfFiniteType f₀ ‹_›).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f₀.appTop).hom.toAlgebra
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  have hs : Function.Surjective (MvPolynomial.eval₂Hom
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f₀.appTop).hom
        fun l : ULift.{u} (Fin n) ↦ f (.X l.down)) := by
    intro y
    obtain ⟨p, rfl⟩ := hf y
    refine ⟨MvPolynomial.rename ULift.up p, ?_⟩
    conv_rhs => rw [MvPolynomial.aeval_unique f]
    exact MvPolynomial.aeval_rename _ _ _
  apply traceFormulaHolds_of_surjective_eval₂Hom
  exact hs

end AlgebraicGeometry.ProEtale
