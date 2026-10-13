/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.AlgebraicGeometry.OpenClosedInduction
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness

/-!
# The finite-coefficient Lefschetz trace formula

For a Weil datum `(K, φ)` on the geometric base change `X` of a separated finite type
`𝐅_q`-scheme `X₀` and every `m ≥ 1`, the trace of the global Frobenius operator on
compactly supported cohomology is the sum of the traces of the local Frobenius operators
on the geometric stalks at the `𝐅_{q^m}`-rational points.

## Main results

- `AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius.traceFormula`: the trace formula for
  an arbitrary Frobenius coefficient morphism, by induction along an affine open cover.
- `AlgebraicGeometry.ProEtale.trace_globalOperator_eq_sum_trace_stalkFrobenius_of_coeff`: the
  same, in the form of blueprint `thm-trf-coefficient-morphism-trace-formula`.
- `AlgebraicGeometry.ProEtale.trace_globalOperator_eq_sum_trace_stalkFrobenius`: the
  finite-coefficient Lefschetz trace formula.

## Implementation notes

The trace formula is stated over `s = Spec Ω` for an algebraically closed field `Ω`, for a
Weil complex whose Frobenius is the base change of the `q`-power Frobenius of a separated
finite type model `X₀` over `𝐅_q` (`WeilComplex.IsModelFrobenius`). Rational points are
rendered as the sections `x : s ⟶ X` of `a_X` fixed by `Φ_m`; these are exactly
`X₀(𝐅_{q^m})`. Their finiteness is an instance hypothesis.

Both traces are the categorical trace of a dualizable — that is, perfect — object, so
`HasRightDual` appears as a hypothesis on the compactly supported cohomology and on each
geometric stalk, and the braiding of `D(s, A)` is an instance hypothesis: this project
installs a monoidal structure on a derived category but not yet a braiding.

The local Frobenius `WeilComplex.stalkFrobenius` is defined in
`WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius`.

The proof follows the blueprint: the affine case is
`AlgebraicGeometry.ProEtale.traceFormulaHolds_of_isAffine` (Steps 1–4), and the general case
splits off, along a finite affine open cover of `X₀`, closed subschemes of affine opens with
the additivity of `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_of_isCompl` (Step 5).
The restrictions of the Frobenius to the pieces come from
`AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius.exists_upperStarPull`.
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {s X : Scheme.{u}}

namespace WeilComplex.IsModelFrobenius

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (G : GeometricOperations A (Spec (.of Ω)))
  {k : Type u} [Field k] [Finite k]

/-- The trace formula for a Weil complex whose Frobenius is the base change of the `q`-power
Frobenius of a separated finite type model `X₀` over `k`, for every `m ≥ 1`. The affine
case is `traceFormulaHolds_of_isAffine`; the general case follows by induction on a finite affine
open cover of `X₀` (`Scheme.induction_on_isCompl`), splitting off at each step a closed
subscheme of an affine open, which is affine, by additivity of the trace formula
(`traceFormula_of_isCompl`) (Step 5 of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`). -/
theorem traceFormula {aX : X ⟶ Spec (.of Ω)} [IsGeometric aX]
    [HasCompactification aX] {W : WeilComplex (A := A) aX} {X₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k)} [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    {σ : Spec (.of Ω) ⟶ Spec (.of k)} {p : X ⟶ X₀} (hΦ : W.IsModelFrobenius f₀ σ p)
    (hctf : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m) [IsProper (W.graph G hctf m).snd] :
    W.TraceFormula G hctf m := by
  have : CompactSpace X₀ := (quasiCompact_iff_compactSpace f₀).mp inferInstance
  revert X W aX σ p
  refine Scheme.induction_on_isCompl (S := Spec (.of k))
    (P := fun {X₀} f₀ ↦ ∀ [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
      {X : Scheme.{u}} {aX : X ⟶ Spec (.of Ω)} [IsGeometric aX] [HasCompactification aX]
      {W : WeilComplex (A := A) aX} {σ : Spec (.of Ω) ⟶ Spec (.of k)} {p : X ⟶ X₀},
      W.IsModelFrobenius f₀ σ p → ∀ (hctf : G.ctf X W.obj) [IsProper (W.graph G hctf m).snd],
        W.TraceFormula G hctf m) ?_ ?_ f₀
  · intro X₀ f₀ _ _ _ _ X aX _ _ W σ p hΦ hctf _
    exact traceFormulaHolds_of_isAffine f₀ G hΦ hctf m hm
  · intro X₀ U₀ Z₀ f₀ j₀ i₀ _ _ _ hU₀ hcompl hU hZ _ _ _ X aX _ _ W σ p hΦ hctf _
    have : QuasiCompact (j₀ ≫ f₀) := (quasiCompact_iff_compactSpace _).mpr hU₀
    have : QuasiCompact (i₀ ≫ f₀) := inferInstance
    obtain ⟨frobU, sqU, hΦU⟩ :=
      hΦ.exists_upperStarPull W (pullback.fst p j₀) j₀ (pullback.snd p j₀)
        (IsPullback.of_hasPullback p j₀).flip fun F₀ hF₀ ↦
          hF₀.exists_comp_eq_of_isOpenImmersion f₀ j₀
    obtain ⟨frobZ, sqZ, hΦZ⟩ :=
      hΦ.exists_upperStarPull W (pullback.fst p i₀) i₀ (pullback.snd p i₀)
        (IsPullback.of_hasPullback p i₀).flip fun F₀ hF₀ ↦
          hF₀.exists_comp_eq_of_isClosedImmersion f₀ i₀
    have := hΦU.isGeometric
    have := hΦZ.isGeometric
    have := hΦU.isFinite_frobeniusIterate _ m
    have := hΦZ.isFinite_frobeniusIterate _ m
    have hctfU := G.ctf_upperStar (pullback.fst p j₀) (.mk (aY := aX) rfl) hctf
    have hctfZ := G.ctf_upperStar (pullback.fst p i₀) (.mk (aY := aX) rfl) hctf
    have : IsProper ((W.upperStarPull (pullback.fst p j₀) rfl frobU sqU).graph G hctfU m).snd :=
      inferInstanceAs
        (IsProper ((W.upperStarPull (pullback.fst p j₀) rfl frobU sqU).frobeniusIterate m))
    have : IsProper ((W.upperStarPull (pullback.fst p i₀) rfl frobZ sqZ).graph G hctfZ m).snd :=
      inferInstanceAs
        (IsProper ((W.upperStarPull (pullback.fst p i₀) rfl frobZ sqZ).frobeniusIterate m))
    have : HasRightDual ((rightDerivedLowerShriek A (pullback.fst p j₀ ≫ aX)).obj
        (W.upperStarPull (pullback.fst p j₀) rfl frobU sqU).obj) :=
      (G.nonempty_hasRightDual_rightDerivedLowerShriek _ hctfU).some
    have : HasRightDual ((rightDerivedLowerShriek A (pullback.fst p i₀ ≫ aX)).obj
        (W.upperStarPull (pullback.fst p i₀) rfl frobZ sqZ).obj) :=
      (G.nonempty_hasRightDual_rightDerivedLowerShriek _ hctfZ).some
    intro _ _ _
    exact traceFormula_of_isCompl G (pullback.fst p j₀) (pullback.fst p i₀) rfl rfl
      (isCompl_range_of_isPullback (IsPullback.of_hasPullback p j₀).flip
        (IsPullback.of_hasPullback p i₀).flip hcompl)
      W hctf frobU frobZ sqU sqZ m (hU hΦU hctfU) (hZ hΦZ hctfZ)

end WeilComplex.IsModelFrobenius

/-- Blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace formula for an arbitrary
Frobenius coefficient morphism `φ : LΦ₁^* K ⟶ K`, with no invertibility assumed. For a Weil
complex on the geometric base change `X = X₀ ×_{𝐅_q} Ω` of a separated finite type `X₀/𝐅_q`,
`Ω` algebraically closed, whose Frobenius is the base change of the `q`-power Frobenius of `X₀`,
and every `m ≥ 1`,

`tr_A(F_{c,m}(φ) ∣ RΓ_c(X, K)) = ∑_{x ∈ X₀(𝐅_{q^m})} tr_A(φ_{m, x̄} ∣ K_x̄)`. -/
theorem trace_globalOperator_eq_sum_trace_stalkFrobenius_of_coeff {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {aX : X ⟶ Spec (.of Ω)} [HasCompactification aX]
    (W : WeilComplex (A := A) aX) {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k)) [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (σ : Spec (.of Ω) ⟶ Spec (.of k)) (p : X ⟶ X₀) (hΦ : W.IsModelFrobenius f₀ σ p)
    (hctf : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    [IsProper (haveI := hΦ.isGeometric; W.graph G hctf m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [Fintype {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}]
    [∀ x : Spec (.of Ω) ⟶ X, HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)] :
    haveI := hΦ.isGeometric
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G hctf m) hctf) =
      ∑ x : {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x},
        MonoidalCategory.trace (W.stalkFrobenius m x.1 x.2.2) := by
  have := hΦ.isGeometric
  have h := hΦ.traceFormula G hctf m hm
  exact h

/-- **The finite-coefficient Lefschetz trace formula.** For every Weil datum on the
geometric base change `X = X₀ ×_{𝐅_q} Ω` of a separated finite type `X₀/𝐅_q`, `Ω`
algebraically closed, whose Frobenius is the base change of the `q`-power Frobenius of `X₀`,
and every `m ≥ 1`,

`tr_A(F_{c,m} ∣ RΓ_c(X, K)) = ∑_{x ∈ X₀(𝐅_{q^m})} tr_A(F_{x,m} ∣ K_x̄)`,

the sum running over the sections `x` of `a_X` fixed by `Φ_m`
(blueprint: `thm-trf-grothendieck-lefschetz-finite-ring`, subsection `sk-thm-trace-formula`). -/
theorem trace_globalOperator_eq_sum_trace_stalkFrobenius {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {aX : X ⟶ Spec (.of Ω)} [HasCompactification aX]
    (W : WeilComplex (A := A) aX) {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k)) [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (σ : Spec (.of Ω) ⟶ Spec (.of k)) (p : X ⟶ X₀) (hΦ : W.IsModelFrobenius f₀ σ p)
    (hW : IsIso W.coeff) (hctf : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    [IsProper (haveI := hΦ.isGeometric; W.graph G hctf m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [Fintype {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}]
    [∀ x : Spec (.of Ω) ⟶ X, HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)] :
    haveI := hΦ.isGeometric
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G hctf m) hctf) =
      ∑ x : {x : Spec (.of Ω) ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x},
        MonoidalCategory.trace (W.stalkFrobenius m x.1 x.2.2) :=
  trace_globalOperator_eq_sum_trace_stalkFrobenius_of_coeff G W f₀ σ p hΦ hctf m hm

end AlgebraicGeometry.ProEtale
