/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius

/-!
# The finite-coefficient Lefschetz trace formula

For a Weil datum `(K, φ)` on the geometric base change `X` of a separated finite type
`𝐅_q`-scheme `X₀` and every `m ≥ 1`, the trace of the global Frobenius operator on
compactly supported cohomology is the sum of the traces of the local Frobenius operators
on the geometric stalks at the `𝐅_{q^m}`-rational points.

## Main results

- `AlgebraicGeometry.ProEtale.trace_globalOperator_eq_trace_add_trace`: additivity of the
  trace of the global operator along an open-closed decomposition.
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

In `trace_globalOperator_eq_trace_add_trace` the restrictions of the Frobenius to the open
and closed pieces are data `Φ_U`, `Φ_Z`, since the project does not construct restrictions of
morphisms to subschemes; the restricted Weil complexes are then `WeilComplex.upperStarPull`,
whose coefficient morphisms are the canonical `WeilComplex.upperStarPullCoeff`.
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

/-- Compact trace additivity: for a closed immersion `i : Z ⟶ X` and its open complement
`j : U ⟶ X`, the Frobenius coefficient morphisms induced on the functorial compact
localization triangle satisfy

`tr_A(F_{c,m}, RΓ_c(X, K)) = tr_A(F_{c,m}, RΓ_c(U, j^* K)) + tr_A(F_{c,m}, RΓ_c(Z, i^* K))`.

Invertibility of the coefficient morphism is unnecessary, so the statement is for plain
`WeilComplex`es (blueprint: `sk-i-global-additivity`). -/
theorem trace_globalOperator_eq_trace_add_trace (G : GeometricOperations A s)
    {U Z : Scheme.{u}} {aX : X ⟶ s} {aU : U ⟶ s} {aZ : Z ⟶ s}
    [IsGeometric aX] [IsGeometric aU] [IsGeometric aZ]
    [HasCompactification aX] [HasCompactification aU] [HasCompactification aZ]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    (hj : j ≫ aX = aU) (hi : i ≫ aX = aZ)
    (hcompl : IsCompl (Set.range j.base) (Set.range i.base))
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (frobU : U ⟶ U) (frobZ : Z ⟶ Z)
    (sqU : CommSq frobU j j (W.frobeniusIterate 1))
    (sqZ : CommSq frobZ i i (W.frobeniusIterate 1))
    (m : ℕ)
    [IsProper (W.graph G hW m).snd]
    [IsProper ((W.upperStarPull j hj frobU sqU).graph G
      (G.ctf_upperStar j (.mk hj) hW) m).snd]
    [IsProper ((W.upperStarPull i hi frobZ sqZ).graph G
      (G.ctf_upperStar i (.mk hi) hW) m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [HasRightDual ((rightDerivedLowerShriek A aU).obj (W.upperStarPull j hj frobU sqU).obj)]
    [HasRightDual ((rightDerivedLowerShriek A aZ).obj (W.upperStarPull i hi frobZ sqZ).obj)] :
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G hW m) hW) =
      MonoidalCategory.trace
          (Correspondence.globalOperator G
            ((W.upperStarPull j hj frobU sqU).graph G (G.ctf_upperStar j (.mk hj) hW) m)
            (G.ctf_upperStar j (.mk hj) hW)) +
        MonoidalCategory.trace
          (Correspondence.globalOperator G
            ((W.upperStarPull i hi frobZ sqZ).graph G (G.ctf_upperStar i (.mk hi) hW) m)
            (G.ctf_upperStar i (.mk hi) hW)) :=
  sorry

/-- **The finite-coefficient Lefschetz trace formula.** For every Weil datum on the
geometric base change `X = X₀ ×_{𝐅_q} Ω` of a separated finite type `X₀/𝐅_q`, `Ω`
algebraically closed, whose Frobenius is the base change of the `q`-power Frobenius of `X₀`,
and every `m ≥ 1`,

`tr_A(F_{c,m} ∣ RΓ_c(X, K)) = ∑_{x ∈ X₀(𝐅_{q^m})} tr_A(F_{x,m} ∣ K_x̄)`,

the sum running over the sections `x` of `a_X` fixed by `Φ_m`
(blueprint: `sk-thm-trace-formula`). -/
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
  sorry

end AlgebraicGeometry.ProEtale
