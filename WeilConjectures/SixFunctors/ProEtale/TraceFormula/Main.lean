/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius

/-!
# The finite-coefficient Lefschetz trace formula

For a Weil datum `(K, φ)` on the geometric base change `X` of a separated finite type
`𝐅_q`-scheme `X₀` and every `m ≥ 1`, the trace of the global Frobenius operator on
compactly supported cohomology is the sum of the traces of the local Frobenius operators
on the geometric stalks at the `𝐅_{q^m}`-rational points.

Rational points are rendered as the `s`-points of `X` fixed by `Φ_m`; over `s = Spec k`
with `k` an algebraic closure of `𝐅_q` these are exactly `X₀(𝐅_{q^m})`.

## Main results

- `AlgebraicGeometry.ProEtale.trace_globalOperator_add` (blueprint
  `sk-i-global-additivity`)
- `AlgebraicGeometry.ProEtale.trace_globalOperator_eq_sum_trace_stalkFrobenius` (blueprint
  `sk-thm-trace-formula`)
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X : Scheme.{u}}

/-- The geometric-stalk Frobenius `F_{x,m} = (φ_m)_x̄` of a Weil complex at a point
`x : s ⟶ X` fixed by `Φ_m`: the composite of the comparison
`Lx^* K ≃ L(x ≫ Φ_m)^* K ≃ Lx^* Φ_m^* K` supplied by `leftDerivedUpperStarComp` and `hx`
with `Lx^* φ_m`. -/
noncomputable def WeilComplex.stalkFrobenius {aX : X ⟶ s} (W : WeilComplex (A := A) aX)
    (m : ℕ) (x : s ⟶ X) (_hx : x ≫ W.frobeniusIterate m = x) :
    ((upperStar A x).leftDerivedFunctor).obj W.obj ⟶
      ((upperStar A x).leftDerivedFunctor).obj W.obj :=
  sorry

/-- Blueprint `sk-i-global-additivity`: Compact trace additivity.

For a closed immersion `i : Z ⟶ X` and its open complement `j : U ⟶ X`, the Frobenius
coefficient morphisms induced on the functorial compact localization triangle satisfy

`tr_A(F_{c,m}, RΓ_c(X, K)) = tr_A(F_{c,m}, RΓ_c(U, j^* K)) + tr_A(F_{c,m}, RΓ_c(Z, i^* K))`.

All three are traces of perfect complexes, rendered as `HasRightDual` hypotheses on the
three compactly supported cohomologies; invertibility of the coefficient morphism is
unnecessary, so the statement is for plain `WeilComplex`es. The restricted Weil complexes
on `U` and on `Z` are taken as data, together with isomorphisms identifying their
underlying complexes with `Lj^* K` and `Li^* K`: the restriction of the Frobenius to an
open or closed piece is not constructed in this project.

The braiding of `D(s, A)` is an instance hypothesis, since this project installs a
monoidal structure on a derived category but not yet a braiding. -/
theorem trace_globalOperator_add (G : GeometricOperations A s)
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    {U Z : Scheme.{u}} {aX : X ⟶ s} {aU : U ⟶ s} {aZ : Z ⟶ s}
    [HasCompactification aX] [HasCompactification aU] [HasCompactification aZ]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    (_hj : j ≫ aX = aU) (_hi : i ≫ aX = aZ)
    (_hcompl : IsCompl (Set.range j.base) (Set.range i.base))
    (W : WeilComplex (A := A) aX) (WU : WeilComplex (A := A) aU)
    (WZ : WeilComplex (A := A) aZ)
    (_hU : Nonempty (WU.obj ≅ ((upperStar A j).leftDerivedFunctor).obj W.obj))
    (_hZ : Nonempty (WZ.obj ≅ ((upperStar A i).leftDerivedFunctor).obj W.obj))
    (m : ℕ)
    [IsProper (W.graph m).snd] [HasCompactification (W.graph m).snd]
    [IsProper (WU.graph m).snd] [HasCompactification (WU.graph m).snd]
    [IsProper (WZ.graph m).snd] [HasCompactification (WZ.graph m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [HasRightDual ((rightDerivedLowerShriek A aU).obj WU.obj)]
    [HasRightDual ((rightDerivedLowerShriek A aZ).obj WZ.obj)] :
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph m)) =
      MonoidalCategory.trace (Correspondence.globalOperator G (WU.graph m)) +
        MonoidalCategory.trace (Correspondence.globalOperator G (WZ.graph m)) :=
  sorry

/-- Blueprint `sk-thm-trace-formula`: Finite-coefficient Lefschetz trace formula.

For every Weil datum on a separated finite type `X₀/𝐅_q` and every `m ≥ 1`,

`tr_A(F_{c,m} ∣ RΓ_c(X, K)) = ∑_{x ∈ X₀(𝐅_{q^m})} tr_A(F_{x,m} ∣ K_x̄)`.

The sum runs over the `s`-points of `X` fixed by `Φ_m`, which for `s = Spec k` are the
`𝐅_{q^m}`-rational points of `X₀`; their finiteness is an instance hypothesis. The global
operator is `Correspondence.globalOperator` applied to the graph correspondence
`c_m = (id, Φ_m)`, the local one is `WeilComplex.stalkFrobenius`, and both traces are the
categorical trace of a dualizable — that is, perfect — object, so `HasRightDual` appears
as a hypothesis on the compactly supported cohomology and on each geometric stalk. The
braiding of `D(s, A)` is an instance hypothesis for the same reason as in
`trace_globalOperator_add`. -/
theorem trace_globalOperator_eq_sum_trace_stalkFrobenius (G : GeometricOperations A s)
    [BraidedCategory (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))]
    {aX : X ⟶ s} [HasCompactification aX] (W : WeilComplex (A := A) aX)
    (_hW : IsIso W.coeff) (_hctf : G.ctf X W.obj) (m : ℕ) (_hm : 1 ≤ m)
    [IsProper (W.graph m).snd] [HasCompactification (W.graph m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [Fintype {x : s ⟶ X // x ≫ W.frobeniusIterate m = x}]
    [∀ x : s ⟶ X, HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)] :
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph m)) =
      ∑ x : {x : s ⟶ X // x ≫ W.frobeniusIterate m = x},
        MonoidalCategory.trace (W.stalkFrobenius m x.1 x.2) :=
  sorry

end AlgebraicGeometry.ProEtale
