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

Rational points are rendered as the `s`-points of `X` fixed by `Φ_m`; over `s = Spec k`
with `k` an algebraic closure of `𝐅_q` these are exactly `X₀(𝐅_{q^m})`. Their finiteness
is an instance hypothesis.

Both traces are the categorical trace of a dualizable — that is, perfect — object, so
`HasRightDual` appears as a hypothesis on the compactly supported cohomology and on each
geometric stalk, and the braiding of `D(s, A)` is an instance hypothesis: this project
installs a monoidal structure on a derived category but not yet a braiding.

The local Frobenius `WeilComplex.stalkFrobenius` is defined in
`WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius`.

In `trace_globalOperator_eq_trace_add_trace` the restriction of a Weil complex to an open
or closed piece is not constructed in this project, so the two restricted Weil complexes
are taken as data. They are tied to `W` by more than an isomorphism of the underlying
complexes: the hypotheses `hjfrob`/`hifrob` say that the two Frobenius morphisms restrict,
and `hjcoeff`/`hicoeff` say that the two coefficient morphisms are the restrictions of
`φ`, along the comparison isomorphisms `cU`, `cZ` for the commuting Frobenius squares that
this project does not construct.
-/

@[expose] public section

universe u' u

set_option linter.unusedVariables false

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [DerivedBraiding A] {s X : Scheme.{u}}

/-- Compact trace additivity: for a closed immersion `i : Z ⟶ X` and its open complement
`j : U ⟶ X`, the Frobenius coefficient morphisms induced on the functorial compact
localization triangle satisfy

`tr_A(F_{c,m}, RΓ_c(X, K)) = tr_A(F_{c,m}, RΓ_c(U, j^* K)) + tr_A(F_{c,m}, RΓ_c(Z, i^* K))`.

Invertibility of the coefficient morphism is unnecessary, so the statement is for plain
`WeilComplex`es (blueprint: `sk-i-global-additivity`). -/
theorem trace_globalOperator_eq_trace_add_trace (G : GeometricOperations A s)
    {U Z : Scheme.{u}} {aX : X ⟶ s} {aU : U ⟶ s} {aZ : Z ⟶ s}
    [HasCompactification aX] [HasCompactification aU] [HasCompactification aZ]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    (hj : j ≫ aX = aU) (hi : i ≫ aX = aZ)
    (hcompl : IsCompl (Set.range j.base) (Set.range i.base))
    (W : WeilComplex (A := A) aX) (WU : WeilComplex (A := A) aU)
    (WZ : WeilComplex (A := A) aZ)
    (eU : WU.obj ≅ ((upperStar A j).leftDerivedFunctor).obj W.obj)
    (eZ : WZ.obj ≅ ((upperStar A i).leftDerivedFunctor).obj W.obj)
    (hjfrob : j ≫ W.frobenius = WU.frobenius ≫ j)
    (hifrob : i ≫ W.frobenius = WZ.frobenius ≫ i)
    (cU : ((upperStar A WU.frobenius).leftDerivedFunctor).obj WU.obj ≅
      ((upperStar A j).leftDerivedFunctor).obj
        (((upperStar A W.frobenius).leftDerivedFunctor).obj W.obj))
    (cZ : ((upperStar A WZ.frobenius).leftDerivedFunctor).obj WZ.obj ≅
      ((upperStar A i).leftDerivedFunctor).obj
        (((upperStar A W.frobenius).leftDerivedFunctor).obj W.obj))
    (hjcoeff : WU.coeff ≫ eU.hom =
      cU.hom ≫ ((upperStar A j).leftDerivedFunctor).map W.coeff)
    (hicoeff : WZ.coeff ≫ eZ.hom =
      cZ.hom ≫ ((upperStar A i).leftDerivedFunctor).map W.coeff)
    (m : ℕ)
    [IsProper (W.graph G m).snd]
    [IsProper (WU.graph G m).snd]
    [IsProper (WZ.graph G m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [HasRightDual ((rightDerivedLowerShriek A aU).obj WU.obj)]
    [HasRightDual ((rightDerivedLowerShriek A aZ).obj WZ.obj)] :
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G m)) =
      MonoidalCategory.trace (Correspondence.globalOperator G (WU.graph G m)) +
        MonoidalCategory.trace (Correspondence.globalOperator G (WZ.graph G m)) :=
  sorry

/-- **The finite-coefficient Lefschetz trace formula.** For every Weil datum on a separated
finite type `X₀/𝐅_q` and every `m ≥ 1`,

`tr_A(F_{c,m} ∣ RΓ_c(X, K)) = ∑_{x ∈ X₀(𝐅_{q^m})} tr_A(F_{x,m} ∣ K_x̄)`,

the sum running over the `s`-points of `X` fixed by `Φ_m`
(blueprint: `sk-thm-trace-formula`). -/
theorem trace_globalOperator_eq_sum_trace_stalkFrobenius (G : GeometricOperations A s)
    {aX : X ⟶ s} [HasCompactification aX] (W : WeilComplex (A := A) aX)
    (hW : IsIso W.coeff) (hctf : G.ctf X W.obj) (m : ℕ) (hm : 1 ≤ m)
    [IsProper (W.graph G m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [Fintype {x : s ⟶ X // x ≫ W.frobeniusIterate m = x}]
    [∀ x : s ⟶ X, HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)] :
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G m)) =
      ∑ x : {x : s ⟶ X // x ≫ W.frobeniusIterate m = x},
        MonoidalCategory.trace (W.stalkFrobenius m x.1 x.2) :=
  sorry

end AlgebraicGeometry.ProEtale
