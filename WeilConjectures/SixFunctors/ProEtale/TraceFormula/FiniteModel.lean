/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward

/-!
# The trace formula for schemes finite over the base

Step 1 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: the trace formula
for a Weil complex on a scheme `X` finite over `s = Spec Ω`, `Ω` algebraically closed. If the
Frobenius has no fixed point, both sides vanish: the Lefschetz–Verdier formula
(`GeometricOperations.trace_globalOperator_eq_sum_localTerm`) on the proper `X` is a sum over the
components of the empty fixed scheme. Otherwise a fixed section `x : s ⟶ X` is a closed immersion
with open complement stable under the Frobenius, the trace formula over the point `x` is
`WeilComplex.traceFormula_of_eq_id`, and induction on the number of points of `X` with the
additivity `WeilComplex.traceFormula_of_isCompl` concludes.

## Main results

- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_of_forall_base_ne`: no fixed points.
- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_one_of_isFinite`: degree one, for a
  Frobenius bijective on points.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale.WeilComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {X : Scheme.{u}}

/-- If `Φ_m` has no fixed point on a scheme `X` proper over `s = Spec Ω`, both sides of the trace
formula vanish: the Lefschetz–Verdier formula is a sum over the empty set of components of the
fixed scheme, and there are no fixed sections. -/
theorem traceFormula_of_forall_base_ne {Ω : Type u} [Field Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {aX : X ⟶ Spec (.of Ω)} [IsGeometric aX]
    [HasCompactification aX] [IsProper aX] (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj)
    (m : ℕ) [IsProper (W.graph G hW m).snd] (h : ∀ y : X, (W.frobeniusIterate m).base y ≠ y) :
    W.TraceFormula G hW m :=
  sorry

/-- The trace formula in degree one for a Weil complex on a scheme `X` finite over `Spec Ω`,
`Ω` algebraically closed, whose Frobenius is bijective on points, by induction on the number of
points of `X`. -/
theorem traceFormula_one_of_isFinite {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {aX : X ⟶ Spec (.of Ω)} [IsFinite aX]
    [HasCompactification aX] (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj)
    (hbij : Function.Bijective W.frobenius.base) [IsProper (W.graph G hW 1).snd] :
    W.TraceFormula G hW 1 :=
  sorry

end AlgebraicGeometry.ProEtale.WeilComplex
