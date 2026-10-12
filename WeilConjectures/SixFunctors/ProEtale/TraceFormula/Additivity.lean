/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius

/-!
# Additivity of the trace formula along open-closed decompositions

For a Weil complex `(K, φ)` on `X` over `s = Spec Ω`, a closed immersion `i : Z ⟶ X` and the
complementary open immersion `j : U ⟶ X`, both stable under the Frobenius, the trace formula
for `X` follows from the trace formulas for the restricted Weil complexes on `U` and `Z`: the
traces of the global operators add up by `trace_globalOperator_eq_trace_add_trace`, and the
fixed points of `X` are the disjoint union of those of `U` and `Z`, with the same stalk traces.
This is the localization step (Step 5) of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.TraceFormula`: the statement of the trace formula
  for a Weil complex in degree `m`.

## Main results

- `AlgebraicGeometry.ProEtale.trace_globalOperator_eq_trace_add_trace`: additivity of the
  trace of the global operator along an open-closed decomposition.
- `AlgebraicGeometry.ProEtale.WeilComplex.trace_stalkFrobenius_upperStarPull`: the stalk
  Frobenius of a restricted Weil complex is the stalk Frobenius of the original one.
- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_of_isCompl`: the trace formula on `X`
  follows from the trace formulas on `U` and `Z`.

## Implementation notes

In `trace_globalOperator_eq_trace_add_trace` the restrictions of the Frobenius to the open
and closed pieces are data `Φ_U`, `Φ_Z`, and the restricted Weil complexes are
`WeilComplex.upperStarPull`, whose coefficient morphisms are the canonical
`WeilComplex.upperStarPullCoeff`.
-/

@[expose] public section

universe u' u

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
`WeilComplex`es (blueprint: `prop-trf-trace-additivity-open-closed`, subsection
`sk-i-global-additivity`). -/
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

namespace WeilComplex

section Restriction

variable {Y : Scheme.{u}} {aX : X ⟶ s} (W : WeilComplex (A := A) aX) (f : Y ⟶ X) {aY : Y ⟶ s}
  (hf : f ≫ aX = aY) (g : Y ⟶ Y) (sq : CommSq g f f (W.frobeniusIterate 1))

/-- The iterates of the Frobenius of a restricted Weil complex are the restrictions of the
iterates: `Φ_{Y,m} ≫ f = f ≫ Φ_{X,m}`. -/
lemma commSq_frobeniusIterate_upperStarPull (m : ℕ) :
    CommSq ((W.upperStarPull f hf g sq).frobeniusIterate m) f f (W.frobeniusIterate m) :=
  sorry

/-- The iterates of the coefficient morphism of a restricted Weil complex are the restrictions
of the iterates: `(f^* φ)_m = f^* φ_m`, read through the square `Φ_{Y,m} ≫ f = f ≫ Φ_{X,m}`. -/
lemma coeffIterate_upperStarPull (m : ℕ) :
    (W.upperStarPull f hf g sq).coeffIterate m =
      W.upperStarPullCoeff m (W.commSq_frobeniusIterate_upperStarPull f hf g sq m) :=
  sorry

/-- If a point `y` of `Y` is fixed by `Φ_{Y,m}`, then `f ∘ y` is fixed by `Φ_{X,m}`. -/
lemma comp_frobeniusIterate_of_upperStarPull (m : ℕ) {T : Scheme.{u}} (y : T ⟶ Y)
    (hy : y ≫ (W.upperStarPull f hf g sq).frobeniusIterate m = y) :
    (y ≫ f) ≫ W.frobeniusIterate m = y ≫ f :=
  sorry

/-- A point `y` of `Y` is fixed by `Φ_{Y,m}` if and only if `f ∘ y` is fixed by `Φ_{X,m}`,
when `f` is a monomorphism. -/
lemma comp_frobeniusIterate_upperStarPull_iff [Mono f] (m : ℕ) {T : Scheme.{u}} (y : T ⟶ Y) :
    y ≫ (W.upperStarPull f hf g sq).frobeniusIterate m = y ↔
      (y ≫ f) ≫ W.frobeniusIterate m = y ≫ f :=
  sorry

/-- The stalk Frobenius of the restricted Weil complex `Lf^* K` at a point `y` is the stalk
Frobenius of `K` at `f ∘ y`: they are conjugate along `Ly^* Lf^* K ≃ L(y ≫ f)^* K`, so they
have the same trace. -/
theorem trace_stalkFrobenius_upperStarPull (m : ℕ) (y : s ⟶ Y)
    (hy : y ≫ (W.upperStarPull f hf g sq).frobeniusIterate m = y)
    [HasRightDual (((upperStar A y).leftDerivedFunctor).obj
      (W.upperStarPull f hf g sq).obj)]
    [HasRightDual (((upperStar A (y ≫ f)).leftDerivedFunctor).obj W.obj)] :
    MonoidalCategory.trace ((W.upperStarPull f hf g sq).stalkFrobenius m y hy) =
      MonoidalCategory.trace (W.stalkFrobenius m (y ≫ f)
        (W.comp_frobeniusIterate_of_upperStarPull f hf g sq m y hy)) :=
  sorry

end Restriction

/-- The trace formula in degree `m` for a Weil complex `W` on `a_X : X ⟶ s`: for every choice
of duals of `RΓ_c(X, K)` and of the geometric stalks, and finiteness of the fixed points of
`Φ_m`,

`tr_A(F_{c,m}(φ) ∣ RΓ_c(X, K)) = ∑_{x ∈ Fix(Φ_m)} tr_A(φ_{m, x} ∣ K_x)`.

This is the identity `TF(X₀, K, φ, m)` of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`. -/
def TraceFormula (G : GeometricOperations A s) {aX : X ⟶ s} [IsGeometric aX]
    [HasCompactification aX] (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ)
    [IsProper (W.graph G hW m).snd] : Prop :=
  ∀ [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [∀ x : s ⟶ X, HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    [Fintype {x : s ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}],
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G hW m) hW) =
      ∑ x : {x : s ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x},
        MonoidalCategory.trace (W.stalkFrobenius m x.1 x.2.2)

/-- Step 5 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`, the
localization step: for a closed immersion `i : Z ⟶ X` with open complement `j : U ⟶ X`, both
stable under the Frobenius, the trace formula for `X` follows from the trace formulas for the
restricted Weil complexes `Lj^* K` on `U` and `Li^* K` on `Z`, by additivity of the trace
(`trace_globalOperator_eq_trace_add_trace`) and since the fixed points of `X` are the disjoint
union of those of `U` and `Z`. -/
theorem traceFormula_of_isCompl {Ω : Type u} [Field Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {U Z : Scheme.{u}} {aX : X ⟶ Spec (.of Ω)}
    {aU : U ⟶ Spec (.of Ω)} {aZ : Z ⟶ Spec (.of Ω)}
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
    [HasRightDual ((rightDerivedLowerShriek A aU).obj (W.upperStarPull j hj frobU sqU).obj)]
    [HasRightDual ((rightDerivedLowerShriek A aZ).obj (W.upperStarPull i hi frobZ sqZ).obj)]
    (hU : (W.upperStarPull j hj frobU sqU).TraceFormula G (G.ctf_upperStar j (.mk hj) hW) m)
    (hZ : (W.upperStarPull i hi frobZ sqZ).TraceFormula G (G.ctf_upperStar i (.mk hi) hW) m) :
    W.TraceFormula G hW m :=
  sorry

end WeilComplex

end AlgebraicGeometry.ProEtale
