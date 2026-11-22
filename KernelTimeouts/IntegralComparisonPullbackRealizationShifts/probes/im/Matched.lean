module
public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonCanonicalShifts
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates

set_option autoImplicit false
@[expose] public noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

example (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E X)
    (M : IntegralComparisonPullbackModel l E f SY ρ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    M.realization.hom.app (DerivedCategory.Q.obj P) ≫ 𝟙 _ =
    M.realization.hom.app (DerivedCategory.Q.obj ((fun Z => Z) P)) ≫ 𝟙 _ := by
  have h : M.realization.hom.app (DerivedCategory.Q.obj ((fun Z => Z) P)) ≫ 𝟙 _ =
      M.realization.hom.app (DerivedCategory.Q.obj P) ≫ 𝟙 _ := by rfl
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let h ← Lean.Meta.getFVarFromUserName `h
      let actual ← Lean.Meta.inferType h
      let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
      Lean.logInfo m!"matched pair syntactic={actual == expected}"
  exact h

end WeilConjectures
