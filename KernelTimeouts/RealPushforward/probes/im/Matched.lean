module
public import WeilConjectures.DeligneLaumon.AffineLine.RealPushforward

@[expose] public noncomputable section
namespace AlgebraicGeometry.WeilSheaf

example {l : ℕ} [Fact l.Prime] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (PadicAlgCl l)) :
    Matrix.charmatrix M = Matrix.charmatrix (fun i j => M i j) := by
  have h : Matrix.charmatrix (fun i j => M i j) = Matrix.charmatrix M := by rfl
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let h ← Lean.Meta.getFVarFromUserName `h
      let actual ← Lean.Meta.inferType h
      let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
      Lean.logInfo m!"matched pair syntactic={actual == expected}"
  exact h

end AlgebraicGeometry.WeilSheaf
