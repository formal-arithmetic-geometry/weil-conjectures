/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData

/-! # Evaluation operations for normalized etale systems

Source: Zheng, Construction 4.1; Stacks Tag 0GL6
(blueprint: lem-pur-etale-system-projection-evaluation-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

private theorem constantModule_exact (W : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (constantModule W A).Additive ∧ PreservesFiniteLimits (constantModule W A) ∧
      PreservesFiniteColimits (constantModule W A) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    intro X Y f g
    ext U x
    rfl
  · let T := sheafCompose W.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    have hT : PreservesFiniteLimits (constantModule W A ⋙ T) := by
      change PreservesFiniteLimits (SheafOfModules.toSheaf _)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ T
  · let T := sheafCompose W.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    have hT : PreservesFiniteColimits (constantModule W A ⋙ T) := by
      change PreservesFiniteColimits (SheafOfModules.toSheaf _)
      infer_instance
    exact preservesFiniteColimits_of_reflects_of_preserves _ T

/-- The exact evaluation functors exist at every coefficient level on all three schemes.
Source: Zheng Construction 4.1; Stacks 03D2, 03S2, 07A4
(blueprint: lem-pur-etale-system-projection-evaluation-existence).

Proof: Evaluate strict module systems at a fixed vertical level, where exactness is
computed componentwise. Compose with restriction from the constant ring sheaf to the
constant module sheaf; finite limits and colimits are preserved by the sectionwise
constant-sheaf construction and its sheafification. Package the resulting additive,
finite-limit-preserving, and finite-colimit-preserving instances for X, Z, and Y.
-/
theorem etaleSystemProjectionEvaluationData_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) :
    Nonempty
      ((∀ B : Coefficients.{u} l, ∀ n : ℕ, Evaluation X B.rings n) ∧
        (∀ B : Coefficients.{u} l, ∀ n : ℕ, Evaluation c.Z B.rings n) ∧
          (∀ B : Coefficients.{u} l, ∀ n : ℕ, Evaluation Y B.rings n)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B n
    let := WeilConjectures.SemilinearSections.evaluationAdditive
      X.smallEtaleTopology (coefficients X B.rings) (transitions X B.rings) n
    let := WeilConjectures.SemilinearSections.evaluationLimits
      X.smallEtaleTopology (coefficients X B.rings) (transitions X B.rings) n
    let := WeilConjectures.SemilinearSections.evaluationColimits
      X.smallEtaleTopology (coefficients X B.rings) (transitions X B.rings) n
    obtain ⟨hA, hL, hC⟩ := constantModule_exact X (B.rings.obj (op n))
    let := hA
    let := hL
    let := hC
    refine { additive := ?_, limits := ?_, colimits := ?_ } <;>
      dsimp only [level] <;> infer_instance
  · intro B n
    let := WeilConjectures.SemilinearSections.evaluationAdditive
      c.Z.smallEtaleTopology (coefficients c.Z B.rings) (transitions c.Z B.rings) n
    let := WeilConjectures.SemilinearSections.evaluationLimits
      c.Z.smallEtaleTopology (coefficients c.Z B.rings) (transitions c.Z B.rings) n
    let := WeilConjectures.SemilinearSections.evaluationColimits
      c.Z.smallEtaleTopology (coefficients c.Z B.rings) (transitions c.Z B.rings) n
    obtain ⟨hA, hL, hC⟩ := constantModule_exact c.Z (B.rings.obj (op n))
    let := hA
    let := hL
    let := hC
    refine { additive := ?_, limits := ?_, colimits := ?_ } <;>
      dsimp only [level] <;> infer_instance
  · intro B n
    let := WeilConjectures.SemilinearSections.evaluationAdditive
      Y.smallEtaleTopology (coefficients Y B.rings) (transitions Y B.rings) n
    let := WeilConjectures.SemilinearSections.evaluationLimits
      Y.smallEtaleTopology (coefficients Y B.rings) (transitions Y B.rings) n
    let := WeilConjectures.SemilinearSections.evaluationColimits
      Y.smallEtaleTopology (coefficients Y B.rings) (transitions Y B.rings) n
    obtain ⟨hA, hL, hC⟩ := constantModule_exact Y (B.rings.obj (op n))
    let := hA
    let := hL
    let := hC
    refine { additive := ?_, limits := ?_, colimits := ?_ } <;>
      dsimp only [level] <;> infer_instance

end AlgebraicGeometry.Etale.SystemProjection
