module
public import Sheaf.Paper.TowerClassCoefficients
public import Sheaf.Paper.TowerIntegralPullbackData
public import Sheaf.Paper.SemilinearOrdinaryInverseSystem
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
/-- Pointwise normalized comparison of constant integral sections.
Source: blueprint classes proof (2), integral reduction; the coefficient ring
comparison is constructed levelwise and checked on the integer generators.
(blueprint: lem-sp-tower-integral-unit-normalization-components). -/
theorem integralInverseSystem_unit_normalization_components (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      ((Rrings l Y).obj (Opposite.op n)) ((Rrings l X).obj (Opposite.op n)))
    (P : WeilConjectures.SemilinearSections.OrdinaryInverseSystem.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
      (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)
      (Scheme.ProEt.topology X) (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (fun n ↦ (Rrings l X).obj (Opposite.op n))
      (fun n ↦ (Rrings l X).map (homOfLE (Nat.le_succ n)).op) I)
    (FY : Forget Y (Rrings l Y)) (FX : Forget X (Rrings l X))
    (e : FY.F ⋙ abPull f ≅ P.pull ⋙ FX.F) :
    ∃ i : P.pull.obj (coefficient Y (Rrings l Y)) ≅ coefficient X (Rrings l X),
      ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
        (x : (((abPull f).obj (integers Y)).obj (op n)).obj.obj U),
        (((((abPull f).map (integerGenerator Y (Rrings l Y) FY)) ≫
          e.hom.app (coefficient Y (Rrings l Y))) ≫ FX.F.map i.hom).app (op n)).hom.app U x =
        ((integerPull f ≫ integerGenerator X (Rrings l X) FX).app (op n)).hom.app U x := by
  sorry
end AlgebraicGeometry.ProEtale.SpTowerClasses
