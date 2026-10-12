module

public import Sheaf.AlgebraicGeometry.CoherentIntegralFiltration

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Pushforward identifies the successor finite sum with the old sum and one
additional summand.
Source: Stacks Project, Tag 01YF, finite-sum comparison in the successor step.
(blueprint: new-pushforward-fin-sum-succ-iso)
-/
theorem pushforward_fin_sum_succ_iso
    {X Z : Scheme.{u}} (i : Z ⟶ X) (r : ℕ) (I : Z.IdealSheafData) :
    Nonempty ((pushforward i).obj (∐ fun _ : Fin (r + 1) => I.toModules) ≅
      (pushforward i).obj (∐ fun _ : Fin r => I.toModules) ⊞
        (pushforward i).obj I.toModules) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
