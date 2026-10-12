module

public import Sheaf.AlgebraicGeometry.Ample
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.AmpleSeparated
import Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import Sheaf.Paper.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-! # Sections of ample powers in an ideal sheaf

Source: Stacks Project, Properties, Proposition 01Q3, equivalence of (1) and (6)
(blueprint: lem-sc-ample-ideal-section).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- If a point is outside a quasi-coherent ideal sheaf on a quasi-compact scheme, an
ample power has a global section coming from that ideal and nonvanishing at the point.
Source: Stacks Project, Properties, Proposition 01Q3, equivalence of (1) and (6)
(blueprint: lem-sc-ample-ideal-section).

Proof: choose an affine nonvanishing neighbourhood from ampleness, choose a section of the
ideal which is a unit at the point, clear its denominator using the section defining that
neighbourhood, and multiply once more by that section to ensure a positive tensor power.
The resulting section lies in the image of the ideal inclusion tensored with the power and
is nonvanishing at the chosen point.
-/
theorem exists_section_of_ample_ideal
    {Y : Scheme.{u}} [CompactSpace Y] (M : Y.Modules) [M.IsInvertible]
    (hM : Scheme.Modules.IsAmple Y M) (J : Y.IdealSheafData)
    {y : Y} (hy : y ∉ (J.support : Set Y)) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Γ(M.tensorPow n, ⊤),
      ∃ v : Γ(J.toModules.tensorObj (M.tensorPow n), ⊤),
        u = ((tensorHom J.toModulesι (𝟙 (M.tensorPow n)) ≫
          (MonoidalCategory.leftUnitor (M.tensorPow n)).hom).app ⊤) v ∧
      y ∈ Scheme.Modules.nonvanishingLocus (M.tensorPow n) u := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
