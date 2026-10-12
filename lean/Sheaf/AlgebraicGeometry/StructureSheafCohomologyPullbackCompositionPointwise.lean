module

public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback

/-! Pointwise composition formula for structure-sheaf cohomology pullback.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-composition-pointwise)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pointwise form of the composition formula. The Ext construction of pullback
is functorial under composition of exact inverse-image functors; evaluating that
functoriality on a class gives the displayed equality. This is the pointwise
calculation underlying the additive-homomorphism composition law.
Source: Stacks Project, Cohomology of Sheaves, Section 01F7, equation-functorial.
(blueprint: lem-sc-structure-sheaf-cohomology-pullback-composition-pointwise)
-/
theorem structureSheafCohomologyPullback_comp_apply {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (x : Sheaf.H (structureSheafAb Z) n) :
    structureSheafCohomologyPullback (f ≫ g) n x =
      structureSheafCohomologyPullback f n
        (structureSheafCohomologyPullback g n x) := by
  sorry

end AlgebraicGeometry.Scheme
