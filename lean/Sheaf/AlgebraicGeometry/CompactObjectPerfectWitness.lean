module
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
public import Sheaf.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DerivedQCohCompactRepresentatives
@[expose] public section
universe u wX wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option linter.unusedVariables false in
/-- A compact object admits the perfect-object witness in suitable local derived models.
Source: Stacks Project, Tag 09M1.
(blueprint: lem-sc-compact-object-perfect-witness). -/
theorem compactObject_perfect_witness
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasCoproducts.{u} (schemeDerivedQCohCategory X)]
    (P : schemeDerivedQCohCategory X) (hP : IsCompactObject P) :
    ∃ (hX : ∀ U : X.Opens, HasDerivedCategory.{wX}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
      (hY : ∀ U : Y.Opens, HasDerivedCategory.{wY}
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))),
      @Scheme.IsPerfect X _ hX P.1 := by
  obtain ⟨hX⟩ := noetherian_open_derived_categories_exists X
  obtain ⟨hY⟩ := noetherian_open_derived_categories_exists Y
  let := hX
  refine ⟨hX, hY, ?_⟩
  exact compact_isPerfect_of_isNoetherian X P hP
end AlgebraicGeometry
