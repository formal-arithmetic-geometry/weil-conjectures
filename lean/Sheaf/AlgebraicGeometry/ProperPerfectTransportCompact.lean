module
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
public import Sheaf.AlgebraicGeometry.PerfectObjectCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Tor
@[expose] public section
universe u wX wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Proper perfect direct image of a perfect object is compact after comparison with the
quasi-coherent model. Source: Stacks Project, Tags 09M1, 0B6G, and 0A9R.
(blueprint: lem-sc-proper-perfect-transport-compact). -/
theorem properPerfect_transport_compact
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (f : X ⟶ Y) [IsProper f]
    (hTor : ∀ x : X, ∃ n : ℕ,
      ∀ (N : ModuleCat.{u} (Y.presheaf.stalk (f x))) (i : ℕ), n < i →
        IsZero (((Tor (ModuleCat.{u} (Y.presheaf.stalk (f x))) i).obj
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))).obj N))
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (eR : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (P : schemeDerivedQCohCategory X) (hP : Scheme.IsPerfect X P.1) :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
    IsCompactObject (R.obj P) := by sorry
end AlgebraicGeometry
