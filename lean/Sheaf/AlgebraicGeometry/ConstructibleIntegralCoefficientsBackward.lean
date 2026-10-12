module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import Sheaf.AlgebraicGeometry.EtalePullbackForgetModules
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.Paper.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Backward direction of `isConstructibleSheaf_integral_iff`.
The proof refines finite set-valued trivializations so that the finite group
operation tables are constant; these are then integral-module trivializations.
Source: Stacks Project Tags 03RW and 095E; blueprint q1-constructible-integral-coefficients.
(blueprint: q1-constructible-integral-coefficients-backward) -/
theorem isConstructibleSheaf_integral_backward {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : X.IsTorsionAbelianSheaf F) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    IsConstructibleEtaleSheafOfSets
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) →
      IsConstructibleSheaf ((sheafCompose X.smallEtaleTopology E).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
