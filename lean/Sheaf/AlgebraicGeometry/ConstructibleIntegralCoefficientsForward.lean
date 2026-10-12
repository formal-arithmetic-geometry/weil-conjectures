module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Forward direction of `isConstructibleSheaf_integral_iff`.
The proof follows the constructible stratification comparison: a finitely generated
integral stalk is torsion by the torsion filtration, hence finite, and forgetting
module structure preserves local constancy and inverse-image stalks.
Source: Stacks Project Tags 03RW and 095E; blueprint q1-constructible-integral-coefficients.
(blueprint: q1-constructible-integral-coefficients-forward) -/
theorem isConstructibleSheaf_integral_forward {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : X.IsTorsionAbelianSheaf F) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    IsConstructibleSheaf ((sheafCompose X.smallEtaleTopology E).obj F) →
      IsConstructibleEtaleSheafOfSets
        ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
