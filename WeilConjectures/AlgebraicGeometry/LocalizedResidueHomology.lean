/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Derived residue homology on the localized module site

## References

* [Stacks, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Restrict the localized module site to the open subscheme, derive pullback to its
residue point, take degree-zero homology and global sections, and transport scalars
along `ΓSpecIso`. (Stacks, Tags 06YJ, 0098) -/
noncomputable def localizedResidueHomology (S : Scheme.{u}) (U : S.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (x : U.toScheme) :
    DerivedCategory (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ⥤
      ModuleCat.{u} (U.toScheme.residueField x) := by
  letI : HasDerivedCategory.{u + 1} U.toScheme.Modules :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)) :=
    HasDerivedCategory.standard _
  letI : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (Scheme.Modules.overEquiv U).functor.mapDerivedCategory.{w, u + 1} ⋙
    derivedPullback.{u, u + 1} (U.toScheme.fromSpecResidueField x) ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)) 0 ⋙
    SheafOfModules.evaluation
      (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace) (op ⊤) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (U.toScheme.residueField x)).inv.hom

end AlgebraicGeometry
