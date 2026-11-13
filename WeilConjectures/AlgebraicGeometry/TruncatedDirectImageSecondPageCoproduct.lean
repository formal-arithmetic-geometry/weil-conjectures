/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import WeilConjectures.AlgebraicGeometry.TruncatedDirectImageSecondPageCoproductMono
import WeilConjectures.AlgebraicGeometry.TruncatedDirectImageSecondPageCoproductEpi

/-! # The second-page coproduct comparison for lower-truncated direct image

## References

* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The second-page maps for a uniformly lower-truncated ambient coproduct are isomorphisms. -/
theorem truncated_directImage_secondPage_coproduct
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a : ℤ) (p : ℕ) (r : ℤ) :
    IsIso (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) := by
  have hm : Mono (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) :=
    truncated_directImage_secondPage_coproduct_mono f I E S ι hc a p r
  have he : Epi (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) :=
    truncated_directImage_secondPage_coproduct_epi f I E S ι hc a p r
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry
