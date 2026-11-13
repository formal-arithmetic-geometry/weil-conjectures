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

import WeilConjectures.AlgebraicGeometry.TruncatedDirectImageSecondPageCoproduct
import WeilConjectures.CategoryTheory.BoundedBelowCoproductFiltration

/-! # Local surjectivity of the lower-truncated coproduct comparison

## References

* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The truncated direct-image coproduct comparison is an epimorphism.
-/
theorem truncated_directImage_sheaf_coproduct_epi
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a q : ℤ) :
    Epi (Sigma.desc (fun i ↦ (schemeHigherDirectImage f q).map
      ((DerivedCategory.TStructure.t.truncGE a).map (ι i)))) := by
  let A := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  have : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (Scheme.Modules.pushforward f)
    infer_instance
  let K : I → DerivedCategory A := fun i ↦
    (DerivedCategory.TStructure.t.truncGE a).obj (E i).obj
  let T : DerivedCategory A := (DerivedCategory.TStructure.t.truncGE a).obj S
  let u : ∀ i, K i ⟶ T := fun i ↦
    (DerivedCategory.TStructure.t.truncGE a).map (ι i)
  have hK (i : I) (r : ℤ) (hr : r < a) :
      IsZero ((DerivedCategory.homologyFunctor A r).obj (K i)) :=
    DerivedCategory.isZero_of_isGE (K i) a r hr
  have hT (r : ℤ) (hr : r < a) :
      IsZero ((DerivedCategory.homologyFunctor A r).obj T) :=
    DerivedCategory.isZero_of_isGE T a r hr
  have hE2 (p : ℕ) (r : ℤ) : IsIso (Sigma.desc (fun i ↦
      (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor B (p : ℤ)).map
          ((DerivedCategory.homologyFunctor A r).map (u i)))) :=
    truncated_directImage_secondPage_coproduct f I E S ι hc a p r
  obtain ⟨FS, FT, phi, hFS, hFT, hphi, hgraded⟩ :=
    exists_boundedBelow_coproduct_filtration F I K T u a q hK hT hE2
  have hiso := (WeilFilteredObject.finite_filtration_induction_steps
    ⟨_, FS⟩ ⟨_, FT⟩ phi hFS hFT hgraded).1
  rw [hphi] at hiso
  have : IsIso (Sigma.desc (fun i ↦ (schemeHigherDirectImage f q).map
      ((DerivedCategory.TStructure.t.truncGE a).map (ι i)))) := hiso
  infer_instance

end AlgebraicGeometry
