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
import WeilConjectures.AlgebraicGeometry.TruncatedHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Affine evaluation of coproducts of lower-truncated higher images

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The sheaf coproduct of lower-truncated higher images is a coproduct on affine sections.
This assertion concerns only the family of higher-image sheaves; no ambient derived
coproduct or its higher direct image occurs in its statement.
-/
theorem truncated_higherImages_affine_coproduct
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (a q : ℤ) (U : Y.Opens) (hU : IsAffineOpen U) :
    Nonempty (IsColimit
      ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).mapCocone
        (Cofan.mk
          (∐ (fun i ↦ (schemeHigherDirectImage f q).obj
            ((DerivedCategory.TStructure.t.truncGE a).obj (E i).obj)))
          (Sigma.ι (fun i ↦ (schemeHigherDirectImage f q).obj
            ((DerivedCategory.TStructure.t.truncGE a).obj (E i).obj)))))) := by
  let M : I → Y.Modules := fun i ↦ (schemeHigherDirectImage f q).obj
    ((DerivedCategory.TStructure.t.truncGE a).obj (E i).obj)
  have hM : ∀ i, (M i).IsQuasicoherent := fun i ↦
    truncated_higherImage_isQuasicoherent f (E i) a q
  let : ∀ i, (M i).IsQuasicoherent := hM
  have hsum : (∐ M).IsQuasicoherent := Scheme.Modules.isQuasicoherent_sigma M
  exact Scheme.Modules.quasiCoherentModuleColimitEvaluation Y (Discrete I)
    (Discrete.functor M) (Cofan.mk (∐ M) (Sigma.ι M))
    (coproductIsCoproduct M) (fun i ↦ hM i.as) hsum U hU

end AlgebraicGeometry
