/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.PinnedTensorSquareLeftSummand
import WeilConjectures.AlgebraicGeometry.PinnedTensorSquareCompatibility

/-! # Stalk compatibility of a specified tensor pullback chain map

## References

* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 0BYJ](https://stacks.math.columbia.edu/tag/0BYJ)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 079R](https://stacks.math.columbia.edu/tag/079R)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry

local instance tensorPullbackStalkSquareInstance1 (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  pullbackDescentModuleTensor Y

local instance tensorPullbackStalkSquareInstance2 (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  modulePreadditive Y

attribute [local instance] pinnedTensorSquareLeftSummandInstance3
  pinnedTensorSquareLeftSummandInstance4

-- Elaborating the scalar-extension and stalk tensor constructions needs more heartbeats.
/-- Stalk compatibility of a specified tensor pullback chain map. -/
theorem exists_tensor_pullback_stalk_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ)
    (a : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q ⟶ N)
    (χ : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P Q) ≅
      pullbackTensorTotal X'
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q))
    (hχ : ∀ (p q n : ℤ) (h : p + q = n),
      (Scheme.Modules.tensorPullback g').map
          (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n h) ≫
        χ.hom.f n =
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g')) (P.X p) (Q.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q)
          (curriedTensor _) (.up ℤ) p q n h) (z : X') :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
    let R := SingleComplexBaseChange.R f g' z
    let A := SingleComplexBaseChange.A g' z
    let B := SingleComplexBaseChange.B f' z
    let C := SingleComplexBaseChange.C z
    let F := (ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))).mapHomologicalComplex (.up ℤ)
    let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)
    let U := SingleComplexBaseChange.stalkComplex g' z P
    let V := SingleComplexBaseChange.stalkComplex g' z Q
    let t := (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z Q).hom ≫ S.map a
    ∃ (σ : U ⊗ V ≅ SingleComplexBaseChange.stalkComplex g' z
        (pullbackTensorTotal X P Q))
      (ρ : F.obj U ⊗ S.obj N ≅ S.obj
        (pullbackTensorTotal X'
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) N)),
      F.map σ.hom ≫
          (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z
            (pullbackTensorTotal X P Q)).hom ≫
          S.map (χ.hom ≫ HomologicalComplex.mapBifunctorMap (𝟙 _) a (curriedTensor _) (.up ℤ)) =
        (Functor.Monoidal.μIso F U V).inv ≫ (F.obj U ◁ t) ≫ ρ.hom := by
  let := SingleComplexBaseChange.leftAlgebra f g' z
  let := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
  let := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' z))
  exact ⟨_, _, pinned_tensor_pullback_stalk_compatibility f f' g g' sq P Q N a χ hχ z⟩

end AlgebraicGeometry
