/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparison
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Naturality of the localized comparison into derived pullback

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-stalk-comparison-pullback-naturality).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- The comparison with the cohomology of the canonical derived pullback.
Its construction uses the invertible pullback counit on the representative, the
specified tensor-stalk isomorphism, and the localization comparison; no target
complex or morphism to a target is involved.
(blueprint: lem-pc-stalk-comparison-pullback-naturality)
-/
def comparisonIntoPullback (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (i : ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  letI := hP
  (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
    HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
    (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv ≫
    (comparisonStalkCohomology X' z i).map
      (cast (by rfl)
        (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
        DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) ⟶
          (derivedPullback g').obj (DerivedCategory.Q.obj P))

end AlgebraicGeometry.SingleComplexBaseChange
