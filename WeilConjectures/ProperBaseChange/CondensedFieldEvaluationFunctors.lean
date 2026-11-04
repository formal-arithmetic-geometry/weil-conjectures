/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Evaluation of condensed-field modules over one geometric point

Source: Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Example 4.2.11.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable def pointConstants
    (E : Type u) [NormedField E] (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    ULift.{u + 1} E ≃+* ULift.{u + 1} C(Spec (.of Ω), E) where
  toFun x := ULift.up (ContinuousMap.const _ x.down)
  invFun f := ULift.up (f.down z)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext y
    exact congrArg f.down (Subsingleton.elim z y)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end AlgebraicGeometry.ProEtale
