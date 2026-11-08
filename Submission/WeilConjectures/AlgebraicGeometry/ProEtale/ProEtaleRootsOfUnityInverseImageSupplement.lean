/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleStructureSheaf
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Inverse-image comparison for pro-etale roots of unity

Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-inverse-image).

## Main definitions

- `proEtaleRootsOfUnityDirectImageMap`: pullback of roots along the projection.
- `proEtaleRootsOfUnityInverseImageMap`: its inverse-image adjunct.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The comparison `c` is the adjoint of `β`, using the recorded inverse-image adjunction.
Source: Stacks Project, Tag 03PK (blueprint: def-pur-roots-of-unity-inverse-image). -/
noncomputable def proEtaleRootsOfUnityInverseImageMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) :
    (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N) ⟶ proEtaleRootsOfUnitySheaf X N :=
  ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (proEtaleRootsOfUnityDirectImageMap f N)

end AlgebraicGeometry.Scheme
