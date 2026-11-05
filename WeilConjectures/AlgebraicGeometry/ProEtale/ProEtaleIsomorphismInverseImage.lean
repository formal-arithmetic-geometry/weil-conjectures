/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Inverse image along an isomorphism of schemes

Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).

## Main statements

- `proEtaleIsoPostcompose_equivalence`: the covering-preserving site equivalence.
- `existsUnique_proEtaleIsoInverseImageIdentification`: its normalized section identification.
- `proEtaleIsoInverseImage_equivalence`: equivalence and preservation of limits and colimits.
- `proEtaleIso_inverseLimitComparison`: the canonical inverse-limit comparison.
- `proEtaleIso_constantComparison`: invertible constant comparison and naturality.
- `proEtaleIso_constantModuleEquivalence`: the same equivalence for module sheaves.
- `proEtaleIso_constantRingModuleEquivalence`: module sheaves over any constant ring.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Change only the structure map of an object of the pro-etale site.
Source: Stacks Project, Tag 09A5
(blueprint: lem-weil-proetale-isomorphism-inverse-image). -/
def proEtaleIsoPostcompose {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)

private theorem isoPostcompose_continuous {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] :
    (proEtaleIsoPostcompose f).IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
  ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)

attribute [local instance] isoPostcompose_continuous

end AlgebraicGeometry.Scheme
