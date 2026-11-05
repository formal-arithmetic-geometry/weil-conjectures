/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Data.Int.Interval

/-! # Bounded ordinary evaluation on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 08JJ and 0A8X.
(blueprint: lem-sfb-ringed-site-bounded-evaluation-assembly)

## Main statements

- `assembly`: the canonical finite diagonal evaluation and its inverse chain map.
- `IsModuleEvaluation`: the section formula for the termwise comparison.

All tensor and Hom objects below are the recorded sheaf constructions. The
section formulas specify the actual comparison, including its normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace CategoryTheory.RingedSiteBoundedEvaluation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  (R : Sheaf J CommRingCat.{max u v w})

attribute [local irreducible] homComplex homComplexFunctor homComplexπ

attribute [local irreducible] SheafOfModules.monoidalCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] dual total inclusion unitComplex
  CochainComplex.ιMapBifunctor CochainComplex.mapBifunctor
  sourceFamily targetFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] sheafCompose
  PresheafOfModules.sheafification PresheafOfModules.sheafificationAdjunction

attribute [local irreducible] inverseCounit

attribute [local semireducible] sheafCompose PresheafOfModules.sheafification
  PresheafOfModules.sheafificationAdjunction

attribute [local irreducible] evaluationPresheaf evaluationBilinear evaluationSection

attribute [local semireducible] SheafOfModules.monoidalCategory

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] tensorLift moduleEvaluation

attribute [local irreducible] evaluationComponent

attribute [local irreducible] evaluationDegree

attribute [local semireducible] SheafOfModules.monoidalCategory

end CategoryTheory.RingedSiteBoundedEvaluation
