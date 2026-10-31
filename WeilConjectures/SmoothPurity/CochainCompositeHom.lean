/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.SmoothPurity.CochainTensoratorExistence
import all WeilConjectures.SmoothPurity.CochainInverseComparison
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.ProperBaseChange.GeometricModuleConstruction
import all WeilConjectures.ProperBaseChange.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
/-! # Normalized scalar-extension comparison for a composite

Source: Stacks Project, Modules on Sites, Tags 03EL and 0D6D.
(blueprint: lem-pur-independent-normalized-scalar-composition).

The comparison is recovered from the two explicit Hom adjunctions. Its value on
scalar-insertion generators determines it and gives its naturality.
-/

@[expose] public section
universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings TensorProduct
namespace CategoryTheory.CochainCompositeHom
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
/-- Module sheaves, using Mathlib's category verbatim.
Source: Stacks 03DA (blueprint: def-pur-cochain-tensor-coherence-data). -/
private abbrev Modules {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
set_option backward.isDefEq.respectTransparency false
open SheafOfModules SheafOfModules.GeometricConstruction

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency true in
variable {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {H : GrothendieckTopology E}
  [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {T : Sheaf H CommRingCat.{w}}

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 40000 in
-- Keep generic functor elaboration from unfolding the module constructions.
set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 40000 in
-- Keep generic functor elaboration from unfolding the module constructions.
set_option backward.isDefEq.respectTransparency true in
end CategoryTheory.CochainCompositeHom
