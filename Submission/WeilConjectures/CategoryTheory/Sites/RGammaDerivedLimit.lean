/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Derived sections over a site object and derived inverse limits

Source: Stacks Project, Cohomology on Sites, Lemma 0D6K, first assertion;
Injectives, Lemma 08U1 (auxiliary; not a blueprint node).

The helper declarations supply the K-injective structure from the recorded existence
node and define the section functor and its unbounded right derived functor.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Transport abelian sheafification from the small model of the site. This is
Mathlib's existing sheafification transport, with the coefficient universe specified.
Source: Stacks Project, Sites, Section 00ZG; Mathlib, Sites/Equivalence,
transport from an equivalent small site
(auxiliary; not a blueprint node). -/
noncomputable instance siteAbelianHasSheafify
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{r} C] : HasSheafify J AddCommGrpCat.{r} :=
  hasSheafifyEssentiallySmallSite.{v, r, c, r + 1, r} J AddCommGrpCat.{r}

/-- Transport the characterization of sheafification equivalences by locally
bijective maps from the same small model. No extra site hypothesis is imposed.
Source: Stacks Project, Sites, Section 00ZG; Mathlib, Sites/Equivalence,
transport from an equivalent small site
(auxiliary; not a blueprint node). -/
noncomputable instance siteAbelianWEqualsLocallyBijective
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{r} C] : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, r, c, r + 1, r, r, r} J

end CategoryTheory
