/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.TwistedSiteSieveGeometry
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Module presheaves and sheaves on the internal action site

Source: the agent-formulated categorical foundation accompanying main-20261015,
sk-thm-sf-ctf-stability-direct-images, paragraph (3), returned steps 4--6;
Stacks Sites, Tags 00Z8, 00ZC, and Modules on Sites, Section 03CS for background
(blueprint: lem-sfb-twisted-module-presheaf-equivalence).

All categories, actions and coefficient objects are the existing constructions in
`InternalActionSitePresentation`, exposed by the sieve-geometry dependency. The theorem
characterizes both functors by equality of section modules and of their component functions.
`HEq` compares functions whose bundled source or target modules are propositionally equal
by the adjacent section equalities. It does not allow changing sections by an isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C] (K : Cᵒᵖ ⥤ GrpCat.{u})

end CategoryTheory.InternalActionSite
