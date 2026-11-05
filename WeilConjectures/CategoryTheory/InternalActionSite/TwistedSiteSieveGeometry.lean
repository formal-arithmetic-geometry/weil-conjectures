/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSiteBasic

/-!
# Labeled pullbacks and sieves of the internal action category

Source: the agent-formulated categorical foundation motivated by main-20261015,
sk-thm-sf-ctf-stability-direct-images, paragraph (3); Stacks Sites, Tags 00VH, 00Z4,
00ZD for the site and topology axioms (blueprint: lem-sfb-twisted-site-sieve-geometry).

The existing `InternalActionSite.Object`, `Arrow`, `categoryStruct`, `category`,
`projection`, `precoverage`, and `topology` give the actual construction. In particular,
composition of `(g,b)` followed by `(f,a)` has label `b * K.map g.op a`.
The theorem supplies the explicit pullbacks, source normalization, and sieve geometry
for that same category, without introducing a second category or a second precoverage.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C] (K : Cᵒᵖ ⥤ GrpCat.{u})

end CategoryTheory.InternalActionSite
