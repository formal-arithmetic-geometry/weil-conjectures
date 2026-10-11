/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Injective module sheaves are acyclic after forgetting to abelian sheaves

Source: literature/stacks-project/sites-cohomology.tex, Lemma Tag 03FD
(lemma-cohomology-modules-abelian-agree), proof, second paragraph (via Lemmas 03FC and 03F9)
(blueprint: lem-sc-injective-module-abelian-acyclic-zariski).

The proof uses `lem-weil-pbc-ringed-site-injective-module-cech-acyclic` for vanishing of
Čech cohomology for every covering, and `lem-weil-pbc-site-cech-vanishing-criterion` to
pass from Čech vanishing to derived cohomology.
-/

universe u v w'

open CategoryTheory

namespace CategoryTheory

/-- The underlying abelian sheaf of an injective sheaf of modules has no positive
cohomology over any object of the site.
Source: Stacks Project, `sites-cohomology.tex`, Tag 03FD
(`lemma-cohomology-modules-abelian-agree`), proof, second paragraph, via Tags 03FC and 03F9.
(blueprint: lem-sc-injective-module-abelian-acyclic-zariski)

Proof: for every covering of every object, apply
`lem-weil-pbc-ringed-site-injective-module-cech-acyclic` (Tag 03FC) to obtain vanishing
of the positive Čech cohomology of the underlying abelian sheaf. Apply
`lem-weil-pbc-site-cech-vanishing-criterion` (Tag 03F9) with the collection of objects
equal to all objects and the collection of coverings equal to all coverings.
Its first assumption holds because every covering object and iterated fibre product
is an object of the site. Its second holds because every covering refines itself.
Its third is the Čech vanishing just obtained. The criterion therefore gives
vanishing of derived cohomology over every object in every positive degree. -/
theorem injective_module_abelian_acyclic
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}} [HasSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (U : C) (I : SheafOfModules.{v} R) [Injective I] :
    ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H' ((SheafOfModules.toSheaf R).obj I) q U) := by
  sorry

end CategoryTheory
