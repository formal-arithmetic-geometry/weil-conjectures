/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Functorial injective embeddings of modules on a scheme

Source: Stacks Project, Injectives, Lemma 01DI, and Cohomology, proof of Lemma 01FF
(blueprint: lem-weil-pbc-scheme-modules-functorial-injective-embeddings).
-/

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Sheaves of modules on a scheme admit functorial monomorphisms into injective objects.
For a directed system `F`, composition with the same functor `J` gives a system of injective
objects, and the components of `j` give compatible monomorphisms.
Source: Stacks Project, Injectives, Lemma 01DI; Cohomology, proof of Lemma 01FF
(blueprint: lem-weil-pbc-scheme-modules-functorial-injective-embeddings).

Proof:
1. At each point `x`, apply `lem-weil-pbc-grothendieck-functorial-injective-embedding`
   to the module category of the stalk ring, which is abelian with enough injectives
   (`lem-weil-pbc-ring-modules-enough-injectives`) and Grothendieck abelian
   (`lem-weil-pbc-ring-modules-grothendieck-abelian`). Stalks and their maps are those of
   `def-weil-pbc-module-stalk`. Obtain functorial embeddings into injective stalk modules.
2. The stalk functor is additive and exact (`lem-weil-pbc-module-stalk-exact`). Its right
   adjoint is the skyscraper functor (`lem-weil-pbc-module-skyscraper-stalk-adjunction`),
   so skyscrapers of injective modules are injective
   (`lem-sp-right-adjoint-preserves-injectives`).
3. Form the product over all points of these skyscrapers. Products are computed on sections
   (`lem-weil-pbc-module-sheaves-limits-sectionwise`), giving sections over `U` equal to
   the product of the injective stalk modules over `x ∈ U`. This product is injective
   (`lem-weil-pbc-product-injectives`).
4. Define `J` on morphisms by the maps of stalk modules followed by their injective-embedding
   functors. The product universal property and functoriality of stalks and skyscrapers give
   preservation of identities and composition.
5. Send a section to the family of its germs followed by the stalk embeddings. A section
   in the kernel has every germ zero, hence is zero
   (`lem-weil-pbc-sheaf-sections-determined-by-germs`); the resulting map is monic.
6. Naturality of the stalk embeddings, checked in every product coordinate, gives naturality
   of these maps, hence `j : id ⟶ J`.
7. Postcompose a directed system with `J`. Its identities and composition laws follow from
   those of the two functors. Its values are injective by step 3, the components of `j` are
   monic by step 5, and their compatibility with transition maps is step 6. -/
theorem exists_functorialInjectiveEmbeddings (X : Scheme.{u}) :
    ∃ (J : X.Modules ⥤ X.Modules) (j : 𝟭 X.Modules ⟶ J),
      (∀ M : X.Modules, Mono (j.app M)) ∧
      (∀ M : X.Modules, Injective (J.obj M)) ∧
      (∀ (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)] (F : I ⥤ X.Modules),
        (∀ i : I, Injective ((F ⋙ J).obj i)) ∧
        (∀ i : I, Mono (j.app (F.obj i))) ∧
        ∀ (i i' : I) (h : i ≤ i'),
          j.app (F.obj i) ≫ (F ⋙ J).map (homOfLE h) =
            F.map (homOfLE h) ≫ j.app (F.obj i')) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
