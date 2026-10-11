/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.Galois.StacksGaloisCategory

/-!
# Transitivity of the automorphism action

Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN3
(blueprint: lem-galois-transitive).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- The automorphism group of a fiber functor acts transitively on the fiber of a
connected object (Stacks Project, Lemma 0BN3).

(blueprint: lem-galois-transitive)

The proof constructs a cofiltered system of Galois objects and identifies its
automorphism inverse limit with `Aut F`; the resulting action is transitive on
each connected fiber and hence on the given fiber.

Proof steps (Stacks Project, Lemma 0BN3):
1. Index representatives of Galois objects by a directed system, normalizing
   transition maps using the chosen fiber points and the Galois axioms
   (`def-galois-category`, `lem-galois-axioms`, `lem-galois-object-exists`).
2. Identify `F` with the colimit of the representables of these objects, using
   the same axioms for injectivity and surjectivity.
3. Form the inverse system of finite automorphism groups. Its surjective
   transition maps give a transitive action of the inverse limit, hence of
   `Aut F`, on every Galois-object fiber (`lem-galois-inverse-limit-surjective`).
4. Cover the connected object by a Galois object and descend transitivity
   along the fiber-surjective cover, using naturality of the automorphism.
-/
theorem aut_fiber_transitive {C : Type u} [Category.{v} C]
    {F : C ⥤ Type w} (hCF : IsStacksGaloisCategory F) (X : C)
    [IsConnected X] : ∀ x y : F.obj X, ∃ g : Aut F, g.hom.app X x = y := by
  sorry

end CategoryTheory
