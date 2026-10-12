/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.Galois.StacksGaloisAxioms
import Sheaf.CategoryTheory.Galois.StacksGaloisCategory

/-!
# Galois objects above connected objects

Source: Stacks Project, Fundamental Groups of Schemes, Lemma 0BN2
(blueprint: lem-galois-object-exists).
-/

@[expose] public section

universe w v u

open CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- (blueprint: lem-galois-object-exists) Stacks, Lemma 0BN2. In a Galois category,
every connected object receives a morphism from a Galois object.

For the proof, let `n` be the finite, nonzero cardinality of `F.obj X`. Decompose
the finite product `X^n` into connected components and choose one whose fibre
contains an enumeration of `F.obj X` with distinct entries. Every tuple in that
component has distinct entries: a repeated pair would make the component the
image of a connected component of `X^(n-1)` under a diagonal map. The resulting
map between connected objects is epi and surjective on fibres by
`stacksGaloisCategory_axioms`, contradicting the chosen enumeration. The
stabilizer of the component in the symmetric group then acts transitively on
its fibre. Its elements induce automorphisms of the component, so the
transitivity criterion of `stacksGaloisCategory_axioms` makes it a Galois
object. Compose the component inclusion with a product projection to obtain
its morphism to `X`. -/
theorem exists_stacksGaloisObject_hom_of_isConnected
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
    (hG : IsStacksGaloisCategory F) (X : C) [IsConnected X] :
    ∃ (Z : C) (_ : Z ⟶ X), IsStacksGaloisObject F Z := by
  sorry

end CategoryTheory
