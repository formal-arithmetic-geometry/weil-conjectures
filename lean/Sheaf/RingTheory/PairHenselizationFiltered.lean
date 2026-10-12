/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Filtered.Basic


@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Filteredness of the category of etale algebras trivial modulo the ideal.
Source: Stacks Project, Tag 0A02, directedness paragraph.
(blueprint: lem-weil-pbc-pair-henselization-filtered).

Proof: Write R = B/J. The identity B-algebra is an object, so the category is nonempty.
For two objects C and D use C tensor_B D. Base change and composition preserve etaleness,
and its reduction is (C/JC) tensor_R (D/JD), canonically R. The two factor maps give
common successors. Every map between etale B-algebras is etale by cancellation.
For parallel maps f,g : C to D put E = D tensor_(f,C,g) D and
T = E tensor_(D tensor_B D) D, using multiplication for the last map to D.
The right factor D to E is a base change of f. The multiplication D tensor_B D to D
is etale by cancellation, so its base change E to T is etale as well. Thus T is etale
over B. Reduction of this entire diagram modulo J replaces each algebra by R and each
map by its identity, whence T/JT is R with the required structure map.
The map D to T identifies the images of d tensor 1 and 1 tensor d, since both become d
under multiplication. In E, f(c) tensor 1 equals 1 tensor g(c), so this map coequalizes
f and g. These three constructions establish all the filteredness axioms. -/
theorem pair_henselization_filtered (B : Type u) [CommRing B] (J : Ideal B) :
    IsFiltered (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))) := by
  sorry

end RingTheory
