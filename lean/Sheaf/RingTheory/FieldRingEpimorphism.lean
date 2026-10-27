/-
Copyright (c) 2026 The Weil Conjectures Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil Conjectures Project
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Ring epimorphisms from a field

Source: Stacks Project, Tag 04VV, `lemma-epimorphism-over-field`
(blueprint: lem-sfb-field-ring-epimorphism-trivial-or-iso).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A ring epimorphism from a field has zero target or is bijective, hence a ring isomorphism.
Source: Stacks Project, Tag 04VV, `lemma-epimorphism-over-field`
(blueprint: lem-sfb-field-ring-epimorphism-trivial-or-iso).

The epimorphism condition is right cancellation against arbitrary commutative test rings.
The test universe contains both the field and target universes, so in particular it contains
all tensor products needed to detect epimorphy. No finiteness or reducedness is assumed.

Proof: If zero equals one in `A`, every element equals zero and the first alternative holds.
Otherwise give `A` the algebra structure induced by `φ`, with scalar action `φ(c) * a`.
By `lem-sfb-nonzero-field-algebra-faithfully-flat`, this nonzero vector space is faithfully
flat: it is free by `Module.Free.of_divisionRing`, so the nontrivial free module instance
`Module.FaithfullyFlat.instOfNontrivialOfFree` applies. The faithful flatness and the given
cancellation condition now satisfy `lem-sfb-faithfully-flat-ring-epimorphism-isomorphism`
(Stacks Tag 04VU), proving bijectivity. Its inverse preserves the ring operations and one,
as can be checked after applying the injective map `φ`; thus `φ` is a ring isomorphism. -/
theorem zero_eq_one_or_bijective_of_epi {k : Type u} [Field k] {A : Type v} [CommRing A]
    (φ : k →+* A)
    (hφ : ∀ (B : Type (max u v)) [CommRing B] (a b : A →+* B),
      a.comp φ = b.comp φ → a = b) :
    (0 : A) = 1 ∨ Function.Bijective φ := by
  sorry

end RingHom
