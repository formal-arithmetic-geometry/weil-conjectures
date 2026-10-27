/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Faithfully flat ring epimorphisms

Source: Stacks Project, Tag 04VU, `lemma-faithfully-flat-epimorphism`
(blueprint: lem-sfb-faithfully-flat-ring-epimorphism-isomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A faithfully flat epimorphism of commutative rings is bijective and is the underlying
homomorphism of a ring equivalence. The map is encoded by the `R`-algebra structure on `S`.
There is no finite-generation or finite-presentation hypothesis.

Source: Stacks Project, Tag 04VU, `lemma-faithfully-flat-epimorphism`
(blueprint: lem-sfb-faithfully-flat-ring-epimorphism-isomorphism).

Proof plan:
1. Set T = S tensor_R S. The tensor pushout universal property
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) gives the two inclusions
   i1(s) = s tensor 1 and i2(s) = 1 tensor s, whose composites with R to S agree.
   Apply hepi with B = T to conclude i1 = i2.
2. The same universal property gives multiplication mu : T to S with mu i1 = id.
   On pure tensors, i1 mu(s tensor t) = st tensor 1 = (s tensor 1)(1 tensor t)
   = s tensor t, using i1 = i2. Pure tensors generate
   (def-weil-pbc-module-tensor-product), so i1 mu = id as well.
3. The unit identification S tensor_R R to S sends s tensor r to s f(r), with
   inverse s to s tensor 1. Under this identification S tensor_R f is i1, hence
   bijective by step 2. Tensoring the complexes 0 to R to S and R to S to 0 with
   S therefore makes them exact. Faithful flatness reflects exactness
   (def-weil-pbc-faithfully-flat-ring-map), giving injectivity and surjectivity of f.
   Its inverse preserves addition, multiplication and one by applying the injective
   map f to each equality, giving the asserted ring equivalence. -/
theorem bijective_algebraMap_of_faithfullyFlat_of_epi
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    (hepi : ∀ (B : Type (max u v)) [CommRing B] (a b : S →+* B),
      a.comp (algebraMap R S) = b.comp (algebraMap R S) → a = b) :
    Function.Bijective (algebraMap R S) ∧
      ∃ e : R ≃+* S, e.toRingHom = algebraMap R S := sorry

end Algebra
