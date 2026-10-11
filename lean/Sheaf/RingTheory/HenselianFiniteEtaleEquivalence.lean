/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Finite

/-!
# Finite étale algebras over a henselian local ring

Source: Stacks Project, Algebra, Lemma 10.153.7, Tag 04GK
(blueprint: lem-weil-pbc-henselian-finite-etale-equivalence).

Mathlib's finite étale algebra category has algebra homomorphisms as its morphisms.
Its base-change functor sends `S` to `κ ⊗[R] S`, canonically isomorphic to `S / 𝔪S`.
-/

universe u v

open CategoryTheory

namespace CommAlgCat.FiniteEtale

/-- Reduction to the residue field of a henselian local ring is an equivalence, and every
finite étale residue-field algebra is the reduction of a finite étale algebra over the ring.
Source: Stacks Project, Algebra, Lemma 10.153.7, Tag 04GK
(blueprint: lem-weil-pbc-henselian-finite-etale-equivalence).

Proof (following the nine steps of the DAG node).
1. Quotient base change preserves étaleness (`lem-weil-pbc-etale-quotient-base-change`);
module generators descend, and reduction commutes with finite products.
2. Henselian étale retraction and the finite-product-local decomposition split each finite
étale algebra into local factors. Localization preserves étaleness; finiteness identifies
contractions of maximal ideals. The étale prime-generation and residue-separability lemmas
show that each factor reduces to its finite separable residue field.
3. Over a field, finite étale algebras split into finite separable fields
(`lem-weil-pbc-etale-algebra-over-field-product`). Orthogonal idempotents show that maps
from a finite product to a nonzero local ring select precisely one factor. Thus full
faithfulness reduces to two local factors.
4. Their tensor product is finite étale by étale base change and composition. Split it
into local factors; its reduction is the tensor product of the two residue fields.
5. An algebra map between the local factors gives a surjective map out of this tensor
product, selecting one factor. Its retraction kernel is a finite module with zero reduction,
so Nakayama (`lem-weil-pbc-nakayama-jacobson`) kills the kernel. Conversely an invertible
structure map from the second algebra to a tensor-product factor determines an algebra map.
These constructions are mutually inverse.
6. Over the residue field the same factor selection describes algebra maps, and reduction
preserves the selected index.
7. A structure map is invertible exactly when its reduction is: Nakayama gives surjectivity;
étale flatness and finite-flat-local freeness split the map, and Nakayama kills its kernel.
Hence the index sets agree, proving full faithfulness.
8. Lift a finite separable residue extension by the prescribed-residue-field étale-ring-map
lemma. Henselian finite-type decomposition gives finite local factors and a remaining factor.
Étale quasi-finiteness rules out closed-fibre points in the remaining factor, so the selected
residue extension is realized by a finite local étale factor.
9. Decompose any finite étale residue algebra into fields, lift each by step 8, and take their
finite product (`lem-weil-pbc-etale-algebra-finite-product`). Step 1 identifies its reduction.
This proves essential surjectivity; together with step 7 it proves equivalence. -/
theorem isEquivalence_baseChange_residueField_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (baseChange.{max u v} R (IsLocalRing.ResidueField R)).IsEquivalence ∧
      ∀ Sbar : CommAlgCat.FiniteEtale.{max u v} (IsLocalRing.ResidueField R),
        ∃ S : CommAlgCat.FiniteEtale.{max u v} R,
          Nonempty ((baseChange.{max u v} R (IsLocalRing.ResidueField R)).obj S ≅ Sbar) :=
  sorry

end CommAlgCat.FiniteEtale
