/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.RingTheory.PairHenselization
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Noetherian henselization of a pair and its completion

Source: Stacks Project, More on Algebra, Lemma 15.12.4, Tag 0AGV
(blueprint: lem-weil-pbc-henselization-noetherian-completion).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- The henselization of a Noetherian pair is Noetherian and flat over the base, has the
same adic completion, and maps faithfully flatly to the completion of the base.
Source: Stacks Project, Tag 0AGV
(blueprint: lem-weil-pbc-henselization-noetherian-completion).

The colimit cocone is the presentation in `pair_henselization`; its vertex is `Aʰ` and
`c.pt.hom.hom` is the structure map. The condition on every quotient projection specifies
that `θ` is the map induced by this structure map, not merely an abstract ring isomorphism.
It also implies compatibility with the `A`-algebra structures. The displayed composite
with `θ.symm` is exactly the map `γ : Aʰ → Â` in the node.

Proof (the seven steps of the node):
1. By lem-weil-pbc-pair-henselization, the vertex is the filtered colimit of étale
   algebras trivial modulo `I`, its extended ideal is henselian, and reduction is an
   isomorphism. Extension of ideals commutes with powers.
2. By lem-weil-pbc-henselization-flat-quotients, the structure map is flat and induces
   isomorphisms modulo every positive power. These commute with transition maps, so
   their inverse limits give the canonical completion isomorphism and its inverse.
3. Each étale stage is finitely presented, hence Noetherian, by
   lem-weil-pbc-lfp-affine-opens-finite-presentation and
   lem-weil-pbc-finite-type-algebra-noetherian.
4. Each stage has the same completion as the base, by lem-weil-pbc-etale-algebra-flat
   and lem-weil-pbc-flat-iso-mod-ideal-powers. Compatibility of coprojections shows
   that its comparison to the completion of the colimit is the same isomorphism.
5. The completion map of each stage is flat by lem-weil-pbc-noetherian-completion-flat.
   Apply lem-weil-pbc-colimit-rings-flat to deduce flatness of the completion map of
   the vertex, hence of its composite with the inverse completion isomorphism.
6. The extended ideal lies in the Jacobson radical by
   lem-weil-pbc-henselian-factorization-criterion. By
   lem-weil-pbc-adic-completion-mod-ideal, the composite reduces to the quotient
   isomorphism, so every maximal ideal extends to a proper ideal. Apply
   lem-weil-pbc-flat-faithfully-flat-maximal-ideals to get faithful flatness.
7. The base completion is Noetherian by lem-weil-pbc-adic-completion-noetherian.
   Faithfully flat descent, lem-weil-pbc-faithfully-flat-descent-noetherian, then
   proves that the vertex is Noetherian. -/
theorem pair_henselization_noetherian_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c) :
    IsNoetherianRing c.pt.right ∧ c.pt.hom.hom.Flat ∧
      ∃ θ : AdicCompletion I A ≃+*
          AdicCompletion (I.map c.pt.hom.hom) c.pt.right,
        (∀ (n : ℕ) (x : AdicCompletion I A) (a : A),
          AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a →
          AdicCompletion.evalₐ (I.map c.pt.hom.hom) n (θ x) =
            Ideal.Quotient.mk ((I.map c.pt.hom.hom) ^ n) (c.pt.hom.hom a)) ∧
        (θ.symm.toRingHom.comp
            (algebraMap c.pt.right (AdicCompletion (I.map c.pt.hom.hom) c.pt.right))).comp
            c.pt.hom.hom = algebraMap A (AdicCompletion I A) ∧
        RingHom.FaithfullyFlat
          (θ.symm.toRingHom.comp
            (algebraMap c.pt.right (AdicCompletion (I.map c.pt.hom.hom) c.pt.right))) := by
  sorry

end RingTheory
