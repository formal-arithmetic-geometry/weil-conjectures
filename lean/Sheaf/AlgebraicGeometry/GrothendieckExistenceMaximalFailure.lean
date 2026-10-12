/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # A maximal closed counterexample to proper algebraization

Source: Stacks Project, Proposition 088C, first two paragraphs of the proof.
(blueprint: lem-weil-pbc-proper-existence-maximal-failure).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Failure of proper existence reduces to a nonempty closed subscheme on which
algebraization fails, but completion on every nonzero closed quotient is an equivalence.
Source: Stacks Project, Proposition 088C, first two paragraphs of the proof.
(blueprint: lem-weil-pbc-proper-existence-maximal-failure).

Proof:
1. Properness over the Noetherian base makes X Noetherian. Full faithfulness of completion
is Lemma 0883, so failure of equivalence means failure of essential surjectivity.
The kernel ideal of Spec(A/I) is the ideal associated to I, by global sections on Spec A.
2. For each quasi-coherent ideal L of X, let P(L) mean essential surjectivity of completion
on its closed subscheme. The zero closed subscheme is X, so the failing ideals are nonempty.
Noetherian ACC (Tag 01Y8) gives a maximal failing ideal L. Put Z = V(L) and j = its inclusion.
Closed immersions and proper morphisms compose, hence j followed by f is proper.
3. Z is nonempty: modules and systems on the empty scheme are zero, and completion of the
zero coherent module algebraizes its only formal system. Choose a failing formal object M
on Z; this is existential proof data, not a definition of a chosen module.
4. A nonzero ideal K on Z corresponds to an ideal of X strictly containing L, by inverse
image under O_X -> j_*O_Z. Its quotient closed subscheme is the closed subscheme of Z cut out
by K (closed-immersion ideal correspondence). Maximality gives essential surjectivity there;
proper full faithfulness gives equivalence. Equal defining ideals identify the closed
subschemes and their extended completion ideals, so this is the stated canonical quotient.
Noetherian witnesses are propositions and the assertion holds for every such witness. -/
theorem proper_existence_maximal_failure
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (hbad : ¬ (@completion X (isNoetherian_of_locallyOfFiniteType f)
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)).IsEquivalence) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X) (_ : IsClosedImmersion j)
      (_ : IsProper (j ≫ f)) (hZ : IsNoetherian Z) (_ : Nonempty Z),
      let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap (j ≫ f)
      ∃ M : @CoherentFormalModule Z hZ J,
        (¬ ∃ F : CoherentModules Z, Nonempty ((@completion Z hZ J).obj F ≅ M)) ∧
        ∀ (K : Z.IdealSheafData), K ≠ ⊥ → ∀ (hW : IsNoetherian K.subscheme),
          (@completion K.subscheme hW (J.comap K.subschemeι)).IsEquivalence := by
  sorry

end AlgebraicGeometry
