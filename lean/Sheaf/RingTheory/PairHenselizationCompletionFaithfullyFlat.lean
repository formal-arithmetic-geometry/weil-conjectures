module

public import Sheaf.RingTheory.PairHenselization
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Sheaf.RingTheory.BijectiveQuotientMapPowOfFlat
import Sheaf.RingTheory.FlatColimitRings
import Sheaf.RingTheory.HenselianFactorizationCriterion
import Sheaf.RingTheory.PairHenselizationCompletionData

/-!
# Faithful flatness of the completion comparison for a pair henselization

Source: Stacks Project, More on Algebra, Tag 0AGV, middle paragraphs of the proof.
(blueprint: lem-weil-pbc-henselization-completion-faithfully-flat).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace RingTheory

/-- The canonical map from a pair henselization to the base completion is faithfully flat.
Source: Stacks Project, More on Algebra, Tag 0AGV, middle paragraphs of the proof.
(blueprint: lem-weil-pbc-henselization-completion-faithfully-flat).

Proof: The pair-henselization theorem presents the vertex as a filtered colimit of
étale A-algebras B trivial modulo I and makes its extended ideal J henselian.
These properties transfer to the specified cocone by the unique colimit isomorphism
in the under category, which carries the structure map and extended ideal with it.
Each B is finitely presented over A, hence Noetherian. Étale flatness and the
flat quotient-power lemma identify A/I^n with B/(IB)^n for every positive n.
These identifications commute with transitions, hence identify the B-completion
with the A-completion. For the coprojection B → Aʰ, its composite with the map
γ = θ⁻¹ ∘ completion has, on every quotient coordinate, precisely this comparison:
both composites send a representative b to its image in the henselization quotient.
Thus B → A^ is the completion map B → B^ followed by the comparison isomorphism.
It is flat since B is Noetherian. Flatness over a filtered colimit now makes γ flat.
The henselian-pair factorization criterion gives J ⊆ Jac(Aʰ). Evaluate the base
completion at n = 1. The given compatibility for θ and the isomorphism A/I → Aʰ/J
show that this projection composed with γ is the quotient map Aʰ → Aʰ/J followed
by that isomorphism's inverse. For each maximal ideal m of Aʰ, J ⊆ m, and the
image of m in Aʰ/J is proper. Consequently m A^ is proper, since its image under
the projection A^ → A/I lies in that proper ideal. The maximal-ideal criterion
for faithful flatness applies to the flat map γ. No Noetherianity of Aʰ is used. -/
theorem pair_henselization_completion_faithfullyFlat
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun C : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c)
    (θ : AdicCompletion I A ≃+*
      AdicCompletion (I.map c.pt.hom.hom) c.pt.right)
    (hθ : ∀ (n : ℕ) (x : AdicCompletion I A) (a : A),
      AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a →
      AdicCompletion.evalₐ (I.map c.pt.hom.hom) n (θ x) =
        Ideal.Quotient.mk ((I.map c.pt.hom.hom) ^ n) (c.pt.hom.hom a)) :
    RingHom.FaithfullyFlat
      (θ.symm.toRingHom.comp
        (algebraMap c.pt.right (AdicCompletion (I.map c.pt.hom.hom) c.pt.right))) := by
  sorry

end RingTheory
