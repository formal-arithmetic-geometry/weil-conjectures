module

public import Sheaf.CategoryTheory.FilteredTwoColimitModel
public import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The comparison characterizes a filtered 2-colimit

Source: blueprint main-20261015, filtered 2-colimit characterization
(blueprint: det-def-sfb-filtered-two-colimit-characterization).
-/

@[expose] public section

universe w u v u' v'

namespace CategoryTheory.FilteredTwoColimit

/-- The three finite-stage conditions characterize the corresponding properties of the canonical
comparison functor, and their conjunction characterizes its being an equivalence.

Source: blueprint main-20261015, characterization statement and proof, steps 1--5; Stacks
04AX and 02C3 (blueprint: det-def-sfb-filtered-two-colimit-characterization).

Proof plan:
1. The model's objects are pairs (i,x), whose comparison images are Phi_i(x). Thus essential
surjectivity is precisely Obj; invert the witnessing isomorphism if necessary.
2. For a pair of objects the common-stage preorder is small, nonempty and filtered. By the
filtered set-colimit representative lemma, each arrow is [k,g]. Its comparison image is theta_jk
composed with Phi_k(g) and theta_ik inverse. Hence fullness is precisely Hom-surj.
3. Under Hom-inj, move two representatives with equal images to one stage, cancel the outer
comparison isomorphisms, and apply Hom-inj there. Conjugate the resulting equality by the tau
components. The filtered set-colimit equality criterion makes the original classes equal.
4. Conversely, faithfulness applied to [k,g] and [k,g'] gives equality of classes when Phi_k(g)
equals Phi_k(g'). Normalization identifies their images with these arrows. The set-colimit
criterion supplies a later stage where their transitions agree, and tau_kkn normalization turns
this into equality after T_kn. This is Hom-inj.
5. The three clauses and the fully faithful, essentially surjective criterion give an equivalence
via Functor.asEquivalence. Conversely a quasi-inverse supplies essential surjectivity and bijective
Hom maps (Equivalence.fullyFaithfulFunctor); steps 1--4 recover the three cocone conditions. -/
theorem comparison_characterization
    {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {C : I → Type u} [∀ i : I, Category.{v} (C i)]
    {D : Type u'} [Category.{v'} D] (c : CoherentCategoryCocone (C := C) (D := D)) :
    ((comparison c).EssSurj ↔ c.toCategoryCocone.EssSurjObj) ∧
    ((comparison c).Full ↔ c.toCategoryCocone.HomSurj) ∧
    ((comparison c).Faithful ↔ c.toCategoryCocone.HomInj) ∧
    (c.toCategoryCocone.IsFilteredTwoColimit ↔ (comparison c).IsEquivalence) := by
  sorry

end CategoryTheory.FilteredTwoColimit
