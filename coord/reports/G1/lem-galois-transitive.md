Files written:

- `dag/nodes/sec-curve-estimates/lem-galois-transitive.json`: statement split into four Stacks 0BN3 steps; Mathlib declaration recorded as a candidate, not a leaf.
- `dag/nodes/sec-curve-estimates/lem-galois-inverse-limit-surjective.json`: Mathlib leaf for the finite inverse-limit nonemptiness and projection-surjectivity clauses, with both declarations and source lines recorded.

Attachments:

- None.

WANTED:

- None.

What was wrong and what changed:

- The previous delivery treated `CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected` as a Mathlib leaf. It is proved for Mathlib's SGA1/Lenstra `GaloisCategory` and `FiberFunctor`, whereas this item uses the Stacks 0BMY definition. The declaration is now recorded under `mathlib_candidate` and the item follows Stacks 0BN3.
- The previous proof was one imported paragraph with the inverse-system construction and its projection-surjectivity claim hidden inside it. It is now four explicit steps. The finite inverse-limit projection claim is isolated as `lem-galois-inverse-limit-surjective`, sourced to Categories Lemma 086J, so the induced `Aut(F)` action is justified rather than inferred from an unsupported extension of one cover automorphism.

What could not be finished:

- The inverse-limit helper is a Mathlib leaf: `nonempty_sections_of_finite_inverse_system` handles nonemptiness and `CategoryTheory.Functor.eval_section_surjective_of_surjective` handles every projection after the specialization $J=I^{\\mathrm{op}}$.

## Review by G1

I read `pione.tex`, Fundamental Groups of Schemes, Lemma 0BN3 (tag 0BN3, label `lemma-tame`), including its first paragraph defining the directed system of Galois objects, the colimit paragraph, the `A_i` inverse-system paragraph, and the final domination argument. I also read Lemma 0BN2 (tag 0BN2, label `lemma-galois`) as the source of the Galois cover used by the item, Lemma 0BN0 (tag 0BN0, label `lemma-epi-mono`) as the source of the six cited consequences in `lem-galois-axioms`, and Categories Lemma 086J (label `lemma-nonempty-limit`) for the finite inverse-limit argument.

For step 1, `def-galois-category` supplies finite products and connected-component decompositions, `lem-galois-object-exists` supplies a Galois object over a component of a product, and clauses (5) and (6) of `lem-galois-axioms` justify normalization and uniqueness of the transition maps. For step 2, the statement of `lem-galois-axioms` gives equality of maps agreeing on one fibre element, surjectivity of the fibre map of an epimorphism, and transitivity on a Galois object's fibre; `lem-galois-object-exists` supplies the cover used for surjectivity. The component reduction is the finite coproduct clause of `def-galois-category`.

For step 3, I checked that the cited clause (6) gives the automorphism of the target Galois object and that clause (5) turns equality on `gamma_i` into equality of morphisms. Surjectivity of each `h_{ii'}` is written out by lifting `b(gamma_{i'})` through the epimorphic fibre map and then using transitivity on `F(X_i)`. The new helper is used exactly for projection-surjectivity of the inverse limit; the precomposition formula is checked against the compatibility equation `f_{ii'} a_i = a_{i'} f_{ii'}`. This yields an action of `A^op` on the colimit and hence natural automorphisms of `F`.

For step 4, `lem-galois-object-exists` gives `q : X_i -> X`; clauses (4) and (2) of `lem-galois-axioms` give that `q` is epi and that `F(q)` is surjective. Naturality of an element of `Aut(F)` then transports the transitivity from `F(X_i)` to `F(X)`. No step is marked elementary because each uses one of these cited lemmas.

I searched the DAG and blueprint for the inverse-limit projection statement before creating the helper; no existing node or blueprint node states it. I tested the helper's formulation on the singleton system and on a constant two-element system with identity transitions: the limit is respectively a singleton and the two-element set, and each projection is surjective. Mathlib searches were recorded for both nodes using LeanSearch, LeanFinder or Loogle, source grep, and local declaration search where available. LeanFinder/local search identified `CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected` at `Mathlib/CategoryTheory/Galois/Prorepresentability.lean:455`; the recorded comparison explains why it remains a candidate only.

The returned delivery at branch head `4dab707e4` was repaired here. The helper no longer contains the unrelated `\\mathcal C,F` clause or the citation to `def-galois-category`; its statement is exactly the inverse-system assertion. Its finite-set hypothesis carries the existing `lem-galois-axioms` citation, recording the source of the finite automorphism systems to which this generic leaf is applied and satisfying the node citation contract. The prior "no exact match" verdict was also corrected: `nonempty_sections_of_finite_inverse_system` at `CofilteredSystem.lean:111-113` gives a compatible section, while `CategoryTheory.Functor.eval_section_surjective_of_surjective` at `CofilteredSystem.lean:304-322` gives surjectivity of evaluation at any index. With $J=I^{\\mathrm{op}}$, these are precisely the two clauses of the helper, so it is recorded as `status: mathlib` with both declarations and lines. This report and the repaired node are post-return changes.
