# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-sset-pullback-preserves-colimits.json`: item, statement, split; no change to its statement or hypotheses. Six proof steps establish existence of slice colimits, the strict comparison, its bijectivity in every degree, and naturality.
- `dag/nodes/sec-six-functors/lem-coef-small-set-colimit-quotient.json`: new statement, Mathlib leaf. It is the general quotient construction of an arbitrary small set colimit, not the pullback-preservation assertion.
- `citations.json`: a verbatim statement quote for every node used by every proof step.
- `searches.jsonl`: actual msearch.py results. The item's inherited search records were retained; new searches supplement them. `prepare_split.py` is sandbox-only preparation material.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the blueprint tag, simplicial/pullback/colimit terminology, and the general set-colimit declaration names found no project declaration stating this item. The actual quotient-colimit declarations are Mathlib declarations and are recorded as a leaf, not an attachment. No compiler, Lake, or Lean-writing operation was performed.

## Literature wanted

WANTED: Charles Rezk, *Fibrations and homotopy colimits of simplicial sheaves*, https://rezk.web.illinois.edu/rezk-sharp-maps.pdf, Proposition 3.7, printed p. 6, for lem-coef-sset-pullback-preserves-colimits. I read the proposition and the following proof online; an archived copy is absent from the named literature directory. No download or change to literature was made. The source reduces the assertion to sets, then presheaves, but does not give the set calculation. The delivered proof supplies that calculation and is marked agent-written, using the local Stacks construction rather than treating the proposition as a black box.

## Corrections and limitations

No STATEMENT-DISPUTED: the item is correct as written, including arbitrary, disconnected and empty small index categories. There is no fibrancy or injectivity assumption. Its immutable source already identifies Rezk Proposition 3.7. The proof of that proposition concerns base change along a map to the colimit; for the item's more general displayed expression this is the same situation with the object E times_B L mapping to L. The delivered representative proof handles the displayed expression directly, so no unrecorded reassociation theorem is needed.

The current blueprint ancestor was read at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. Its second paragraph is the derived coefficient adjunction served by the existing technical chain. The item retains the existing ancestry and unit; it is not the unit key node, so no unit record was edited. The chapter and unit records were read. This strict simplicial-set calculation makes no assertion about homotopy colimits or infinity-categorical pullbacks and does not replace a unit-level proof route.

## Searches and leaf verification

Before creating the leaf I searched the whole DAG for the set quotient construction, `ColimitType`, its declaration names, disjoint unions and generated equivalence relations, and searched the entire imported blueprint with blueprint_refs.py for pullback colimits, simplicial pullback, colimit of sets, disjoint union, quotient and equivalence relation generated. I opened the plausible set, presheaf and simplicial-category nodes. The presheaf-colimit node was reused. No existing blueprint node states the new leaf.

All new Mathlib searches were run with the required msearch.py command under NP and this item. LeanFinder, LeanSearch and Loogle all returned the explicit quotient construction; grep located its source. I read `Mathlib/CategoryTheory/Limits/Types/ColimitType.lean`, especially lines 105-158, and `Types/Colimits.lean`, especially lines 32-33 and 97-107. `ColimitTypeRel` is precisely the arrow-generated relation, `ColimitType` its quotient, `ιColimitType_eq_iff` gives equality modulo the equivalence closure, and `ιColimitType_jointly_surjective` supplies representatives. `colimitCoconeIsColimit` gives the categorical universal property, with the smallness instance supplying its sole universe obligation for a small index category. These declarations supply each clause of the leaf with no supplementary mathematical hypothesis. The empty quotient clause unfolds its empty disjoint union.

For the item, the fresh strict-pullback LeanFinder search returned SSet.hasColimits and related instances, which give existence alone. The exact Loogle combination and grep returned no match. I also read the candidates from the retained searches: ExponentiableMorphism.lean requires exponentiability as extra data, VanKampen.lean defines universal colimits without asserting universality for simplicial sets, and Types/Colimits.lean gives set representatives. These cannot attach or make the whole item a one-line Mathlib specialization. The retained alternative phrasings were read and not rerun merely to regenerate logs.

## Not duplicates

lem-coef-small-set-colimit-quotient vs lem-coef-simplicial-category-degreewise-colimits: the existing node, also citing Stacks 002U, constructs colimits of enriched simplicial categories with mapping-category relations; it does not state the quotient construction or representative/equality criterion for an arbitrary diagram of sets. In particular its object-set colimit is input to that statement, not a theorem constructing it.

lem-coef-small-set-colimit-quotient vs det-pe-classical-definition-continuity-map: the existing node, also citing 002U, defines the continuity maps and classical pro-etale sheaves using filtered sections diagrams. It neither constructs arbitrary set colimits nor supplies their generated-equivalence-relation equality criterion.

lem-coef-small-set-colimit-quotient vs lem-weil-pbc-filtered-colimit-sets-elementwise: that node assumes a filtered category and gives eventual equality in a common target. The new leaf permits arbitrary and empty small categories, where common-target equality is generally false and the full generated relation is required.

lem-coef-small-set-colimit-quotient vs lem-weil-pbc-presheaf-colimits-sectionwise: the existing leaf starts with chosen sectionwise colimits and proves their presheaf universal property. The new leaf constructs the set colimits and their representatives, so its statement is not a specialization of that conditional presheaf statement.

## Review by NP

I checked this split against delivery-errors B through E with the source and cited statements open. For the item I read Rezk Proposition 3.7 and its reduction to sets/presheaves online, the Stacks source `categories.tex` section-limit-sets (Tag 002U), and `sites.tex` section-limits-colimits-PSh (Tag 00VB). I verified those tags in stacks-project/tags/tags. For the only new node I read the same Stacks 002U quotient formula and generated-relation paragraph together with the Mathlib declarations listed above. The node is statement-only and a Mathlib leaf; no proof is hidden in its statement. It introduces its universe, category, diagram and relation explicitly.

Step 1 cites the simplicial-set definition for its actual presheaf description, the new leaf for existence and representatives of all degreewise set colimits, and the existing presheaf-colimit leaf for assembling those chosen colimits. I reread the latter's entire statement: it allows values in sets, assumes only a small index category, and gives the structure maps, natural cocone legs and universal property. Consequently no existence assertion is taken from a node that merely assumes existence. The smallness hypothesis is checked degree by degree with the same I and universe.

Step 2 uses exactly colimit descent and uniqueness from the cited category-colimit definition. The displayed comparison of two maps to B proves, rather than assumes, that the descended map lies in the slice. It has no connectedness requirement and works for the empty diagram. No theorem about creation of colimits by a slice forgetful functor is imported silently.

Step 3 uses the definition that simplicial sets and their morphisms are functors and natural transformations. It writes the operators on the pair sets, verifies the defining base equation by naturality, and checks the universal property on every simplex. Thus the strict pullback formula and its functoriality are proved directly, not taken from a definition node making no such assertion.

Step 4 cites the category-colimit definition for the induced canonical comparison and the quotient leaf for representatives. The comparison has the right direction, from the colimit of the pullbacks to the pullback of the colimit. Its preimage formula satisfies the fiber equality because the induced base map sends [i,x] to q_i(x). This uses the diagram maps over B, which are hypotheses of the slice diagram. I explicitly checked the empty diagram: both sides have empty sets in every degree.

Step 5 uses exactly the quotient leaf's generated-equivalence-relation equality criterion. It writes the base-value equation for each generating arrow and carries the fixed e-coordinate along forward and reverse relations. Reflexivity, symmetry and transitivity preserve the lifted equality, giving induction on the generated relation (equivalently finite chains). Thus this is a short direct quotient calculation from the cited statement, not an unsupported appeal to exactness of arbitrary colimits or an accidental use of the filtered eventual-equality theorem. In particular noninjective transition maps and reverse arrows in a zigzag are allowed. This proof of the item's substantive clause stays in the item's steps; it was not moved into a new restatement node.

Step 6 checks the inverse's simplicial identities by composing the known naturality equation with bijections. It also checks the equation over E and computes naturality under an arbitrary morphism of diagrams on representatives. The representative clause is again explicitly cited, and the simplicial-set definition identifies the resulting degreewise identities with identities of morphisms. No unproved transport or comparison compatibility is being concealed.

The edge checks include: empty I; B empty, which forces E and every X_i empty in every degree; E empty; a disconnected discrete diagram, where the formula is the ordinary distribution over a disjoint union; and a diagram with a noninjective transition map, where identifications lift with e fixed. A group-indexed diagram is also handled by the full relation rather than an invalid common-target argument. The quotient proof needs no Kan or monomorphism hypothesis and makes no homotopy assertion.

Every proof use has its verbatim node-statement quote in citations.json. All newly used notions are defined inline or are already definition nodes. The general set construction is neither elementary enough to replace by an unexplained step nor a clause of the simplicial-pullback item: it is an independent, existing Mathlib construction. The other calculations are written out as elementary steps. Every step is below 2000 characters; none hides a separately hypothesized auxiliary lemma. No statement was weakened, no source error was found, no SGA source was used, and no live repository or launcher file was edited. Only the allowed sandbox contains the delivery material.

## Unfinished work

None in the split. Server checks and the final dry run/push are performed by the mandated delivery tools; their outcome is recorded by the final delivery result.
