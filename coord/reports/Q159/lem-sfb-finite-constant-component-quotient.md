# Q159 stage-1 report: lem-sfb-finite-constant-component-quotient

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-constant-component-quotient.json`: statement, split; no exact Mathlib match. The proof constructs the group on components, the finite constant scheme, and the quotient homomorphism, then identifies its fibres.
- `citations.json`: 17 exact statement quotations for the 17 step/node incidences.
- `searches.jsonl`: actual search-command records; all results read.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. All required facts already have nodes, so there is no reason to create auxiliary duplicates. No Lean files were written and no compiler, Lake, build, or local preflight was run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and by component-group, connected-component, and group-scheme concepts. `GroupScheme/Basic.lean` and `GroupScheme/AmpleFamily.lean` provide component geometry and a disjoint-union isomorphism, not the finite constant quotient group scheme with the required homomorphism identities and fibres. Thus no declaration states the whole item; no attachment is claimed. The displayed Galois-category and profinite-group Mathlib hits likewise concern different objects. `AlgebraicGeometry.sigmaSpec` and its finite-isomorphism instance were read in `Mathlib/AlgebraicGeometry/Limits.lean`, lines 604–647: this supports the already existing coproduct-spectrum leaf, not an attachment or Mathlib match for the item.

## WANTED

None. The required Milne PDF and Stacks sources are present and were read locally.

## What needed repair

The item had a complete, correct statement but no proof. Its statement, statement dependencies, inherited source, creation record, blueprint provenance and earlier Q91 search results were retained. The new proof spells out the part hidden by the construction preceding Milne Proposition 2.37: a multiplication on components must come from multiplication on component-product schemes, and equality on rational points alone would not prove the group-scheme homomorphism property for a nonreduced source. The proof therefore uses connectedness to determine a component, and then equality of the unique structural maps to a copy of Spec k to establish scheme-morphism identities on an open cover.

I read GOAL.md, the chapter and unit records, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. The latter's clause (3) is the direct-image branch to which the inherited component-group support is assigned; this delivery changes no unit or chapter claim. The ancestor command returns `None` on this inherited provenance chain, so the existing `blueprint.from.node = null` and its complete place/via chain were retained. Whole-DAG statement/title searches and `blueprint_refs.py search` for component, connected components, constant group, etale algebra, and irreducible products found no equivalent quotient statement. In particular `sk-p-geometry` describes components/cosets for its algebraic groups but does not construct the required quotient homomorphism for arbitrary nonreduced group schemes. It was not used as a surrogate for the item.

## What could not be finished

Nothing in the mathematical split. Required server dry run and delivery are recorded below after they finish.

## Review by Q159

I checked the split against delivery-errors B–E, reading the cited statements rather than borrowing their proofs. For the item I read Milne Section 2(g), the construction preceding Proposition 2.37 and its proof and Remark 2.39, printed pp.51–52, together with Propositions 1.29–1.34 and the component discussion, printed pp.14–17. I also read Stacks groupoids.tex, Tag 0B7R, `proposition-connected-component`, which explicitly gives geometric irreducibility without reducedness. No SGA source is used. There are no new nodes needing separate source or duplicate review.

Step 1 uses the statement of `lem-sfb-group-neutral-component-translates` for finite clopen components, their open-subscheme structures, and rational translation isomorphisms. Its algebraically closed finite-type hypotheses are exactly those of the item. The separate statement of `lem-sfb-locally-algebraic-group-identity-component` explicitly gives geometric irreducibility of the original identity component; finite type implies its locally finite type assumption. The definition `def-pc-geometrically-irreducible` makes invariance under an isomorphism after any field extension a direct verification. I checked that neither supporting node depends on this item. In particular this does not use the smooth reduction clause of the larger identity-component node.

Step 2 uses `lem-sc-irreducible-product-over-field` exactly with the two geometrically irreducible open components established in step 1; its field and scheme-over-field hypotheses hold. I read Tag 038F, `lemma-bijection-irreducible-components`, in varieties.tex: it gives the product irreducibility input. Connected images under a continuous map and their containment in a maximal connected component follow from connectedness, whose definition is cited. The group-scheme definition explicitly supplies the group G(k). Surjectivity on rational representatives comes from step 1, not an unsupported general rational-point surjectivity assertion. I wrote out associativity, unit, and inverse identities on representatives. This is a generic off-unit geometric tool use, declared in `split_report.tool_uses`; it does not change the unit route.

Step 3 uses `lem-weil-pbc-scheme-coproduct-family` for the existence and disjoint clopen inclusions of the copies of Spec k. `lem-weil-pbc-open-fibre-product` gives the exact open subsets covering products, not an identification of the topological scheme product with the ordinary product of spaces. Its hypotheses apply with the whole base Spec k and the indicated component opens. The fibre-product definition identifies each pair of base copies with Spec k. The morphism gluing statement provides both existence and equality on open covers; I read the gluing mapping property in Stacks Tags 01JB/01JC and the open product statement in 01JR. Checking the group diagrams summand by summand uses only the already proved group laws and uniqueness of a map over the base to Spec k. The existing Mathlib leaf `lem-weil-pbc-finite-affine-coproduct-spectrum` states the canonical affine identification, including its coprojection maps, exactly as used. Finite type is proved by the explicit finite list of coordinate idempotent generators, under the cited finite-type definition.

Step 4 applies the same gluing and open product statements to the actual clopen cover of G and G times G. For the multiplication image containment established in step 2 I use `lem-weil-pbc-morphism-factors-through-open-subscheme`: its statement really does permit factorization from set-theoretic containment because the target is an open subscheme. Both resulting composites on each piece are the structural map followed by the same labelled inclusion; this proves equality of scheme maps even with nilpotents. The inverse and identity checks are explicit. These are the homomorphism diagrams in `def-sc-group-scheme`, not a weaker assertion about rational points.

Step 5 is elementary from the already constructed labelled map and the disjoint nonempty component partition: each inverse image is exactly its corresponding component, which proves surjectivity and the identity-fibre assertion. No separate lemma restates a clause of the item. Each step is below 2000 characters, and all non-elementary ingredients are cited nodes. The exact quotations in citations.json were checked as substrings of the corresponding statements.

For small cases I checked the trivial group, a connected nonreduced group such as alpha_p or mu_p in characteristic p, a disconnected finite constant group, and a product of a connected nonreduced group with a nontrivial finite constant group. In the connected cases P has one element and c is the structural map, so nilpotents are preserved throughout the construction. In the constant case the quotient is the labelled identity. In the product case its fibres are copies of the connected factor. The empty group scheme cannot occur over a field because the identity section exists, so P is nonempty and its distinguished identity component always exists. No perfectness, characteristic-zero, smoothness, reducedness, or commutativity hypothesis was silently imposed beyond the algebraically closed field already required.

## Not duplicates

No new nodes were created. Existing component geometry, products, gluing, and coproduct-spectrum statements were reused directly.

## Dry-run diagnostics

The first dry run required longer group-scheme-definition quotations (minimum 40 characters). Replaced each of these three short excerpts with the complete verbatim definition; the cited mathematical content and proof are unchanged.
