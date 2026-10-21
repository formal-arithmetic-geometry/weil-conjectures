# Q30 stage-1 delivery: lem-sfb-coherent-right-adjoint-comparisons

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-coherent-right-adjoint-comparisons.json`: statement split into five proof steps; no exact Mathlib match for the full indexed, normalized theorem.
- `citations.json`: a verbatim statement quote for every citation in every proof step.
- `report.md`: this report. `searches.jsonl` was produced by the required search command.

New nodes: 0. New Mathlib leaves: 0. The proof reuses two existing Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for coherent/right-adjoint/comparison terminology. The equivalence-transport theorem in `CategoryTheory/EquivalenceRightAdjointCounitTransport.lean` has different data and no indexed cocycle or componentwise uniqueness assertion; it does not attach this item. The generic Mathlib declarations are not project attachments.

## WANTED

None. The blueprint proof, Stacks source, and Mathlib source needed here are available locally.

## Corrections and route

The statement is unchanged and has no statement dispute. Its proof was empty. The construction now retains each chosen adjunction, including its particular Hom bijection and counit, rather than asserting an unnormalized uniqueness isomorphism. No dependency is taken from the proof of another DAG node. The statement dependencies remain the category definition and conjugation definition; adjunctions and natural isomorphisms are described inline in the statement.

Read the item chapter and its assigned unit `sk-prop-sf-existence`, and the current blueprint `det-sf-existence-brown.proof.md`, especially part (3). This is the categorical uniqueness/coherence calculation requested there and does not use any conditional pro-etale existence theorem or the Brown argument. This is not the unit's key statement, so no unit realization record is modified. Blueprint ancestor is `det-sf-existence-brown`; searches for coherent right-adjoint comparisons, conjugate, and uniqueness of right adjoints found no blueprint node stating the entire item. The existing square-of-adjunctions `def-sfb-conjugate-pull-iso` concerns a different four-adjunction construction, not this indexed normalization theorem.

## Mathlib searches

Retained the imported Q04 searches and ran five additional searches with `msearch.py` under this item's Q30 log: two LeanFinder phrasings, Loogle, source grep, and LeanSearch. All returned results and none was unavailable. Read the hits in `Mathlib/CategoryTheory/Adjunction/Basic.lean` (Hom formulas and `mkOfHomEquiv`), `Mates.lean` (conjugation, counit, identity, composition, and iso), and `Unique.lean` (common-left uniqueness). The two existing DAG leaves below state the needed generic results. The complete item still requires the displayed transposition calculations and an indexed assembly; it is not a one-line specialization of a returned declaration.

## Not duplicates

No new nodes were created. In particular, the natural-bijection constructor and conjugation calculus are reused instead of duplicated. The broader whole-DAG title/concept scan also found `lem-weil-common-left-adjunctions-iso`, which only asserts an isomorphism for a common left adjoint and does not state the normalized indexed theorem.

## Review by Q30

I read Stacks `categories.tex`, Tag 0037 (`definition-adjoint`) and its following discussion defining the unit, counit, and both transpose formulas, and Tag 0B65 (`lemma-transformation-between-functors-and-adjoints`) and its proof identifying the conjugate by the counit. I read the full statements of both cited DAG nodes, and checked the supporting Mathlib source. There are no new-node sources to review.

Step 1 cites `lem-weil-pbc-adjunction-of-natural-bijection`: it explicitly returns an adjunction with the very same supplied bijections, gives the stated unit and counit, and states both formulas used. Its hypotheses hold because the item assumes bijections natural in both variables. In particular this handles chosen, potentially differently normalized adjunctions.

Step 2 cites `def-weil-pbc-adjunction-conjugate` for a natural isomorphism and its component formula. With L1=Fi, R1=Gi, L2=Fj, R2=Gj, the input is phi_ji inverse: Fj to Fi, so the output has exactly the required direction Gi to Gj. This cited statement explicitly gives the formula and preserves isomorphisms. The other cited node gives the forward Hom formula that identifies this component with its specified Phi-j transpose. Naturality and invertibility here are supplied by the cited conjugation statement, not asserted from an unstated Yoneda result.

Step 3 uses only the inverse Hom formula from the natural-bijection node. Applying that inverse to the step-2 component equality proves the desired counit equation, and injectivity of the same bijection proves uniqueness among all component morphisms, without any naturality or invertibility assumption on the competing morphism. This is a direct substitution and injectivity calculation, so it is marked elementary. Equality of every component determines a natural transformation and then the isomorphism and indexed family.

Step 4 cites the composition and identity clauses actually present in the conjugation node's statement. I checked the direction: the inverse of phi_kj composed with phi_ji is phi_ji inverse composed with phi_kj inverse; conjugation reverses this again to gamma_kj composed with gamma_ji. The cocycle for phi gives the cocycle for gamma. Both inverse identities follow by choosing repeated indices; no arbitrary base index or nonemptiness of I is needed.

Step 5 cites exactly the inverse Hom formula in the natural-bijection node. Substitution of the counit identity, then the naturality square of the supplied inverse phi at b, produces h composed with phi inverse. Applying the bijection proves the final clause, including its exact normalization. This is a displayed elementary calculation using the given naturality, not an unproved compatibility assertion.

For B-E of delivery-errors I checked self-contained hypotheses, precise citations rather than proof internals, and no circular dependencies or replacement clauses. All proof dependencies are the union of step citations and are existing Mathlib leaves, so they are generic tools without changing the unit route. The verbatim citations are copied directly from their node statements. The proof contains no long step (all below 700 characters), no hidden existence theorem, and no new lemma disguised as a clause node. I checked I empty (the unique empty family), singleton I (identity comparison for the specified self-adjunction), repeated indices, identity isomorphisms with differently chosen adjunctions, and empty categories wherever the assumed functors exist. All formulas are pointwise and remain valid; there is no use of a chosen object or an index. The fixed-universe family is constructed by the given conjugation functions. No triangulated structure, coproduct preservation, or new adjoint existence is used.

## Unfinished work

None in the stage-1 split. No Lean was written or compiled, and no repository or launcher file was edited.
