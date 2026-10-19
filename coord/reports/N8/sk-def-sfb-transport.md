# Stage-1 report: sk-def-sfb-transport

## Files written

- `dag/nodes/sec-proetale-coefficients/sk-def-sfb-transport.json`: existing definition, split with seven sourced steps; the complete four-part item is not a Mathlib leaf. Statement unchanged. Added the existing named constructions to `stmt_deps`, since this aggregate definition is built from them.
- `citations.json`: verbatim statement quotations for every step/node citation.
- `report.md`: this report. No new DAG nodes, no new Mathlib leaves. `prepare.py` is the sandbox-only script used for the JSON edit; `searches.jsonl` is the real msearch log.

## Attachments

No attachment for the entire item. `CategoryTheory.Functor.mapMod`, `CategoryTheory.Functor.modObjObj`, and `CategoryTheory.Functor.act_mapMod_obj` belong to `def-sfb-modobj-transport`; this attachment is already recorded and closed in the shared DAG. Read `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Mod.lean`, lines 145–172 and 199–201, in the read-only slopmaster2 source. These declarations cover part 1 only. Searches of `WeilConjectures/` by the item's blueprint tag, transport terminology and all expected adjunction/projection-formula names found no implementation of the remaining clauses. Therefore part 1 does not warrant attaching the aggregate.

## WANTED

None. This is the general categorical interface supplied by the current blueprint; no Stacks tag or SGA result is needed or cited.

## Problems found and changes

The imported proof was three paragraphs saying which definitions provide the claims. All nine referenced nodes already exist, and their statements supply the constructions being requested. Kept that route, but expanded the paragraphs into seven steps specifying hypotheses, actions and the adjunction bijections. In particular the identification of the right linearization with transport in part 4 is now a typed mate calculation and triangle identity, rather than an unsupported assertion.

No false statement or missing hypothesis was found in the item. In particular no symmetry, commutativity, abelianity, cocompleteness or exactness hypothesis is used. The existing child `def-sfb-modobj-linearized-adjunction` introduces its context by a reference to the previous construction; I resolved that context by reading that construction's statement and supplied the adjunction, counit and module types explicitly in step 4. The child itself is outside my editing scope.

The imported item and its nine child nodes have no `chapter` or `unit` metadata. Neither `dag/chapters/sec-proetale-coefficients.json` nor `dag/units/sk-def-sfb-transport.json` exists. Read instead the current chapter's `_section.md`, this item's `_section.md`, its `.proof.md`, and all nine construction `.md` files with their proof companions. No unit record was created or maintainer-owned binding modified. The chapter's coefficient-category route and the unit's three proof paragraphs are preserved.

## Unfinished work

None for the one-level split. Existing imported child nodes retain their own stage-1 work; I have neither split nor edited them. No Lean was written and no compiler, Lake or build tool was run. Delivery is left to the second reader after the required dry run.

## Not duplicates

No new nodes. Whole-blueprint searches for `projection formula` and `transport`, the ancestor query, DAG searches and source searches confirmed that all nine required nodes already exist. Other hits concern derived projection formulas, geometric operations, special symmetric-monoidal transport or coefficient comparisons, and do not state the complete four-part interface. Accordingly `blueprint.same_as` is `[]`; `blueprint.from` remains null because this item is itself imported.

## Review by N8

I read the current main-20261015 item `_section.md` and `sk-def-sfb-transport.proof.md`, and all nine sibling definition sources and their proof companions. There are no new-node sources to audit. I checked the actual statements of each existing node against each use, not merely their proof text:

1. `def-sfb-modobj-transport` explicitly gives the transported monoid's multiplication/unit, module action, linearity of `Ff`, and the functor commuting with forgetful functors. Its assumptions are exactly monoidal categories, lax monoidal F, and a monoid R. This supports every claim in step 1 and part 1.
2. `def-sfb-modobj-transport-adjunction` states both monoid-linearity of the unit at R and the adjunction after restricting scalars. Its assumption that the structures are mates is present in part 2. Step 2 uses its statement about the hom bijection, not the calculation inside its proof.
3. `def-sfb-projection-formula` states the natural isomorphisms and both coherence identities. `def-sfb-modobj-linearization` states the inverse-projection-formula action on PM, its module axioms, linearity of Pf and the functor. S is strong monoidal and B is a monoid in D, so the source modules really are over SB and the target modules over B.
4. `def-sfb-modobj-linearization-right-adjoint` states the mate theta using the counit of any given P-adjunction and the resulting action on GN; no lax monoidal structure on arbitrary G is assumed. `def-sfb-modobj-linearized-adjunction` states the restricted natural hom bijection. Thus the adjunction in step 4 comes from a cited assertion, not from just a definition of adjointness or from the phrase “taking mates”.
5. `def-sfb-adjunction-has-projection-formula` gives the exact mate involving the unit u and the strong monoidal structure on S. `def-sfb-adjunction-projection-formula` asserts that invertibility supplies all the coherence required by `def-sfb-projection-formula`. Merely defining a projection-formula map would not have sufficed for this step; the second node is needed and cited.
6. For the equality of right linearizations, the right-adjoint construction's statement supplies theta, the canonical-map statement supplies the mate of pi, and transport's statement supplies the action for mapMod(S). The step computes theta as S(L tensor c_N) composed with mu at (L,PSN) and SL tensor u_SN; these are composable maps starting at SL tensor SN. Naturality rewrites the last two factors to SL tensor (S(c_N) composed with u_SN), and the triangle identity makes this the identity of SL tensor SN. Consequently theta equals mu at (L,N). Applying S to the action of N gives exactly the transported action. Both functors have the same arrow assignment. This is a direct computation from the three cited constructions, so I marked this step elementary and did not invent a node for it.
7. `def-sfb-modobj-linearized-adjunction` gives the adjunction after the previous identification. `def-sfb-modobj-linearization-transport-adjunction` explicitly states that its hom bijection is the original adjunction's, so the resulting construction agrees with the blueprint's final named adjunction.

For C4 I copied whole verbatim statements into citations.json so the second reader can compare the actions, types and hom bijections directly. For C1 every non-elementary assertion in these steps is a statement of one of those existing nine nodes. No claim is imported from the proof of a child. Their statement dependencies have been opened and checked for direction: the source/target switch in restriction of scalars is from GF(R) to R, while right linearization sends B-modules in D to SB-modules in C. Existing dependency edges do not return to this aggregate.

For B and D I created no statement-only placeholder, duplicate, elementary fact node or replacement clause node. The current unit's exact existing nine-node route is retained; the item is a definition built from these pre-existing constructions, rather than a theorem whose substance was moved into new lemmas. The JSON preserves every imported flag and blueprint field, with only same_as filled. The statement was not corrected or weakened.

For E I tested the formulas on the identity adjunction and identity monoidal functor: theta is the identity tensorator and the lifted functors are the identity. For the unit monoid in a tensor category, forgetting the module structure reduces the lifted bijections to the original adjunction bijections. For ordinary noncommutative rings as monoids in abelian groups, the left-module formulas need no commutativity. The mate computation uses the given adjunction's triangle identity and never identifies two unrelated choices of right adjoint. Empty monoidal categories require no separate exception because a monoidal unit is part of the hypotheses.

All Mathlib searches were actually run through msearch.py. I tried a second semantic phrasing, a second Loogle query and wider grep patterns, then read the pinned sources for mapMon, Adjunction.mapMon, rightAdjointLaxMonoidal, scalar restriction and coherent lineators. These results cover only ingredients, not every clause of the item. None of the services was unavailable in this run. No unrun search has been recorded and no partial match has been declared a leaf.

## Second reading by N8

- Item statement: checked all four clauses against `sk-def-sfb-transport/_section.md` in the main-20261015 blueprint, including the monoidal, module, adjunction, and projection-formula hypotheses; verdict: unchanged and faithful.
- Step 1: checked against `def-sfb-modobj-transport` and its displayed transported action, monoid structure, linearity, and forgetful-functor claim; verdict: every assertion is stated by the cited node.
- Step 2: checked against `def-sfb-modobj-transport-adjunction` (including the unit as a monoid morphism, restriction of scalars, and restricted hom bijection); verdict: hypotheses and direction of the adjunction agree.
- Step 3: checked against `def-sfb-projection-formula` and `def-sfb-modobj-linearization`, including inverse projection map, source and target module categories, and action; verdict: cited statements supply the complete construction.
- Step 4: checked against `def-sfb-modobj-linearization-right-adjoint` and `def-sfb-modobj-linearized-adjunction`; verdict: the mate, induced action, functoriality, and restricted adjunction are all present in the cited statements.
- Step 5: checked against `def-sfb-adjunction-has-projection-formula` and `def-sfb-adjunction-projection-formula`; verdict: the canonical mate and the invertibility/coherence implication have the required types.
- Step 6: checked the typed mate calculation against `def-sfb-modobj-linearization-right-adjoint`, `def-sfb-adjunction-has-projection-formula`, and `def-sfb-modobj-transport`; verdict: naturality plus the adjunction triangle identity identifies the two actions and arrow assignments, so the elementary mark is justified.
- Step 7: checked against `def-sfb-modobj-linearized-adjunction` and `def-sfb-modobj-linearization-transport-adjunction`; verdict: the final hom bijection and identification with transport are exactly stated.
- New nodes: none; all nine construction dependencies already exist in the DAG, so there are no B1–B7 node statements or duplicate/Mathlib leaves to repair.
- Small cases: rechecked identity functor/identity adjunction, the unit monoid, and ordinary possibly noncommutative ring modules; verdict: all four clauses and the mate calculation remain well typed, with no extra commutativity or exactness assumption.

Changes made in this second reading: appended this per-step audit; no node or citation text required correction.
