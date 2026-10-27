# NW stage-1 delivery: lem-sfb-affine-target-adequacy-criterion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-target-adequacy-criterion.json`: statement, split with five proof steps; no Mathlib match. The statement and its statement dependencies are unchanged.
- `citations.json`: verbatim statement quotations for every step/node pair.
- `searches.jsonl` and `search-result-0.txt` through `search-result-4.txt`: actual Mathlib searches and their returned hits; existing item searches are retained.
- `report.md`: this report. `prepare.py` is sandbox-only preparation code.

New nodes: **0**. New Mathlib leaves: **0**. No unit or chapter record changed.

## Attachments

None. Searching `lean/WeilConjectures/` for the blueprint id and for adequate-affineness terminology returned no declaration. In particular, an ordinary affine-scheme theorem does not attach to this algebraic-stack statement.

## Literature wanted

WANTED: Jarod Alper, *Adequate moduli spaces and geometrically reductive group schemes*, arXiv:1005.2398v3, Remarks 4.1.2--4.1.3, Lemma 4.1.8(2),(3), and Lemmas 3.1.3, 3.4.4, for lem-sfb-affine-target-adequacy-criterion. The named local PDF is absent. I read the primary online text at https://arxiv.org/html/1005.2398v3 (including the actual proof of 4.1.8 and the descent proof of 3.1.3). Per the standing brief the expanded proof is marked agent-written, not a proof from an obtained local document.

The source confirms both implications without a structural-ring isomorphism and without Noetherian hypotheses. The converse in the source upgrades adequacy using polynomial algebras. Here the existing affine quasi-coherent pushforward statement gives the equivalent affine-test argument explicitly, so no polynomial-comparison lemma or new adequate-moduli assertion is needed. I also read Stacks Tags 0765 (`lemma-flat-comparison`) and 0771 (`proposition-loc-qcoh-flat-base-change`) in the local `stacks-cohomology.tex`, especially the qcqs hypothesis and degree-zero flat comparison.

## Problems found and changes

The item was statement-only. No earlier sandbox split, report, or search log existed. Its statement is correct against Alper and is preserved. The earlier adequate-moduli criteria elsewhere in the DAG require the additional structural-ring isomorphism; they cannot be used to deduce the present theorem by dropping that hypothesis. They are not cited.

The inherited blueprint ancestry has `from.node: null`; `tools/blueprint_refs.py ancestor` returns exactly `None`. I retained that ancestry and the explicit place referring to the product-affinization prerequisite. Searches of the whole imported blueprint for `adequat` and `power lifting` found no equivalent blueprint node. I read the chapter/unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`; its six-functor statement does not state the adequate-affineness tool. This split continues the supplied supporting route, changing no chapter or unit assertion.

## Not duplicates

No new nodes were created. I read the existing global-power-lifting, adequate-moduli etale-locality, affine-algebra-direct-image, flat-scalar-sections, and adequate-affineness definition nodes. The first two require a structural-ring isomorphism and were not substituted for the item. All other supporting claims already have nodes and are cited directly.

## Review by NW

I checked delivery-errors B--E against the actual statements and the primary source. There are no new statement-only nodes to audit for missing objects, hidden proof sketches, or duplicate tags. The item has a genuine argument in both directions, with no clause delegated to a restatement. Every proof step is below 2000 characters. Every id in a step is in proof_deps, and citations.json quotes the cited statement verbatim. I read each cited node's statement, not merely its proof or title.

Step 1 uses `def-sfb-adequately-affine-morphism` precisely for local lifts on the identity smooth test; `def-sfb-stack-quasi-coherent-algebra` supplies the direct-image and restriction interpretations. The finite affine covering-sieve node explicitly gives arrows belonging to the generated sieve, so each factors through an original cover member. Its base scheme need not satisfy extra finiteness assumptions. The algebraic-stack fibre-product node supplies algebraicity of the test stacks; it is not being cited for a flatness theorem.

Step 2 uses the finite affine coproduct-spectrum statement with its component maps. The etale-algebra-flat node makes each A_j flat, the finite-product-flat-modules node makes their finite product flat, and the flat-surjective-spectrum node gives faithful flatness using the stated jointly surjective maps. Taking the product of the finitely many positive exponents permits raising every lift to the same power. The sections glue only on disjoint components, with empty overlaps, by the sheaf convention in the cited definition. There is no assertion that arbitrary lifts on overlapping etale charts agree.

Step 3 checks the exact hypothesis of the flat-scalar-sections node: the given morphism f is qcqs and the ring extension from step 2 is flat. Its natural algebra isomorphisms identify the power lift with an element in the image of h tensor S. The tensor-right-exact node is applied to the module cokernel of h, not to the algebra quotient by its image, since that image need not be an ideal. The faithfully-flat-universally-injective node applies to this A-module cokernel; its injectivity gives a lift in the original section ring. Thus no descent of a chosen lift is asserted, only descent of membership in the image.

Step 4 uses exactly the affine-algebra-direct-image statement: the projection for any A-algebra R is affine, its quasi-coherent right adjoint preserves algebra surjections, and its global-section ring isomorphisms are natural and preserve powers. The fibre-product node gives the algebraic stack on which to apply it. Arbitrary algebras on that stack are allowed. Neither a flatness assumption on A to R nor descent of those algebras is being smuggled into this step.

Step 5 uses only the explicit restriction, local presentation, and locally-surjective conventions of `def-sfb-stack-quasi-coherent-algebra`, followed by the definition of adequate affineness. A cover of an object lying over V stays over V by composition, so local lifts and free presentations restrict. An initial draft incorrectly tried to read smooth-implies-flat from the smoothness definition. I removed that inference: the elementary restriction argument needs no flatness, and it is written out. The affine opens of each smooth test form an etale cover; the previous step gives the demanded power lifts there, with potentially different positive exponents, exactly as the definition permits.

Small cases: if Spec A is empty, the stack over it is empty and the zero section with exponent 1 works. Otherwise a finite jointly surjective family is nonempty and its exponent product is positive. The empty source, zero target algebra, zero section, and identity surjections all behave as required. No cancellation of powers, characteristic restriction, finite-generation condition, or isomorphism A to global functions is used. The converse proof even establishes global lifting for arbitrary algebras on every affine base change, so it covers all smooth tests in the stated definition.

The off-unit inputs are generic finite etale refinement and module descent tools; their uses are declared in split_report.tool_uses. No accepted unit proof step is replaced by a different geometric route. No SGA source, Lean writing, compiler, Lake, repository mutation, or agent delegation was used.

## Unfinished work

None for this one-level split. The existing cited statement-only tools remain their own stage-1 items. The required dry run and delivery are the final validation steps.
