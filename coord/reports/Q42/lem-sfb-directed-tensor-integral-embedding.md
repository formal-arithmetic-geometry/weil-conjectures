# Q42: lem-sfb-directed-tensor-integral-embedding

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-directed-tensor-integral-embedding.json: statement, split into five proof steps; no exact Mathlib match.
- citations.json: six exact statement quotations covering all step citations.
- searches.jsonl: searches recorded by the required msearch command.
- report.md: this report.

No new nodes; no new Mathlib leaves. The item statement, source, statement dependencies, inherited blueprint provenance, and prior searches are retained.

## Attachments

None. Searches of lean/WeilConjectures/ by the exact item tag, directed tensor integrality, integral image, and stagewise injectivity found no declaration giving the whole assertion. DirectedColimitBaseChangeElementwise.lean and IntegralElementsColimitDescent.lean give related but different results. FilteredColimitAlgebrasTensorElementwise.lean gives the existing node used below, not this item. No sorry declaration is treated as a completed proof.

## WANTED

None. All sources needed are present locally.

## What was wrong or incomplete

The statement is correct and unchanged. The item had no proof: Stacks Tag 0CBF calls compatibility with filtered colimits straightforward without supplying the elementwise argument. I expanded that argument, rather than citing 0CBF as if it already stated this more general tensor-map claim. No statement dispute or departure from the unit route is needed. The stored unit record points to the older six-functors chapter; I read it and the current main-20261015 chapter/unit proof and preserved the inherited chapter and unit fields. The current proof's paragraph (3) is the open-direct-image ancestor of this algebra input.

The blueprint ancestor command returns None, consistent with the item's inherited null from.node. Searches of the whole blueprint for tensor colimit, integral closure, and injective tensor found no equivalent statement: the integral-closure hits concern normalization or weakly etale normality. The generic algebra input already has an exact existing DAG node, so I created none. No definitions or statement clauses were repackaged as new nodes.

## Mathlib and DAG research

I read the prior searches in the live item and retained them. Fresh msearch calls used LeanFinder twice, Loogle, LeanSearch, and grep; their exact query strings and returned records are appended to mathlib_searches. LeanSearch was available for this run. Hits included TensorProduct.directLimitLeft_rTensor_of and Module.DirectLimit.lift_injective (direct-limit components), TensorProduct.toIntegralClosure_injective_of_flat (a specific integral-closure map under flatness), and Algebra.IsIntegral.tensorProduct (an integral-algebra base-change statement). I read Smooth/IntegralClosure.lean:35-56 and IntegralClosure/Algebra/Basic.lean:241-255 to check the latter candidates. Their hypotheses and maps do not give the item by a one-line specialization. Other semantic hits impose localization, completion or faithfully-flat hypotheses. Loogle and the targeted colimit/integrality grep had no exact match.

I searched DAG statements and titles for tensor/colimit, eventual zero, direct limits, and integrality transport, and inspected the existing nodes for underlying-module colimits, tensor-colimit elementwise descriptions, directed tails, and algebra tensor ring maps. The precise reusable result is lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise. Its statement covers both representation and eventual zero, for arbitrary module coefficients over the fixed base R, and states the ring-homomorphism clause when those coefficients are algebras. The initial-stage-base version and the cofinal-tail variant needlessly change the base and are not used.

## Not duplicates

No new nodes, so there are no new/existing node pairs requiring a same-tag distinction. All general tensor-colimit facts are reused through the existing node.

## Review by Q42

I read the full proof of Stacks Tag 0CBF (algebra.tex, lemma-integral-closure-commutes-colim-smooth), and the statements and surrounding proofs of 00D6 (lemma-directed-colimit), 00D7 (lemma-zero-directed-limit), 00DD (lemma-tensor-products-commute-with-limits), 00GI (definition-integral-ring-map), 00GO (lemma-integral-closure-is-ring), and 00GP (definition-integral-closure). I checked the tags against tags/tags. There are no new-node sources to review. Since 0CBF omits the details, proof_origin is agent, with the exact literature places recorded.

Step 1 uses def-weil-pbc-module-tensor-product: its statement gives the universal property, generation by pure tensors and compatibility with composition. I checked these words in the node itself. The step explicitly calculates multiplicativity, units, scalar maps and both naturality identities on pure tensors and extends by bilinearity. No unstated tensor functoriality lemma is hidden here.

Step 2 uses def-weil-pbc-category-colimit for the filtered-category condition and cocone universal property, and lem-weil-pbc-filtered-colimit-algebras-tensor-elementwise for representatives, eventual zero and ring maps. I opened both nodes and checked that their statements say precisely this. A nonempty directed preorder is filtered because parallel arrows coincide; all carriers and the index are in the common universe stipulated by the item. The diagram is of commutative R-algebras and both C and B are R-modules, so both applications have exactly the required hypotheses. The unique isomorphism from the specified colimit to a chosen colimit transports coprojections, hence representatives and zero, directly from the defining universal property.

Step 3 cites that same elementwise node for the two clauses it uses. Its kernel argument is written out: represent x, kill f_i(x_i) at a later stage, use injectivity of f_j there, and map the resulting zero back to the colimit. It never infers that an individual coprojection is injective. The previously established pure-tensor naturality is exactly the equality required at the later stage.

Step 4 uses def-weil-pbc-integral-closure for the monic-equation definition of integrality. I checked the statement, including the positive-degree convention. Applying d_i to the displayed finite equation gives the displayed monic equation with coefficients a_i(r_k); the coefficient and evaluation transport is explicit. This is elementary ring algebra, not an uncited integrality theorem. Representatives were already supplied in step 2, and the ring-map property needed here is stated there by the cited existing node.

Step 5 uses def-weil-pbc-integral-closure for the fact that the integral elements form a subring containing the scalar image. That clause is actually in its statement, not merely in its source proof. Restricting the codomain therefore preserves addition, multiplication, unit and the S-algebra structure. Injectivity follows by composing with the inclusion and using step 3; the pure-tensor formula is the definition of q.

I tested the constant singleton diagram, a zero-ring stage or zero colimit, and diagrams whose transition maps kill elements. The kernel proof remains valid because eventual zero, rather than injectivity of transitions, is used. For a noninjective v itself, R=Z, C=Z, B=F_2 and a constant diagram S_i=F_2 gives identity stage tensor maps and satisfies the conclusion. Thus the proof does not silently require v injective. No nontriviality, flatness, reducedness or finiteness hypothesis is introduced. All proof steps are below 2000 characters (the total proof text is below 3000), and the only non-elementary input is the existing tensor-colimit node. Its use is declared in split_report.tool_uses as a generic algebra tool, not a replacement of any geometric unit step.

I checked delivery-errors B through E: no new nodes or hollow definitions, no fabricated searches, every cited statement opened and quoted verbatim, no proof-of-node citation, no statement-clause relabelling, all compatibility calculations explicit, and no added hypotheses. citations.json was checked locally for exact substring agreement with every cited statement. Repository and launcher files remain read-only; no Lean or compiler tools were invoked.

## Unfinished work

None in the mathematical split. Required remote dry run and direct push are the remaining delivery operations.
