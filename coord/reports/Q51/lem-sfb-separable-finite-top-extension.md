# Worker report: lem-sfb-separable-finite-top-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-separable-finite-top-extension.json`: statement, split; five proof steps, no new nodes, no new Mathlib leaves. The statement and statement dependencies are unchanged.
- `citations.json`: thirteen entries, one per cited node per proof step, each quoting that node's statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's own log and was read before recording its results in the item.

## Attachments

None. I searched all `lean/WeilConjectures/` for the blueprint tag, separably-generated terminology and separability transitivity, and searched its FieldTheory files for `IsSeparableExtension`. There is no project declaration proving the item. The existing definitions in `FieldTheory/SeparableExtension.lean` and the tensor-reducedness and geometric-reducedness criterion declarations cover tools used in the proof, not the asserted tower permanence. I did not infer an attachment from their existence or from any sorry declaration.

## Wanted sources

None. All sources used are present locally; no SGA source was used.

## What needed repair

The item was statement-only, with empty proof and dependency lists. The statement is correct: its lower extension is not assumed algebraic, and algebraic transitivity alone cannot prove it. The inherited source is Stacks More on Algebra, Tag 0BRM (`lemma-abhyankar`), final paragraph, which explicitly uses that a finite separable extension of the residue field remains separable over the original residue field. Algebra Tag 030O gives the nonalgebraic definition. The proof here supplies the transitivity argument through the existing 030U and 030W nodes. It is marked agent-written because 0BRM invokes transitivity without giving this argument and the argument assembles separate Stacks results.

No statement dispute or source error was found. The finite-dimensional hypothesis on M/L remains exactly as stated, though the argument works for any separable algebraic top extension. In particular I did not add finite generation or algebraicity to L/k.

The historical blueprint ancestor is null, as `tools/blueprint_refs.py ancestor` confirms. I retained its complete creation chain and explanatory place. I read the latest `sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3), as well as the recorded chapter and unit. The latest direct-image argument does not state this supporting algebraic result. This split completes the existing historical auxiliary node without changing any chapter or unit route. The two non-Mathlib field-algebra tools are declared in `split_report.tool_uses`; the worker did not set the maintainer's `tool_uses` field.

## Searches and reuse

I searched the full DAG for separability, separably-generated extensions, tensor reducedness, and the tags 030O, 030U, 030W and 030X. The existing `lem-weil-pbc-separably-generated-tensor-reduced` states only the separably-generated case of 030U, so step 2 explicitly reduces the arbitrary separable lower extension to that case. I also read the existing tensor-field descent split as a check on available tool statements; I do not cite its proof as a theorem. All needed tools already have nodes. No new node is needed for finite tensor coefficients, the empty transcendence basis, or the explicit two inverse tensor maps: their arguments appear in the steps.

Whole-blueprint searches with `tools/blueprint_refs.py search 'separable finite'` and `... search 'separably generated'` gave, respectively, the unrelated separably-closed finite-extension/purely-inseparable statement and no match. The broader separable search did not give this tower statement. Thus `blueprint.same_as` stays empty.

The required msearch commands were run with group Q51 and this item: LeanFinder on a possibly transcendental separable extension followed by a finite separable algebraic extension; Loogle with `Algebra.IsSeparable, Algebra.IsSeparableExtension`; LeanSearch on transitivity without algebraicity of the lower extension; and grep for `IsSeparableExtension|IsSeparablyGenerated|IsSeparable.trans` in FieldTheory. I also tried a second LeanFinder phrasing in terms of geometrically reduced field extensions and a second grep covering algebraicity and transitivity. Each exact query, actual result record and verdict is retained in `mathlib_searches`; the item's inherited searches are also retained.

LeanSearch and LeanFinder suggested `Algebra.IsSeparable.trans`; I read `Mathlib/FieldTheory/SeparableDegree.lean:835` and `Separable.lean:539,549,570`. That class implies algebraicity, so the result cannot specialize to this item. The Loogle result says the identifier `Algebra.IsSeparableExtension` is unknown to Mathlib; the predicate occurs in the project instead. No service outage was reported. I read `Mathlib/RingTheory/Flat/Basic.lean:131` for the existing injective-tensor leaf and confirmed its flat-module hypothesis and the orientation of its tensor map. All Mathlib searches went through msearch; the later source reads were reads of the returned declarations.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The existing finite-separable tensor-field-reduced node is narrower in its second factor (a field). The proof instead uses the already existing separably-generated tensor-reducedness theorem with a possibly non-domain reduced algebra; no duplicate of either node was introduced.

## Review by Q51

I read Stacks `more-algebra.tex`, Tag 0BRM (`lemma-abhyankar`), through its concluding residue-field tower; `algebra.tex`, Tag 030O (`definition-separable-field-extension`), Tag 030U (`lemma-separable-extension-preserves-reducedness`, both cases and its proof), and Tag 030W (`lemma-characterize-separable-field-extensions`, statement and (4) implies (1)); and the definition of a transcendence basis in the existing 030E node. These agree with the item's hypotheses and conclusion. There are no new-node statements to audit.

Step 1 uses the exact statement of `lem-weil-pbc-char-zero-field-extension-separable` for arbitrary M/k in characteristic zero, not algebraic separability. It then restricts the remaining argument to prime characteristic. The commutative-algebra tensor universal-property node supplies the ring multiplication and structural maps for S and subsequent tensors. The characteristic dichotomy and the construction S=L tensor_k E are elementary. All field extensions in this argument have compatible maps from k.

Step 2 uses the tensor-product definition for a finite pure-tensor expression of a single element; it does not assume L is finitely generated. Its field F is generated by just those finitely many coefficients, so clause (2) of the separable-field-extension definition supplies precisely separable generation of F/k. The cited 030U node accepts an arbitrary reduced algebra, and E is reduced because it is a field. Vector-space flatness and the injective-tensor leaf apply over k to F -> L with flat factor E. The interchange of factors is the explicit elementary pure-tensor swap, not a further separability assertion. The tensor map is a ring map by its product formula. I checked that a nilpotent upstairs need not have a nilpotent lift through a general map; here injectivity gives y^n=0 from j(y)^n=0, which is why the injection is included explicitly.

Step 3 cites the actual transcendence-basis definition, the actual separable algebraic-extension definition and clause (1) of the nonalgebraic definition. The empty family's polynomial ring is L; its evaluation is the injective inclusion into M. The top extension is algebraic by the stated hypothesis, so this family is a transcendence basis, and its generated subfield is exactly L. The top separability hypothesis then supplies the remaining clause. This is a direct unpacking of the cited definitions and is the single step marked elementary. No theorem about all separable extensions being separably generated is used.

Step 4 uses 030U with base field L, extension M and the reduced L-algebra S; this is allowed even when S=L tensor_k E has zero divisors. I checked the two tensor maps on the k- and L-balancing relations and on products. Their composites are the identity on pure tensors, which generate by the cited tensor definition. Thus this is an explicit elementary identification inside the application step, not an unnamed comparison lemma. Reducedness passes along the isomorphism by applying its inverse to any nilpotent. This step uses the statement of 030U, not an internal construction from its proof.

Step 5 applies the precise positive-characteristic node `lem-weil-pbc-geometrically-reduced-extension-separable`. Its hypothesis quantifies over every field E/k; step 1 chose arbitrary E, and steps 2–4 imposed no restriction on it. The prime characteristic required by this node was isolated in step 1. Its conclusion is exactly the finitely-generated-subextension meaning requested in the item. All thirteen step/node citations were opened and copied into citations.json verbatim, and proof_deps is their union. Every non-elementary fact is a cited statement; no source tag substitutes for a node.

I checked small and boundary cases: M=L makes the top extension degree one and step 3 still has the empty basis; L=k reduces to finite separable algebraic over k; L=k(t) demonstrates that the argument permits transcendence; the zero tensor element permits an empty coefficient sum, with F=k; E=k is allowed; and no assumption that L tensor_k E is a field or a domain occurs. Over an imperfect field of characteristic p, adjoining a pth root of an element with no pth root fails the top separability hypothesis, so the proof does not assert permanence for inseparable top extensions. Characteristic zero is covered independently. Every step is shorter than 2000 characters. No Lean source, compiler, build tool, shared repository file or launcher file was written or run outside the authorized stage-1 delivery workflow.

## Unfinished work

None in the requested one-level split. The existing cited non-leaf tools remain governed by their own DAG status. Delivery validation and push are performed with the required deliver.py commands.
