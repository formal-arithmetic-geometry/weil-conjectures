## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-functorial-flat-resolution.json`: statement, split; explicit free-cover construction, with existing Mathlib leaves supplying flatness and exactness. The statement is unchanged.
- `citations.json`: a verbatim statement quotation for every node used in each proof step.
- `report.md`: this report and the author's review.

## New nodes

None. There are zero new Mathlib leaves. Existing leaves reused are `def-weil-pbc-free-module`, `lem-weil-pbc-projective-module-flat`, `lem-weil-pbc-flat-tensor-exact` and `lem-weil-pbc-tensor-right-exact`. This item itself is not a Mathlib leaf: the free-functor and module-flatness declarations require the explicit construction and the comparison of algebraic flatness with exact tensor functors written here.

## Attachments

None. The previous proposed `AddCommGrpCat.hasFunctorialFlatResolution` attachment was rejected, and is not proposed again. The current shared tree does contain `CategoryTheory/RingObjects/Ab.lean`, including an anonymous instance at lines 290–292, but the delivery does not treat that instance or a named candidate as evidence of closure. The earlier candidate metadata is retained as requested. The source place no longer asserts that the unverified named declaration supplies a finished proof.

## WANTED

None. The mathematical sources used are present. The historical worker brief refers to `coord/dag-sync.md`, which is absent in this live read clone; the explicit supplied live-repository instructions determine the paths and delivery procedure.

## Corrections and limitations

The item was an unsplit statement. No statement correction or dispute is needed. The imported source place claimed an exact project declaration; this was removed from the source place, without deleting historical candidate or search records. The proof does not depend on that claim. No Lean was written, no compiler or build was run, and no repository or launcher file was changed.

The source's Part 4 uses free abelian sheaves on represented objects. Our item is its coefficient input, so the proof explicitly constructs the ordinary free abelian group on the underlying set; it does not use the sheaf-transfer conclusion to prove its own input. The ancestor's present split step 2 uses this coefficient input before applying sheaf transfer. No route is changed and no off-unit non-leaf theorem is used as a tool.

## Searches and reuse

Read the entire item, its ancestor's relevant proof step, the chapter and unit records, and the current main-20261015 proof of `sk-prop-sfb-module-category`, Part 4. Searched project Lean by the exact blueprint tag and functorial-flat-resolution names and concepts. Searched the whole DAG's statements for free abelian groups, free/flat modules and exact tensor products, then opened every reused node's statement. Whole-blueprint searches used `tools/blueprint_refs.py search` with `functorial flat`, `free abelian group`, `projective module flat`, and `Abelian groups admit`; the search results do not provide a duplicate of this coefficient statement. The ancestry command identifies `def-sfb-module-derived-pushpull-adjunction`.

All current Mathlib searches were made with the required msearch command; queries and returned summaries are retained verbatim in `searches.jsonl` and appended to the item's existing records. Both natural-language phrasings returned `AddCommGrpCat.free`/`adj` and tensor-exactness ingredients. Loogle returned the free adjunction, and grep found no `HasFunctorialFlatResolution` predicate. Read Mathlib `Algebra/Category/Grp/Adjunctions.lean:49–87`, `RingTheory/Flat/Basic.lean:220–231,305–350`: free and adjunction exist, free modules are flat, and both tensor orientations preserve exact sequences. Mathlib's returned `AddCommGrpCat.tensorObj_eq` is the Cartesian product and is not the tensor over integers specified by this item. The item's verdict remains split.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs. Freeness, free-module flatness, exactness under flat tensor and right exactness are cited through their existing nodes rather than copied into new ones. Construction of the free cover and its functor laws are elementary finite-sum calculations in the item's proof.

## Review by NH

I read the main-20261015 module-category proof, Part 4, including its tensor-flatness argument and its canonical free-cover epimorphism, and the ancestor's current step 2. I also read Stacks `algebra.tex`, Tag 00C2 (`algebra-item-free-module`), Tag 051G (`algebra-lemma-local-artinian-characterize-flat`, the opening general observation of its proof), Tag 00HD (`algebra-lemma-flat`) and Tag 00DF (`algebra-lemma-tensor-product-exact`). The occurrence of the free/projective-flat fact in 051G is a general fact in its proof, not an application of the lemma's local-Artinian equivalence to the integers. The exact existing node states that general fact with only a commutative-ring hypothesis. The overall explicit coefficient construction is marked agent-written; it is not represented as a verbatim Stacks proof of functorial resolutions.

Step 1 uses the statement of `def-weil-pbc-free-module`: unique finite coordinates give a basis with arbitrary index set. The functions of finite support are the object itself, not data picked from an unproved existence theorem. The formula on basis elements extends by the displayed finite sum, respects addition, and verifies identity and composition. Repeated images under a noninjective homomorphism merely add coefficients. This is an elementary construction, not a hidden free-forgetful-adjunction theorem.

Step 2 uses no other theorem. Finite sums define the evaluation homomorphism, and preservation of integer multiples follows from additivity. The same formula proves naturality on every element. Each group element has its displayed basis-vector preimage; cancellation on those preimages proves the epi property directly. No equivalence between categorical epis and surjections is invoked. A natural map of underlying sets sending m to e_m need not be additive and is not claimed to split pi in abelian groups.

Step 3 uses exactly the final sentence of `lem-weil-pbc-projective-module-flat`, which says that every free module is flat. The ring is the commutative ring Z, the basis comes from step 1, and no finite-generation, projectivity construction or local-ring hypothesis is added. Every additive map is Z-linear by repeated addition and negation; this elementary observation explains the coefficient-category identification.

Step 4 reads the statements of both `lem-weil-pbc-flat-tensor-exact` and `lem-weil-pbc-tensor-right-exact`. The first supplies left and middle exactness for both tensor orientations, while the second supplies right exactness including terminal surjectivity for both orientations. I explicitly included the second node because left/middle exactness alone is insufficient to conclude preservation of a short exact sequence. The starting sequence is short exact, hence supplies both the hypotheses required by these nodes. Kernels and cokernels of abelian groups carry the same integer action, so this is the same algebraic sequence. `sk-def-sfb-sheaf-tensor` is used only for its statement that the coefficient Ab tensor is the tensor over Z; no sheaf statement is taken from its proof and no Cartesian tensor is substituted.

Step 5 uses only the sentence defining a functorial flat resolution in `lem-sfb-sheaf-functorial-flat-resolution`. It does not invoke that node's sheaf-transfer conclusion or assume a site. Its input data are precisely the constructed functor, the flatness just established, and the natural epi. Thus there is no cycle through the coefficient input.

I checked the empty basis in the freeness convention, the zero target group, torsion groups and arbitrary infinite groups. For the zero target, its underlying set has one element, so P(0) is Z and pi is the zero map onto the zero group, which is an epi; preservation of zero by P is not required. For Z/2, P has one generator for each underlying element and evaluation is still surjective, although the group being covered is not flat. Infinite groups require neither finite rank nor a cardinal enlargement: finitely supported functions on a U-small set with integer values stay in U. Noninjective maps, including the zero map, satisfy the formulas; in particular P need not be an additive functor, and the item does not ask for one. The internal Hom and tensor unit in the statement are unchanged.

No new lemma is a renamed clause of the item. All five steps have fewer than 2000 characters. I checked B1–B10 through reuse and source identification, C1/C3/C4 by opening every cited statement and recording exact quotations, and D/E through the explicit constructions, exactness endpoints and small cases above. No work remains mathematically in this one-level split; dependencies remain the existing DAG's responsibility.
