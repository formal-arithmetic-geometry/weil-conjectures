# Q58: lem-pod-completed-scalar-extension-texact

1. Files written

- `dag/nodes/sec-poincare-duality/lem-pod-completed-scalar-extension-texact.json`: statement, now split; six proof steps; unchanged statement; no full Mathlib match.
- `citations.json`: verbatim statement quotations for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log; `write_split.py` is a sandbox-only preparation script.
- New nodes: 0. New Mathlib leaves: 0. The proof uses the existing Mathlib leaf `lem-weil-pbc-exact-functor-derived-factorization` rather than creating another exact-functor lemma.

2. Attachments

None for this item. Searching `lean/WeilConjectures/` for the exact blueprint tag and for scalar-extension terminology found generic constant-ring scalar-extension declarations, not this full completed integral assertion. The related existing `scalarCompletion_existsUnique` in `lean/Sheaf/Paper/IntegralOperationsScalarComparisons.lean:516` contains `sorry` at line 525 and would cover only the comparison clause anyway. It is not an attachment.

3. WANTED

None. The blueprint snapshots, Bhatt--Scholze paper, Stacks source and Mathlib declaration source used here are available locally.

4. Problems and corrections

The imported item had no proof. Its assertion does not follow merely from finite-level truncation or from the finite quotient maps being flat: those quotient maps need not be flat for ramified coefficient extension. The proof instead uses finite freeness of the completed coefficient ring sheaf and the already existing strict-tower comparison.

The statement refers to `def-weil-derived-complete-integral-detailed`, whereas `prop-weil-pbc-integral-tstructure` uses the proper-base-change category, including compatible etale-origin witnesses. I did not identify these definitions silently or drop their extra conditions. Step 1 cites the explicit equivalence of precisely those categories in the last two sentences of `lem-weil-pbc-integral-stratified-perfect-characterization`. Its noetherian, finite-dimensional, and invertibility hypotheses are all hypotheses of the item. The statement is unchanged.

The blueprint proof also makes unrelated claims about truncations being triangulated and about integral truncations being computed levelwise without the Tor-compatibility qualification. This item proves neither claim and uses neither. It supplies just the finite scalar-extension t-exactness argument extracted by its parent. No unit or chapter route is replaced.

5. Unfinished work

None for this split. All non-elementary inputs are existing DAG statements, which retain their own status and proof obligations. No new statement-only frontier is necessary.

## Not duplicates

No new nodes or same-tag pairs were created. I searched the entire DAG and imported blueprint for completed scalar extension and exact-functor machinery, read the matching completed scalar comparison, constructibility, triangulated-subcategory, and category-characterization statements, and reused them. The existing full comparison is strictly weaker than this item's conjunction, since it does not state constructible restriction or t-exactness; it is an input to the argument, not a replacement item. The generic exact-derived-functor result is already a Mathlib leaf.

## Review by Q58

I read the item's statement, the chapter and unit records, both the master blueprint text and the current main-20261015 proof of `prop-constructible-truncations`, including its integral paragraph and sentence beginning “Being characterized by the vanishing of cohomology sheaves”. I read Bhatt--Scholze Lemma 6.8.2(1), pp. 58–59, which identifies the completed coefficient sheaves. I also opened Stacks `derived.tex`, Tags 015F (`lemma-right-derived-exact-functor`) and 014X (`lemma-additive-exact-homotopy-category`), and `sites-modules.tex`, Tag 093M (`lemma-completion-flat`), to check the coefficient context and exact-functor argument. The supplied proof is marked agent-written: the blueprint's short sentence is not being passed off as a detailed literature proof. There are no new nodes for which a separate source attribution is required.

For Step 1, I read the full statements of `lem-weil-pbc-integral-stratified-perfect-characterization` and `prop-weil-pbc-integral-tstructure`. The former explicitly says its conditions describe exactly the detailed integral category over such a scheme, and the latter explicitly identifies the truncations and bounds with the ambient ones. The scheme assumptions and both finite coefficient fields satisfy their hypotheses. In particular this step does not cite a definition as evidence for a t-structure theorem or assume the extra Tor-compatibility condition needed only for levelwise truncated towers.

For Step 2, I read `lem-weil-finite-free-completed-scalar-comparison`, `def-pur-sheaf-tensor-product`, `def-weil-sheaf-of-modules-category`, and `def-pc-sheaf-restrict-scalars`. The first explicitly states that S is finite free of rank [L:E], the second defines the tensor as the associated sheaf, the third states how kernels and cokernels are computed, and the fourth says restriction leaves the underlying abelian sheaf unchanged. The written forward and inverse coordinate maps give the needed natural decomposition. Applying it to a morphism gives coordinatewise kernels and cokernels, so the exactness deduction is elementary once those cited facts are supplied. I did not use a flatness theorem from a definition of flatness, nor assume epimorphisms are sectionwise surjective.

For Step 3, I opened the full statement and Mathlib match of `lem-weil-pbc-exact-functor-derived-factorization` and read `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:36`, its factorization at line 41, its shift construction and its triangulated instance. This leaf gives termwise computation, preservation of quasi-isomorphisms, shifts, and triangles. `lem-pur-derived-change-of-rings` explicitly computes the ordinary derived change of rings on K-flat resolutions for a map of ring sheaves on one site. Here the site is small as fixed in the item, the two module categories are abelian, R and S are commutative ring sheaves, and Step 2 provides exactness. Applying exact F to a K-flat resolution is the written comparison of the two derived constructions; no injectivity or flatness of the input's cohomology is added.

For Step 4, I read the detailed integral-category definition and the full completed-scalar comparison statement. Completeness is a membership condition in the former; the latter is explicitly about the actual strict-tower functor, with the quotient tensor projections and zero shifted-product component, not only an abstract isomorphism of unrelated completion objects. Its map is natural in K, invertible for every derived-complete K, and its ordinary output is derived v-complete. These are exactly the facts used.

For Step 5, the statement of `lem-weil-integral-scalar-extension-constructible` preserves exactly the detailed integral category, for every scheme. The statement of `lem-weil-integral-constructible-triangulated` makes exactly this full subcategory triangulated with inherited ambient shifts and triangles. With Step 3 they justify restriction. I wrote the induced shift comparison as the composite through chi and explained preservation of triangles by natural isomorphism; no unexplained transport of a shift comparison is left in the argument.

For Step 6, `def-sbc-standard-tstructure-derived-category` explicitly includes the bounded-representative characterization in both directions. Applying the termwise functor to such a representative preserves its zero terms, giving both ambient bounds independently. The integral t-structure statement quoted in Step 1 identifies the constructible bounds, and Step 5 ensures target membership. This proves the desired two inequalities without a claim that truncation is itself an exact triangulated functor.

I checked the identity extension L=E, zero complex, empty scheme, arbitrary integral shifts, and a ramified extension on a geometric point with input O_E/t in degree zero. In the last case the output is O_L/t O_L in degree zero; it may have v-torsion, which confirms why no flat-cohomology hypothesis is needed. Both half-bound arguments work for all integers independently, including a=b. No positive characteristic of a global base field is used; the proof works under the item's stated scheme hypotheses. No new statements were introduced to test separately.

Against delivery-errors B–E: no new-node form or search-veracity issue; every reused assertion is read from its statement (C4), and every non-elementary input has an explicit node citation (C1). `citations.json` quotes those statements verbatim. The finite-coordinate and bounded-representative arguments are written in the item rather than promoted to unnecessary nodes. All six steps are under 2000 characters. I checked candidate dependencies for a path back to this item and found none. Off-unit coefficient/category results are declared as tool uses in `split_report`; they serve the ancestor's prescribed integral scalar-extension argument, not a replacement unit route. The original item statement, source, creation metadata and historical Mathlib searches are retained. Fresh actual command results were appended without rewriting old searches. No Lean was written and no compiler, Lake, local DAG-check script, git command, or subagent was used.
