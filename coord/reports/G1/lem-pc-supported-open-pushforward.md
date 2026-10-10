1. Files written:

   - `dag/nodes/sec-picard-framework/lem-pc-supported-open-pushforward.json`: repaired item with three direct Stacks proof steps and no relabelling children.
   - `citations.json`: verbatim quotations from the existing restriction, extension-by-zero, and perfect-complex statements.

2. Attachments: none.

3. WANTED: none.

4. What was wrong in the node or blueprint: the previous two children merely restated the item's own 08DP and 08DF clauses. I removed both and replaced the steps with the actual arguments requested by the return: use Tag 08FE (the existing `lem-pc-restrict-derived-direct-image-open` node) on the cover U and V=X minus T, use the cone criterion to glue the local isomorphisms, use exact extension by zero from `lem-sc-derived-open-restriction-adjunction-exact`, and use the open-cover definition of perfectness. The item statement and blueprint metadata are unchanged; the erroneous `created.item` metadata was corrected.

5. What I could not finish: nothing.

## Review by G1

I read the item's source in `literature/stacks-project/cohomology.tex`, Tags 08DP and 08DF, and checked the cited DAG statements themselves. Step 1 spells out 08DF(1): with V=X minus T and W=U intersection V, the existing 08FE statement gives the restriction of Rj_* to V as the pushforward from W, which is zero from the support hypothesis; on U it identifies Rj_* with the original restriction, and the cone argument makes the unit an isomorphism globally. Step 2 checks 08DF(2) using the existing statement that j_! is exact and left adjoint to restriction, so extension by zero restricts to zero on V and to F on U; the same 08FE calculation and cone argument give the global isomorphism. Step 3 checks 08DP directly from the definition of a perfect complex: Rj_*F is F on U and zero on V, hence locally perfect, and j(T)=T is closed because T is closed in X. I verified every hypothesis (open inclusion, T closed and contained in U, and support vanishing) at the step where it is used. I removed both prior child nodes after confirming they duplicated the item's clauses and updated citations to quote only statements that the cited nodes actually contain.
The use of `lem-pc-restrict-derived-direct-image-open` is declared in `split_report.tool_uses` as the generic Tag 08FE tool required by the cover argument; no node in this unit supplies that compatibility statement.

## Second reading by G1

- Item statement: checked against Stacks `cohomology.tex`, Tags 08DF and 08DP; hypotheses (open inclusion, closed support contained in the open, and supported cohomology) agree, including the specialization `j(T)=T`.
- Step 1: checked against Tag 08DF(1) and the statement of `lem-pc-restrict-derived-direct-image-open`; the cover restrictions and cone argument use exactly the cited compatibility and support vanishing.
- Step 2: checked against Tag 08DF(2); the original abstract-adjunction citation did not state the restriction formulas for derived `j_!`, so I added and cited the definition node `def-pc-derived-open-extension-by-zero`.
- Step 3: checked against Tag 08DP and `def-pc-perfect-complex`; perfectness is local on the cover and the zero complex is the required second restriction.
- New node `def-pc-derived-open-extension-by-zero`: statement-only, self-contained, definitions cited, source label is Tag 08DF proof of part (2), and Mathlib searches were run; tested on the empty open and on a one-point ringed space.

Changes: added the derived extension-by-zero definition node and its citation, updated Step 2 and `proof_deps` to use it, and recorded the repair because the prior cited node supplied only an abstract adjunction.

## Not duplicates

- `def-pc-derived-open-extension-by-zero` vs `lem-pc-supported-open-pushforward`: the new node defines the derived extension-by-zero functor and its restrictions for an arbitrary open inclusion; the item proves two supported-complex isomorphisms and perfectness under a closed-support hypothesis.
