# Q34: lem-coef-dgcat-formal-cone-enlargement

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dgcat-formal-cone-enlargement.json`: split statement, zero new nodes, zero Mathlib leaves.
- `citations.json`: one verbatim citation for the only non-elementary dependency.

## Attachments

None. I searched the project source and the upstream reference tree for the blueprint id, strict dg Yoneda, dg module cone constructions, and likely declaration names. No sorry-free project declaration states this item.

## WANTED

WANTED: Gonçalo Tabuada, *Théorie homotopique des DG-catégories*, arXiv:0710.4303, Chapter 1, section 1.2, Definition 1.4 and Proposition 1.7, printed pp. 26–27, for the strict dg-module Yoneda and cone-matrix construction. The PDF is not archived in `literature/`; I did not download or modify literature files.

## Not duplicates

No new node was created. The existing `lem-coef-dgcat-free-cell-calculus` node supplies only the dg-category conventions and free-arrow calculus; it does not state the representable-module Yoneda isomorphism or the labelled cone category with its shifted matrix Hom complexes. The existing derived/enriched Yoneda and dg quotient nodes concern localized or derived constructions and do not state this strict arbitrary-ring construction.

## What was checked

The imported statement has no Lean declaration in either read-only source tree and remains mathematically meaningful for the empty dg category, the zero ring, and a one-object dg category. Its only statement dependency is `lem-coef-dgcat-free-cell-calculus`, which supplies the cochain grading and signed Leibniz convention. No Mathlib declaration gives the full strict dg-module/cone construction, so no child node is a Mathlib leaf.

## Review by Q34

I read the current item node, `lem-coef-dgcat-free-cell-calculus`, the sec-six-functors chapter record, the ancestor blueprint route, and the source locations in Tabuada Chapter 1, section 1.2. I also searched the whole DAG and blueprint for strict dg Yoneda, formal cone, dg modules, twisted complexes, and matrix cone constructions. The parent node is genuinely smaller and is cited only for the ambient dg-category conventions; its statement says exactly the cochain Hom complexes, associative composition, signed Leibniz rule, and preservation by dg functors used in step 1.

Step 1 checks directly that graded module maps with differential `∂q=d_Nq-(-1)^n q d_M` form a dg category. The module action and Leibniz identities give `∂²=0` and the composition rule, with the cited free-cell statement providing the ambient convention.

Step 2 is the strict Yoneda calculation. A map out of `h_x` is determined by the image of `1_x`; right-linearity gives `q_z(a)=m a`, and evaluation at `1_x` sends the map differential to `d_M(m)`. This proves the complex isomorphism and its compatibility with composition.

Step 3 verifies that the shifted direct sum defining `C_u` is a right dg module and that `D_u²=0` because `u` is closed. The labels form a small set, and the Yoneda calculation makes the representable subcategory a fully faithful dg embedding.

Step 4 expands homogeneous maps between the two summands into four shifted components. The displayed degrees, matrix differential, cone formula for maps from `h_z`, and the graded inclusion/projection identities follow by direct shift bookkeeping and multiplication. No derived or homotopy assertion is used.

Step 5 applies a dg functor entrywise to actions, labels, and matrix components. It preserves module-linearity, differentials, units, and composition, and the construction is compatible with composition of dg functors.

I checked delivery-errors B–E: the item is self-contained, has no hollow definition, uses one existing node whose statement supplies the cited fact, has no duplicate child nodes, and has no hidden flatness, boundedness, or nonempty-category hypothesis. The zero ring and empty-category cases are vacuous or direct, and the one-object identity-arrow case gives the usual two-term cone. Every non-elementary citation appears in `citations.json` as a verbatim substring of the cited node statement. No source error or statement dispute was found.

## Unfinished work

None. The required dry run is the final check; no Lean, compiler, Lake, or build command was run.

## Second reading by Q34

- Source and item statement: read Tabuada, *Théorie homotopique des DG-catégories*, Definition 1.3–1.4 (PDF pp. 25–26) and Proposition 1.7 (PDF p. 26); the module, Yoneda, shifted cone, and matrix clauses agree hypothesis by hypothesis, including empty and one-object dg categories and the zero ring.
- Step 1: checked against `lem-coef-dgcat-free-cell-calculus` and Definition 1.3; the cited signed Leibniz convention supplies exactly the ambient dg-category identities, and the module-map differential calculation is elementary.
- Step 2: checked against Definition 1.3 and the representable calculation preceding Definition 1.4; right-linearity determines a map by its value at `1_x`, and evaluation commutes with differentials, so the elementary label is justified.
- Step 3: checked against Proposition 1.7's cone module matrix and Definition 1.4; `du=0` gives `D_u^2=0`, smallness follows from small objects and Hom sets, and the representable full embedding is the stated Yoneda calculation.
- Step 4: checked against Proposition 1.7, lines giving the shifted cone matrix and its differential; all four degree shifts, cone differential, and biproduct identities follow by componentwise bookkeeping, so the elementary label is justified.
- Step 5: checked against Definition 1.4 and Proposition 1.7; applying a dg functor to actions, labels, and entries preserves the displayed equations and composition, an elementary verification.
- New nodes: none; no additional node was needed after searching the DAG and Mathlib for strict dg-module Yoneda or a formal cone enlargement.
- Changed the `created` record to this item, group Q34, and 2026-10-17 because it incorrectly named the unrelated equivalence-cell item and group NW.
- Kept the sole citation unchanged: its quote is a verbatim statement of `lem-coef-dgcat-free-cell-calculus` and is the only non-elementary dependency.
