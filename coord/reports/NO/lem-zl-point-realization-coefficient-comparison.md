# Stage-1 delivery: lem-zl-point-realization-coefficient-comparison

Group NO; 2026-10-18. Direct delivery with the worker's own review.

## Files written

- `dag/nodes/sec-zeta-weil/lem-zl-point-realization-coefficient-comparison.json`: imported statement retained and split into four proof steps; no new node and no new Mathlib leaf.
- `citations.json`: verbatim statement citations for every node used by every step.
- `searches.jsonl`: actual msearch commands and returned results.

## Attachments

None. I searched both read-only Lean source trees for the exact item id, the blueprint tag, and the point-realization/coefficient-comparison terminology. No sorry-free project declaration states this item exactly.

## WANTED

None. The blueprint, Bhatt--Scholze source named by the reused realization node, and all cited DAG statements are available locally.

## Corrections and scope

The imported statement is unchanged. No new child node was created: the point-fibre equivalence, rational condensed realization, derived scalar extension, and finite-matrix realization are existing DAG statements, while the remaining work is the item's explicit comparison calculation. The route remains the first-sentence point-comparison obligation in `sk-thm-rationality`; no SGA source is used and no off-unit tool use is declared.

The item itself is not a Mathlib theorem. The four required searches were run for the item: LeanFinder (two phrasings), Loogle, Mathlib grep, and LeanSearch. They returned only generic condensed or scalar-extension declarations and no theorem comparing the specified adic point realization with the finite-matrix condensed realization; the results are retained in `searches.jsonl` and reflected in `mathlib_searches`.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs. The existing `lem-zl-condensed-point-supertrace` defines the finite-matrix functor and its basis/quasi-isomorphism properties; it does not identify that functor with `T^s_{E,\\Omega}\\circ J_s\\circ Q`. The existing `lem-weil-pbc-condensed-e-realization` gives the coefficient realization equivalence but does not state the pointwise finite-matrix comparison. Thus the item is not a restatement of either node.

## Review by NO

I read the complete item, the `sk-thm-rationality` unit, the `sec-zeta-weil` chapter, the current main-20261015 blueprint proof, and delivery-errors.md sections B--E. I read the complete statements of `lem-weil-point-fibre-equivalence`, `lem-weil-pbc-condensed-e-realization`, `def-sfb-derived-extend-to-qlbar`, and `lem-zl-condensed-point-supertrace`; every quote in `citations.json` is copied verbatim from those statements.

Step 1 uses the point-fibre equivalence exactly for the rational (E)-coefficient category: it supplies a bounded finite-dimensional (E)-complex and a quasi-inverse point representative, with shifts and triangles preserved. Step 2 uses the stated derived-extension description of (J_s), the definition of (T^s_{E,\\Omega}) as derived tensor along (E_s^c\to U_s), and the existing finite-matrix definition of (\\rho_{E,s}). On a finite free representative, the tensor is computed termwise and sends each matrix entry through (E\to\\Omega), giving the displayed comparison. Step 3 checks basis changes by the identity (D(D^{-1}AB)=AB), and checks independence of representatives using the stated facts that (\\rho) sends quasi-isomorphisms to isomorphisms and (J_s) is an equivalence. This supplies naturality on derived morphisms and removes all basis choices. Step 4 checks shifts by the identical shifted matrix complex and checks the unit (E_s[0]) by the ordinary tensor-unit map; the existing rho statement supplies (\\rho(E[0])=U_s).

I checked the edge cases (C=0), (C=E[0]), a one-term complex in an arbitrary degree, and a two-term contractible complex. In each case the comparison is the expected zero, unit, shifted, or contractible matrix object. I also checked that the argument uses the adic object (N) as the input to (J_s), while (\\operatorname{Fib}_sN) appears only on the finite-matrix side, matching the item's final clarification. No hypothesis was added or dropped.

No Lean was written and no compiler, Lake, build, or local DAG-check tool was run.

## Unfinished work

No unfinished work remains for this one-level split. The reused point-realization and condensed-functor nodes remain separate DAG items for their own future stage-1 work.

