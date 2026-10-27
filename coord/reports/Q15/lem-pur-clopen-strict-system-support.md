Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-clopen-strict-system-support.json`: item split, no new nodes, no Mathlib leaves.
- `citations.json`: verbatim statements for every cited node in every proof step.

Attachments: none. No existing sorry-free declaration states the item exactly.

WANTED: none.

The item statement and its statement dependencies were retained unchanged. The imported proof had only the strict-system clopen decomposition and the compact-support compositor implicit in an earlier report; this split makes those arguments explicit. It does not create a node for a clause of the item. The empty-index and empty-component cases are included in the assembly argument.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by Q15

I read the item source and route in `literature/blueprint/main-20261015` and the prior Q121 report, then checked the source statements of every cited DAG node. Step 1 uses `lem-weil-pbc-etale-sheaf-clopen-product` only for the finite clopen equivalence of abelian étale sheaves; I wrote out separately how scalar actions and linear maps are transported. Step 2 uses `lem-pur-coefficient-system-derived-comparison` for the definition and levelwise exactness of strict systems, and verifies that transition maps and their compatibility equations are componentwise. Step 3 is the elementary product-category Hom calculation, including the zero object and the empty cover.

Step 4 cites `lem-sf-exact-functor-derived-triangulated`, `lem-weil-pbc-localization-universal-property`, and `lem-pur-coefficient-system-derived-comparison`; their statements give termwise exact derived functors, descent of natural transformations through localization, and exact evaluation, respectively. I checked that the finite reconstruction and both adjunctions are descended from actual complex maps, with finite sums/products and all units and counits retained. Step 5 cites the ordinary extension-by-zero adjunction, composite adjunction, unit-normalized left-adjoint uniqueness, the existing compositor, and module extension exactness. Their statements provide exactly the adjunctions, unit formula, uniqueness, and exactness used. I checked the hypotheses on the localized étale module categories and that `a`, `j_i`, and `a∘j_i` are open immersions.

Step 6 reads the explicit presheaf and sheafification definitions and checks a generator section in each factorization summand. The quotient map $A_{n+1}\to A_n$ is used only by restriction of scalars, so no flatness is assumed; both compositor orders send the same generator to the same summand and send complementary summands to zero. Step 7 uses the exact-system comparison and the actual derived direct image from `lem-pur-etale-coefficient-system-adjoint`; it applies the natural isomorphism before localization and then evaluates it using the cited evaluation comparison. I checked that the argument acts on morphisms, handles empty components, and never assumes that $Y$ is separated. All seven steps cite the source documents and places recorded in the node, and every `uses` entry has a verbatim statement quote in `citations.json`.

Mathlib searches were rerun for the item on 2026-10-22 with LeanSearch, LeanFinder, Loogle, and Mathlib grep. The hits were generic clopen topology, Zariski module restriction, free presheaves, and inverse-limit transition identities; none states strict varying-coefficient étale systems or the compact-support compositor. No Lean was written or compiled.

What I could not finish: nothing within stage 1; the item is split and ready for review.
