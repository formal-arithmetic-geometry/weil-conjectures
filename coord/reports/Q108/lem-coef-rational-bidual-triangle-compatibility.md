# Stage-1 repair: lem-coef-rational-bidual-triangle-compatibility

## Files written

- `dag/nodes/sec-six-functors/lem-coef-rational-bidual-triangle-compatibility.json`: existing item, unchanged statement, thirteen replacement proof steps, explicit signed normalization, updated dependencies and declared generic tool uses.
- `citations.json`: 43 verbatim cited statements, one entry for every use in every numbered proof step. Full statements are retained so the scope and hypotheses of each quotation are visible.
- `searches.jsonl`: five actual additional Mathlib searches, whose results were read and recorded in the item. Earlier inherited search records remain in the node.
- No new nodes or Mathlib leaves. No unit or chapter files changed.

## Attachments

None. The exact blueprint tag has no hit under the read-only slopmaster2 `WeilConjectures/`; the concept searches find general dualizable-object biduality and the geometric Verdier duality interfaces, not this unbounded arbitrary-ringed-site coefficient theorem with slice restriction and raw scalar localization. Upstream master is reference material only.

## WANTED

None. All construction sources are present locally.

## Problems found and corrections

This repairs the returned delivery, rather than merely rebasing it. Comparing the retained item with current shared state showed only the prior split fields differ: current main still has the unchanged statement and empty proof. I retained the statement, ancestry, original search entries, and useful evaluation/localization route. The old report is appended below as a superseded historical report; its claims about shift coherence and R-linearity are replaced by this review.

1. Return (1), E5/C3/C4: the existential shift-comparison node cannot fix a chain sign. It is removed. The existing `lem-sf-double-hom-cone-comparison` states the natural maps s, their component signs, and chi = -s_(T(E),-1) T(s_(E,1))^(-1). Step 6 fixes precisely this normalization. Step 7 computes p+t+p(t+1) = (p+1)t modulo 2. The leading minus is essential, even for a one-dimensional degree-zero complex over a field of characteristic different from two. No new statement-only lemma replaces the item's shift clause.
2. Return (2), C4: the same cone lemma is natural in the source complex and supplies both cone-arrow identities with chi. Step 6 therefore proves exactness with the very comparison used in the shift calculation. It does not identify an arbitrary existential e with the comparison used by the generic exactness node. Step 1 checks descent through quasi-isomorphisms twice; naturality of chi then also holds for derived morphisms. Steps 8 and 13 apply the triangle-morphism and two-out-of-three lemmas only after these hypotheses are established.
3. Return (3), E5: Steps 9–10 compute the slice Hom comparison on each object V -> U, show that restricted I is K-injective using the exact j_! adjunction, and check restriction of s, its inverse, and the leading minus in chi. Step 10 includes an explicit target-resolution comparison and the entire connecting-arrow equality with beta. The word 'transports' is no longer standing in for this argument.
4. Return (4): Step 11 proves R-linearity of F from componentwise O-linearity, on homotopy classes and derived fractions. The proof now calls d a natural transformation between R-linear functors. Step 12 checks tensor balancing, naturality on f tensor a, and exactness on all localized triangles using their description as triangles isomorphic to localized original ones. `split_report.tool_uses` now actually declares the twelve generic off-unit tools used, with the purpose of each. The incorrect attribution of a sign calculation to Tag 08JA is removed; signs come from the Hom differential in 0A8X and the explicit cone lemma.

There is no statement dispute: the source's signed comparison is now explicitly normalized in the proof, and the statement and its hypotheses remain byte-for-byte unchanged. In particular, the proof requires neither perfectness nor bidual invertibility. The ancestor's final site-perfect paragraph motivates this tool but is not being used to assume arbitrary objects are perfect.

## Review by Q108

I read the source Hom differential in sites-cohomology.tex, section-hom-complexes (0A8X), the chain currying construction (0A90), RHom well-definedness (0A95), Hom from K-flat into K-injective (0A96), internal-Hom construction and adjunction (08J9), restriction (08JB and lemma-restrict-K-injective-to-open, 08FI), triangulatedness (08JC), dual/evaluation constructions (08JD and 0A97), and the cone definition (014E) in derived.tex. I read the ancestor `lem-coef-rational-retract-evaluation.md`, the actual unit and chapter records, and the full statement and proof of the existing signed-double-Hom cone lemma. The ancestor has no blueprint_update. The chapter and unit remain fixed; no SGA source is used. The proof is explicitly agent-written: Stacks 08JC omits its cone signs, so its reference alone cannot fill the gap.

For Step 1, the resolution theorem supplies I under exactly the small-site hypothesis of the item. The derived-Hom definition allows arbitrary source complexes with K-injective target, and 0A95 applies with target map 1_I for both inversions. Thus no K-flatness of E or T(E) is assumed.

For Step 2, I opened each of `lem-pc-kflat-resolution`, `lem-pur-hom-kflat-into-kinjective`, `lem-weil-pbc-site-derived-tensor-descent`, `lem-weil-pbc-kinjective-hom-derived`, `lem-pur-hom-complex-global-homotopy`, and `lem-sc-derived-hom-tensor-total`. They respectively give flat-term models, K-injectivity of T(P_V), the actual tensor comparison and descent, morphism computation, Hom-cohomology/homotopy identification, and chain currying. The component formula and its differential are written explicitly using the Hom and tensor definitions; a general adjunction is not inferred from a definition node alone.

Step 3 constructs b and checks its differential and naturality directly. The only theorem taken from `lem-sfb-ringed-site-duality-maps` is the defining natural evaluation-transpose d. Its ordinary-O representative formula has additional quasi-isomorphism hypotheses; these are deliberately not assumed. Steps 4–5 instead identify b with d on K-flat models using r:L -> T(P), the Hom/tensor comparison, and then 0A95 and naturality. I checked both variances: T(r) goes from T^2(P) to T(L), exactly the comparison needed for the transpose. The resolution P -> E then yields the result for arbitrary E.

Step 6 uses the *statement* of `lem-sf-double-hom-cone-comparison`, not a sign inferred from its proof: it states the natural s, chi including the leading minus, theta, and both cone-arrow equalities. I checked the last cone arrow against `def-weil-abstract-derived-category`: it is -pi. The definition of distinguished triangles and Step 1 consequently establish exactness with this very psi. Step 7 uses the same component formula and b, explicitly checking the exponent; all integer shifts follow by iteration and inverses. This also resolves the missing naturality in V.

For Step 8, `lem-weil-pbc-commshift-nattrans-triangle-morphism` requires natural shift isomorphisms and the compatibility equation. Both were proved, and its displayed final-square equation is also written in the step, so no exactness or sign hypothesis is silently added.

Step 9 uses the slice definition's relocalization and sectionwise restriction, the Hom definition's families of local module maps and sectionwise products, the exact j_! left adjoint from `lem-pur-site-restriction-module-adjunction-exact`, and the definition of K-injectivity. The short Hom_K adjunction argument proves preservation of K-injectivity here; it is not borrowed from a ringed-space-only node. This pins down the canonical derived restriction comparison of `lem-weil-pbc-ringed-internal-hom-exact-restriction` on actual models. Step 10 checks its compatibility with s/chi using their formulas, with d using the restriction clause of the duality-map node, and with a change of K-injective target using the written t f evaluation equality and 0A95. The full beta connecting-square calculation is present, so the slice claim is more than preservation of a diagram's vertices.

For Step 11, I checked centrality is used precisely to move the R-scalar through the O-linear Hom maps. The same component calculation gives additivity, and the common-denominator formula for localized derived morphisms gives R-linearity of F. No assertion 'd is R-linear' remains. Step 12 uses the exact Hom-module tensor construction in `def-weil-linear-scalar-localization`; R-linearity makes the formula well-defined. The triangulated localization node says every distinguished triangle is isomorphic to the image of an original one. Thus the argument covers fractions in arbitrary localized triangles, not only arrows f tensor 1. The assumptions that T is full, triangulated, duality-preserved, and has R-linear shifts are used exactly here. Step 13 applies `lem-sf-triangle-two-out-of-three` only with the exact functors and the established shift equation, both before and after localization.

I checked zero complexes, the identity and zero-arrow cone triangles, negative degrees, characteristic two, a field in characteristic different from two, and a nonreflexive infinite-dimensional vector space: the proof constructs its double-dual map but never declares it invertible. For the sign identity I also evaluated all integer degree pairs from -4 to 4; the difference is always 2p. Slice U and its further slice V use exactly the same component formula. Scalar cases s=1, s=0 (the zero localization), and s nilpotent require no cancellation or non-zero-divisor assumption. No new statements need separate small-case tests.

I checked delivery-errors B1–B10: there are no new nodes, all symbols are introduced, existing definition nodes supply the notions, TeX is single-escaped, sources use tags and labels, and every additional search is logged as executed. C1–C8: every non-elementary input is a cited statement read above, citations are verbatim, the current DAG/whole-blueprint search found no exact attachment or duplicate item, and off-unit tools are declared. D1–D5: the thirteen steps carry the evaluation identification, exponent and connecting-square arguments, with no new lemma restating a clause and no circular dependency. E1–E7: source/target variance, exactness hypotheses, model hypotheses, signs, slice normalization and scalar fractions were checked as just described. Every step is below 2000 characters; the earlier omitted subclaims are now explicit calculations from cited model theorems, and the substantial cone calculation is supplied by an existing separate node.

## What remains

Only the required repaired dry run and push. The first dry run of the retained version passed mechanically at db81d3993a; that did not address the mathematical return and is not evidence for this repair. The repaired version must obtain its own successful receipt before delivery.

## Superseded retained report

The following is the original delivery report, kept for continuity. Its mathematical claims about the existential shift comparison, restriction and scalar linearity were rejected and are superseded by the repair and review above.

# Stage-1 report: lem-coef-rational-bidual-triangle-compatibility

## Files written

- `dag/nodes/sec-six-functors/lem-coef-rational-bidual-triangle-compatibility.json` — existing item, statement retained, seven proof steps added, dependencies and split metadata completed; no new nodes.
- `citations.json` — 20 verbatim node-statement citations, one for every use in every proof step.

## Attachments

None. No sorry-free declaration in `WeilConjectures/` states this item exactly.

## WANTED

None.

## Problems found and corrections

The imported item had an empty proof, omitted the internal-Hom shift-comparison and triangle two-out-of-three dependencies, and did not spell out how the evaluation map gives the connecting-map square or how the construction descends through scalar localization. I retained the exact ringed-site, central-action, subcategory, and localization hypotheses and supplied those arguments. The generic shift-compatible triangle-morphism lemma and the triangle two-out-of-three lemma are cross-unit tools: the current unit has no replacement for these categorical facts, so they are reported for maintainer tool-use review. No statement dispute or source error was found.

## Review by Q108

I read the item statement, its source references in `literature/stacks-project/sites-cohomology.tex` (Tags 08JC, 0A97, 08JB), the scalar-localization paragraph of `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-rational-retract-evaluation.md`, and every cited DAG node. Step 1 uses the definitions of the derived category, module-sheaf category, internal derived Hom, and triangulated category, together with `lem-weil-pbc-ringed-internal-hom-exact-restriction` (RHom sends triangles to triangles and has signed shift comparisons) and `lem-pur-derived-internal-hom-shift-comparison` (the canonical two-variable shift isomorphisms); these statements supply exactly the exact endofunctor and shift data claimed. Step 2 uses `lem-sfb-ringed-site-duality-maps`, which states the evaluation-transpose map, its naturality, and its explicit representative formula; central scalar naturality gives the asserted R-linearity. Step 3 uses the same explicit formula and the shift-comparison node; I checked the two specializations and the Koszul sign, including the degree-zero and zero-complex cases. Step 4 uses exactness from the internal-Hom node and `lem-weil-pbc-commshift-nattrans-triangle-morphism`; the cited statement explicitly supplies all three squares, including the shifted connecting square. Step 5 uses `def-pur-localized-ringed-site`, the duality-map node's restriction clause, and the internal-Hom restriction comparison; I checked that each vertex, arrow, and comparison is the slice object/map. Step 6 uses the scalar-localization definition and its triangulated-exactness lemma, together with naturality of the evaluation map, to extend F and d on localized Hom modules. Step 7 uses `lem-sf-triangle-two-out-of-three` for the three possible pairs and the localization/exactness nodes for shifts and distinguished triangles. All hypotheses (small site, commutative ring sheaf, central R-action, R-linear shifts, duality preservation of the full subcategory) are checked where used. I checked small cases (zero object, identity triangle, a shifted object, and a triangle with one zero vertex); no arbitrary bidual invertibility was introduced. The proof dependencies equal the union of step uses, and all citation quotes are copied verbatim from the cited statements.

## What remains

Nothing remains for the stage-1 split; the required dry run is the next step.
