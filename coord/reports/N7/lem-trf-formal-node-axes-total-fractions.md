## Files written

- dag/nodes/sec-trace-formula/lem-trf-formal-node-axes-total-fractions.json: statement, split; no exact Mathlib match. Five proof steps reduce the item to existing Mathlib leaves and explicit coefficient calculations.
- citations.json: one verbatim statement quotation for every step/node citation.
- searches.jsonl: actual search-command output records for this item. The item's seven inherited Q85 search records are retained; five fresh N7 searches are appended to its mathlib_searches.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves used include the power-series-domain, Laurent-series-field, and ring-localization-universal-property nodes.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, formal-node names, axes/fractions, axis/kernel, and equal-constant terminology. No declaration states every clause of this item. No sorry-containing declaration is treated as an attachment.

## WANTED

None. All sources used are available in the read-only repository.

## What was wrong or missing

The item was statement-only, without proof steps. Stacks 0C4A (curves-lemma-2-branches-delta-1), in the proof of (1) implies (2), Case I, asserts the split normalization after replacing the quadratic form by xy, and leaves its explicit algebra to the reader. This delivery supplies that algebra; the proof_origin is agent because the coefficient argument and simultaneous denominator construction are written here rather than transcribed from Stacks.

The mathematical statement is unchanged. Added only references to the existing quotient-algebra and localization definitions, and spelled out non-zero-divisor as injective multiplication. The final reference to the inclusion of P is interpreted explicitly: the resulting isomorphism embeds P into Q(R), represented by (uf,vg)/(u,v), and this agrees with its coefficientwise inclusion into the Laurent product. No global geometry, completeness, normalization theorem, or algebraic closedness hypothesis is needed.

Read the chapter and unit records for sec-trace-formula/sk-i-curve-zero and the current main-20261015 locality node. This item is a subsidiary algebra calculation in the normalization/Euler-defect descendant of that node, not a replacement for a step of the unit. The fixed chapter and unit are untouched. No repair note exists for this item and there was no previous sandbox split to reuse.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. Searches of the whole DAG and blueprint for power series, Laurent series, axis, equal constant, and tag 0C4A were read. The existing lem-weil-pbc-power-series-domain, lem-weil-pbc-laurent-series-field, and lem-weil-pbc-ring-localization-universal-property are reused. The related lem-trf-equal-constant-normalization-residue-quotient concerns integral closure and the quotient P/S, not the axis kernel or total fractions. lem-sfb-quadratic-series-integral-closure assumes a nonzero square coefficient and states a quadratic normalization, not this two-axis map. lem-sfb-nodal-local-tangent-normalization and lem-sfb-nodal-completed-normalization-model add geometric hypotheses and do not replace the calculation for every field; the latter remains unsplit. No claim is taken from a dependency's proof instead of its statement.

## Review by N7

I read Stacks curves.tex, Tag 0C4A, label lemma-2-branches-delta-1, including both forward cases and the converse, and algebra.tex Tag 00CP (proposition-universal-property-localization) and the Laurent-field paragraph of Tag 0BI0. I read every cited node's statement, including the precise coefficient conventions in the two power-series/Laurent-series definitions. The current blueprint locality statement supplies only provenance, not a false claim that it directly proves this commutative-algebra calculation. This argument expands the split-node calculation and is marked agent-written accordingly. There are no new-node sources to audit.

Step 1 uses only def-weil-pbc-multivariate-power-series: its coefficientwise operations prove that restricting to one axis is multiplicative, because a nonnegative sum of v-exponents is zero exactly when both exponents are zero. Reindexing the coefficients a_(i+1,j+1) explicitly factors every kernel element by uv. This is a direct coefficient calculation, marked elementary; no general substitution or convergence theorem is invoked.

Step 2 uses that same power-series definition and def-weil-pbc-algebra-hom-quotient. The latter explicitly gives the quotient algebra and its surjective quotient map with the specified kernel; it is not being cited for an unstated isomorphism theorem. The proof itself constructs the induced map and its inverse and checks both composites using Step 1. Equal constants are exactly what makes f(u)+g(v)-c have the requested two restrictions. This also works in characteristic two: subtraction of the common constant gives c+c-c=c, with no division by 2.

Step 3 uses def-weil-field for 1 != 0 and the power-series convention for the nonzero witnesses u and v. lem-weil-pbc-power-series-domain explicitly applies to any integral domain A and any number d of variables; here a field is a domain and d=1. Its conclusion gives cancellation separately in k[[u]] and k[[v]], exactly what the step uses. The converse uses (u,0) or (0,v), which really lie in S because both constants vanish; using (1,0) here would have been wrong, since it is not in S. Zero itself is a zero-divisor by the same witnesses. The multiplicative set contains 1 and is closed under products by the two domain conclusions. No inference from just the definition of flatness or normality is hidden.

Step 4 uses def-weil-pbc-laurent-series, which explicitly states the injective power-series inclusion; lem-weil-pbc-laurent-series-field, whose hypothesis is exactly the given field k; and lem-weil-pbc-ring-localization-universal-property, which applies to arbitrary commutative rings and any multiplicative subset mapped to units. Both components of a denominator are nonzero by Step 3, so the two field inverses give an actual inverse pair. The universal property's hypotheses are thus all checked. Injectivity is proved directly from r/t mapping to zero and j(r)=0; it is not inferred from a general localization theorem without a citation. Agreement on k follows from the extension formula.

Step 5 uses the bounded-below coefficient description in def-weil-pbc-laurent-series. A common positive N shifts both supports into degrees at least 1, including when either series is zero, so the numerator has equal constants zero and really belongs to S. This is the reason arbitrary pairs of Laurent series have a denominator in R, despite their original constants need not agreeing. The formula r_N/s^N gives every pair, and (uf,vg)/s gives every element of P compatibly. The step invokes the field cancellation already obtained in Step 4 and no independent non-elementary lemma. It stays elementary: it is a coefficient shift followed by substitution in the displayed localization formula.

Against delivery-errors B--E: no statement-only child is supplied with an illicit proof, no duplicate or restated clause is made into a node, and all notation is introduced in the item or its cited definition. Sources have tags and labels. The complete statements copied into citations.json are verbatim and give exactly the properties described above. The used-node union is exactly proof_deps, the new dependencies are existing leaves rather than descendants, so no cycle is introduced. The proof treats both zero components, nonzero constants, unequal constants in P, arbitrarily negative Laurent orders, zero Laurent series, and positive characteristic. It does not assume the nodal ring R is a domain. Each step has fewer than 2000 characters and contains no hidden standard comparison lemma. No SGA source, Lean edit, compiler, Lake, git command in the read clone, or forbidden local preflight was used.

## Unfinished work

None in the natural-language split. Delivery is subject to the required server dry run and independent maintainer review.
