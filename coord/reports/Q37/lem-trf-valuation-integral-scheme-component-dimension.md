## Worker report

Q37, stage 1, 2026-10-23. Item: lem-trf-valuation-integral-scheme-component-dimension.

### Files written

- dag/nodes/sec-trace-formula/lem-trf-valuation-integral-scheme-component-dimension.json: existing statement, unchanged; split into eight steps using existing nodes. Not a Mathlib leaf.
- citations.json: 33 entries quoting the statements of the 25 existing proof inputs, indexed by the eight proof steps.
- report.md: this report and the author's review.

New nodes: 0. New Mathlib leaves: 0. No Lean, compiler, Lake, library build, repository write, launcher write, or direct git command was used. The write_split.py helper and searches.jsonl stay in the sandbox.

### Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for valuation-domain / valuation-ring dimension terminology. There is no project declaration stating the whole item. ValuationClosedFibreIntegral.lean:33, AlgebraicGeometry.Scheme.Modules.closed_fibre_is_integral, merely transports an assumed integral quotient fibre to the residue-field fibre under proper/flat/finite-presentation hypotheses. It does not prove this item's generic-fibre integrality or component dimensions and is not an attachment.

### Literature

WANTED: none.

Read the first proof paragraph of Stacks Tag 0GSI, more-morphisms.tex, lemma-associated-point-specializes, where the integral valuation-base scheme is treated by applying Tag 00QK. Read the full statement and proof of 00QK in algebra.tex, lemma-finite-type-domain-over-valuation-ring-dim-fibres. Its ring theorem already has a DAG node: lem-trf-valuation-domain-fibre-dimensions. Its equidimensionality conclusion, rather than only equality of the dimensions of the two affine fibres, is essential here.

For globalization, read Varieties Tag 0A21, lemma-dimension-locally-algebraic, especially (3) and (5); Schemes Tags 01I4, lemma-fibre-product-affine-schemes, 01JR, lemma-open-fibre-product, 01J2, lemma-affine-reduced, and 01J3, lemma-reduced-closed-subscheme; Algebra Tags 00DK, lemma-tensor-localization, 00FN, lemma-Noetherian-permanence, and 00OT, lemma-dimension-at-a-point-finite-type-over-field; Morphisms Tags 01T3, lemma-composition-finite-type, and 01T5, lemma-immersion-locally-finite-type; Properties Tag 01ON, lemma-characterize-integral. Verified the cited tag/label pairs in stacks-project/tags/tags, including fibre topology 01K1 and the local-dimension definition 0055. No SGA source is used.

### Changes and faults found

The imported item was statement-only, not a completed split. Its statement is correct and is retained verbatim, including dominance at the generic point, local finite type rather than finite type, arbitrary-rank valuation domains, potentially empty closed fibre, and absence of flatness and quasi-compactness hypotheses. There is no STATEMENT-DISPUTED correction.

The argument now explains why every chosen affine coordinate algebra contains A, why the generic tensor algebra is a nonzero domain, why the charts share the same generic point, and why non-quasi-compact components still have the dimension computed on a single nonempty affine intersection. Local topological dimension is not confused with the dimension of a local ring at a generic point.

The field-component construction and field-dimension formulas are generic tools recorded in split_report.tool_uses, not a change in the unit's route. No maintainer-owned tool_uses field was set. The item remains in sec-trace-formula / sk-i-curve-zero, serving lem-trf-local-term-locality through the existing nearby-cycle / alteration ancestor chain. Neither the chapter nor the unit was edited.

### Unfinished work

The item's one-level split is complete. Existing unsolved dependency nodes retain their own work; none was copied or silently restated as a new node. Delivery verification is performed with the required server dry run after this report is written.

## New nodes

None. In particular, no new node repeats the affine 00QK theorem, generic-fibre integrality clause, component-dimension clause, or local-dimension clause.

## Searches and blueprint

The item's earlier 2026-10-22 Mathlib searches and provenance are retained. Five new searches were actually executed with msearch.py and logged in searches.jsonl: LeanFinder with the whole scheme statement, LeanSearch with closed-fibre component dimensions, Loogle `ValuationRing, topologicalKrullDim`, grep `valuation.*dim|dim.*valuation|equidimensional` in AlgebraicGeometry, and a second LeanFinder phrasing for a finite type domain algebra over a valuation ring. All five services returned successfully. Loogle had zero hits; grep returned only a comment about equidimensionality in AlgebraicCycle/Basic. The semantic hits concern definitions of integral schemes, a universally closed scheme over a field, finite component sets, generic points, discrete valuation cotangent spaces, and Noetherian local dimension bounds. None gives the arbitrary valuation-base fibre comparison, and the properness, discrete-valuation, or Noetherian hypotheses of some hits cannot be supplied. Their results and no-match verdicts are in the item's mathlib_searches; none is labelled unavailable.

Searched the whole DAG for Tag 00QK and its label, for open/component and field dimension facts, affine fibre tensor products, reduced induced closed subschemes, localization base change, and local dimension at a point. Opened the statements of all nodes used. Ran blueprint_refs.py ancestor for the item (nearest ancestor lem-trf-local-term-locality), and whole-blueprint searches `valuation dimension`, `00QK`, and `dimension-locally-algebraic`; no imported blueprint node states this item. Retained its precise from.place and via list and recorded how the eight steps serve that place in split_report.blueprint.

## Not duplicates

No new nodes; the existing affine theorem and existing field-dimension and affine-localization tools are cited instead. This avoids introducing duplicates under 00QK, 0A21, 00OT, 00DK, 01I4 or 01J3.

## Review by Q37

I read the item against the 0GSI paragraph and the complete affine theorem 00QK. The first is the actual scheme use of the second: the integral scheme dominates the valuation base, so each nonempty finite-type affine chart is a domain containing A. The statement needs no flatness assumption; the proof never applies a flat-family theorem. Both fibres are locally Noetherian because their coordinate rings, not A, are finite type over fields.

Step 1 cites def-weil-finite-type-morphism for a finite-type affine cover, def-pc-integral-scheme for domains, def-sc-generic-point for density, def-weil-affine-spectrum for induced affine ring maps, and lem-weil-pbc-spec-irreducible-closed-subsets-primes for the zero prime's closure. The last statement really says closure{p}=V(p). In a domain this makes (0) the generic prime. Generic-point dominance makes its inverse image zero, which is exactly injectivity of A to B. No surjectivity of h or closed-fibre nonemptiness is assumed.

Step 2 cites lem-weil-pbc-open-fibre-product and lem-weil-pbc-fibre-product-affine-spectra. The first explicitly identifies the open inverse images; the second supplies Spec(B tensor L), not only an isomorphism of section rings. The tensor generators are written out as polynomials, so no unquoted finite-type base-change theorem is hidden here. def-weil-pbc-finite-type-algebra and def-weil-finite-type-morphism identify the resulting finiteness properties. lem-weil-pbc-finite-type-algebra-noetherian says finite type over a Noetherian ring is Noetherian; a field's two possible ideals supply its hypothesis. pqf-def-locnoeth is precisely the affine-cover definition being used.

Step 3 cites lem-weil-pbc-localization-base-change: its statement supplies B tensor K as localization at the image of A minus zero, with no flatness hypothesis. The fraction calculation explicitly proves nonzero and no zero divisors, using injectivity from step 1 to exclude zero denominators. The spectrum closure theorem then identifies the zero prime's generic point and its contraction.

Step 4 cites the affine reducedness equivalence, def-pc-reduced-scheme (the stalk formulation), and def-pc-scheme-fibre (including its explicit homeomorphism onto the set-theoretic fibre). Thus the generic points in the charts are the same point above eta, not merely an unspecified collection of points. Their density on all charts gives a dense global point; the closed-cover argument for irreducibility is included. def-pc-integral-scheme explicitly includes the reduced-and-irreducible equivalence. Open restriction preserves the local ring by the definition of restriction, so this is a direct local argument, not an uncited integrality-under-arbitrary-base-change claim.

Step 5 applies lem-sc-integral-locally-algebraic-opens-dimension only after steps 2 and 4 establish all its hypotheses: integral, locally finite type, and field base K. Its statement allows every nonempty open, without quasi-compactness. The other two cited statements are homeomorphism invariance and equality between ring dimension and dimension of its spectrum, exactly the conversions used here. This is also why generic fibre dimension is common to all chosen charts.

Step 6 opens and uses lem-trf-valuation-domain-fibre-dimensions. It assumes precisely a valuation domain, an included finite type domain, and nonzero closed tensor fibre, and concludes equidimensionality with component dimension equal to generic ring dimension. Each assumption was checked here: inclusion and finite type in step 1, nonzero from the point in U_k, generic dimension in step 5. The cited homeomorphism theorem transfers its spectral conclusion to the chart; it is not being used to claim dimension equality for an arbitrary continuous map.

Step 7 cites lem-sc-components-open-injection, whose statement actually says that a component meeting an open has a component as its intersection, so it supplies E intersect U_k. The reduced-induced-scheme node supplies a reduced closed scheme with image E. def-weil-closed-immersion includes the homeomorphism onto that image; def-pc-integral-scheme then gives integrality. lem-weil-pbc-immersion-base-change-lft gives the closed immersion's local finite type property, and part (e) of lem-weil-pbc-proper-fp-permanence gives composition for locally finite type morphisms. No properness part of that bundled statement is used. The field open-dimension theorem applies to this reduced component with no global quasi-compactness assumption; homeomorphism invariance is again the only topological transport. These are actual statement-level inputs, not assertions extracted from their proofs.

Step 8 cites lem-weil-pbc-dimension-at-point-components, which explicitly identifies local topological dimension of a finite type affine field scheme with the maximum of the component dimensions through the point. This is the needed formula, not a local-ring dimension formula at the generic prime. The cited statement also gives nonemptiness of that finite maximum. Step 6 gives every entry d. lem-weil-pbc-dimension-at-point-open-subspace explicitly equates local dimension on an open with that on its ambient space. Its hypotheses hold because U_k is the open inverse image obtained in step 2. This completes every clause.

I checked the B--E return checklist against these files: all proof steps are judged non-elementary and name their actual theorem inputs; elementary fraction, ideal, tensor-generator and dense-point calculations are written in the steps. There are no new statement-only nodes to leave with proof data or missing definitions. Every step is under 900 characters, hence none triggers the 2000-character hidden-lemma review threshold. There is no new definition, additional hypothesis, SGA citation or replacement of the prescribed affine 00QK route. citations.json contains a verbatim statement quote for every cited step/node pair.

Small cases checked: if A is a field, both fibres are Z and the result reduces to the field dimension theorem; no argument assumes a nonzero maximal ideal. For a DVR A, Z=Spec(A[1/pi]) has empty closed fibre, and the component argument is correctly skipped. A ramified domain A[x]/(x^2-pi) can have nonreduced closed fibre, so the proof does not assume reducedness there. The domain A[x,y]/(xy-pi) has a reducible closed fibre with two one-dimensional components, both allowed. An infinite-origin integral line over a field tests the absence of global quasi-compactness: only affine covers and the locally algebraic open-dimension theorem are used. Nothing chooses a uniformizer for the arbitrary valuation ring in the theorem, or assumes its rank or Noetherianity.

The split's main repair of the statement-only input is the explicit globalization through a component's reduced induced scheme and the separate local-dimension computation. No statement was changed and no new node was needed. The maintainer's independent review remains to assess this direct delivery after the required tool checks.
