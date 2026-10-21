## Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-section-centred-coordinates.json`: statement, split into ten steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the 31 step/node citations.
- `report.md`: this report. The sandbox also retains `searches.jsonl` and the local writing script.

## Attachments

None. Searching the live `lean/WeilConjectures/` for the item tag, centred/centered coordinates, conormal graded algebra and smooth-section regularity did not find a declaration giving the entire item. In particular `AlgebraicGeometry.exists_etale_neighbourhoods_of_smooth_section` in `AlgebraicGeometry/SmoothSectionEtaleNeighbourhoods.lean` concerns quotient neighbourhoods and does not assert centred charts or their graded algebra. The standard-smooth polynomial chart declaration supplies only a preliminary tool, already represented by `lem-sc-standard-smooth-etale-polynomial-chart`.

## WANTED

None. The blueprint and all Stacks sources needed for the split are present locally. No SGA source is used.

## What needed repair

The item was unsplit, rather than an earlier completed sandbox attempt. Its statement is mathematically sound. I retained the whole statement and its inherited searches, source, creation record and blueprint ancestry; I added definition references for regular closed immersions with specified codimension and for base change. There is no statement dispute or weakened conclusion.

The blueprint's Local construction permits an etale base cover and leaves the affine refinements unstated. Here a Zariski cover suffices: choose a chart through each section point, shrink the base so its entire section lies in that chart, and translate by its section coordinates. Removing the other zero-fibre components may destroy affineness; the proof therefore chooses a new affine source neighbourhood and a smaller affine base, taking their fibre product over the earlier affine base. This does not assume arbitrary affine-open intersections are affine. The blueprint's clopen argument is used scheme-theoretically, with the actual inverse isomorphism furnished by the section lemma.

## Unfinished work

None for this one-level split. No new pending lemmas were required; all non-elementary inputs are already DAG statements.

## Not duplicates

No new nodes. Existing nodes for Stacks 054L, 024T, 067U, conormal algebras, flat tensor injections, standard-smooth polynomial charts and regular-sequence associated graded algebras were searched and reused as appropriate. In particular the broader smooth-pair coordinate theorem was not restated as a new centred-section theorem. Blueprint searches for `conormal` and `etale coordinates` found no blueprint node equal to this full item; `same_as` remains empty. The nearest blueprint ancestor was confirmed by `tools/blueprint_refs.py ancestor` as `lem-trf-local-term-locality`.

## Mathlib search assessment

I ran the supplied `msearch.py` command with LeanFinder twice, Loogle twice, LeanSearch, and source grep twice; the exact queries and actual returned names are in `searches.jsonl` and appended to the item's existing `mathlib_searches`. One Loogle query used an unrecognized identifier and was retried with the actual `SmoothOfRelativeDimension` and `Etale` names. No failed service was called an absence result. LeanFinder found standard-smooth affine charts and etale polynomial factorizations, not the full section-family assertion. I read the local source of `RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` at StandardSmooth.lean:253–258, the `SmoothOfRelativeDimension` chart field at Smooth.lean:136–138, and the relative-dimension-zero characterization at Etale.lean:108. These support existing preliminary DAG tools, not an attachment or a leaf for the whole item. Other hits concerned standard-etale presentations, general etale definitions and manifold sections; none asserts all clauses here.

## Review by Q129

I read the current item's source, `main-20261015/.../sk-thm-dnc.proof.md`, particularly the Local construction, and the trace-formula chapter/unit records. This is the centred-coordinate geometric input on the inherited normal-cone specialization route; it does not replace the contracting-correspondence theorem or use any trace construction from SGA. I also read Stacks `morphisms.tex` 054L (smooth etale affine-space normal form), 02GJ (affine etaleness) and 02GO (base change); `etale.tex` 024T (sections); `schemes.tex` 01IT (affine-open basis), 01I4 (tensor-product fibre products) and 01KU (separated base change); `algebra.tex` 00LN together with its explicit quasi-regular polynomial map; and `morphisms.tex` 01R3 (affine conormal modules). The proof is marked agent-origin because it assembles and supplies the explicit affine and algebraic arguments rather than copying a single document's proof. No new node needs an additional source audit.

For every dependency I opened and read its statement before writing the proof; `citations.json` quotes those actual statements verbatim, including all hypotheses. The checks by step were as follows.

1. The standard-smooth local-relative-dimension node gives charts with exactly the prescribed dimension d, not merely an unspecified n. Its polynomial-chart node states the etale ring factorization with unchanged constant map; taking affine spectra gives the required chart. Both hypotheses hold for g at s(t).
2. The affine-basis statement supplies the smaller base inside the inverse image of the first source chart. The affine-fibre-product statement supplies affineness of the new source, and the etale base-change statement applies without a Noetherian or finite-field restriction. The translation has its explicit inverse. The etale-composition node applies to its composite; the affine-source-separated statement applies because the source has been kept affine. No separatedness theorem is extracted merely from a definition.
3. The zero-fibre map is literally a base change of the separated etale chart, meeting both permanence nodes' hypotheses. The clopen-section node states both open-and-closedness and that projection on the section is its inverse. This proves equality of the remaining fibre as a scheme; pointwise equality alone is not used to discard nilpotents.
4. The second source and base refinements use the affine-basis node separately. Their fibre product over an affine base, not a possibly nonaffine intersection, is affine by the tensor-product node. Open restrictions compose with the etale map and its base change. The fibre-product universal property preserves the zero-fibre square. The selected bases contain t and therefore are nonempty.
5. The affine-etale equivalence gives the ring-map property, and the separate etale-algebra-flat lemma gives flatness. The affine-fibre-product node gives the tensor ring and the displayed mutually inverse quotient maps compute its ring explicitly. The existing ideal-sheaf definition gives precisely the augmentation kernel, so it really is J_i B_i.
6. The polynomial multiplication injections are proved by shifting coefficients. The flat-tensor-injection node applies to P_i-linear maps with flat module B_i. Both directions of the tensor/quotient identification are written; under them the map is the specified multiplication. The regular-sequence definition also requires a nonzero final quotient: it is R_i, which is nonzero because S_i contains t. This prevents confusing weak regularity with regularity.
7. The graded-polynomial theorem's hypotheses now hold with its ring R equal to B_i and quotient B equal to R_i. Its statement includes the graded isomorphism, the exact monomial formula and the basis in every degree; none is inferred from its proof or from the conormal definition.
8. The regular-immersion definition asks for affine local equations of the specified length, supplied in the previous steps. The conormal-algebra node states the affine identification I_i/I_i^2, and the affine-frame lemma takes exactly such a basis, requiring no regular base or field hypothesis. It supplies the sheaf frame and stalk rank.
9. The conormal node actually states the canonical map and its generator formula. It also states quasi-coherence, needed for the symmetric-algebra affine comparison. The free-symmetric-polynomial node applies to the resulting free conormal module. Comparison with the explicit graded-polynomial theorem is equality on polynomial generators, so the map shown to be invertible is the canonical multiplication map, not some unspecified algebra isomorphism.
10. The restriction and gluing assertions use that same canonical sheaf map and its product formula. The inverse gluing argument is elementary: two inverses of a common map are equal. The restriction calculation is written on products of local representatives and does not assert coordinate bases coincide on overlaps.

I checked the empty-base case (empty cover), d=0 (empty regular sequence on each nonempty chart; zero ideal and only degree zero), m=0 (identity on R_i), arbitrary nonregular/nonreduced Noetherian bases (no base regularity used), and multiple zero-fibre components (removed only the clopen complement). The proof needs no stronger base hypotheses. All ten steps are shorter than 2000 characters; the only elementary-marked step is the explicit restriction, inverse-gluing and d=0 calculation. The other steps cite their non-elementary tools. All newly added proof edges are to existing generic geometry or algebra nodes; off-unit uses are declared in `split_report.tool_uses`. No unit or chapter file was altered.
