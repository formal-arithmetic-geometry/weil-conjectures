# Q87: lem-trf-projective-nodal-family-geometry

1. Files written:
   - `dag/nodes/sec-trace-formula/lem-trf-projective-nodal-family-geometry.json`: completed the four-step split; statement unchanged.
   - `dag/nodes/sec-trace-formula/def-trf-first-fitting-singular-subscheme.json`: new definition node; no Mathlib match.
   - `dag/nodes/sec-trace-formula/lem-trf-nodal-family-fitting-singular.json`: new statement-only node; no Mathlib match.
   - `citations.json`: verbatim excerpts for every cited node in every item step.
   - `searches.jsonl`: records of the required Mathlib searches.
2. Attachments: none. The read-only Lean source has no declaration tagged or named for this item.
3. WANTED: none.
4. Faults and corrections: the repository node had no proof and its `created` metadata named Q88's different item; the sandbox copy corrects that metadata to this Q87 item. The imported statement itself was retained. The source's “first Fitting ideal” construction was made an explicit definition node so the theorem node and item do not use an undefined notion. No statement dispute was found.
5. Unfinished: the two new nodes are intentionally unsplit stage-1 dependencies; their later proofs remain for downstream workers.

## Review by Q87

I read the item, `sec-trace-formula` chapter, `sk-i-curve-zero` unit, and the Stacks sources `curves.tex` Tags 0C59 and 0C5B plus `divisors.tex` Tags 0C3I–0C3K. I also read every existing node cited by the item: projective base change, flat base change, finite-presentation base change, unramified base change and discreteness over a field, and finiteness of zero-dimensional closed subschemes over a field. The new definition introduces relative Kähler differentials and the first Fitting ideal, and the new lemma states the exact nodal-family consequences used here: openness of the smooth locus, identification of its complement with the Fitting singular subscheme, unramifiedness, and scheme-theoretic formation under arbitrary base change.

Step 1 checks the item's flatness, local finite-presentation, one-dimensional-fibre, and completed ordinary-double-point hypotheses against the new nodal-family lemma, then defines (S_f) as its canonical Fitting singular subscheme. Step 2 checks the geometric fibre argument: unramifiedness survives base change, projective fibres are finite type, an unramified scheme over an algebraically closed field is discrete, and the existing zero-dimensional closed-subscheme lemma gives finiteness. Step 3 checks projectivity, flatness, and local finite presentation under the arbitrary base change (Y_1\to Y); fibre-product associativity then carries nonemptiness, connectedness, dimension one, and the nodal completed local rings to each geometric fibre. Step 4 uses the new lemma's scheme-theoretic Fitting base-change equality to identify (S_f\times_Y Y_1) and (U\times_Y Y_1) with the corresponding singular and smooth loci, without asserting anything about reduced subschemes.

I checked each citation quote against the cited node's statement and recorded it in `citations.json`; every non-elementary use appears in `proof_deps`. The four Mathlib search kinds were run for the item and for each new node, with their actual outputs retained in the node records and `searches.jsonl`. No existing DAG or blueprint node states either new fact, and no Lean declaration attaches to the item.

## Not duplicates

def-trf-first-fitting-singular-subscheme vs def-sc-relative-differential-sheaf: the existing node defines the relative Kähler differential sheaf \(\Omega^1_{X/S}\), whereas the new node defines the first Fitting ideal of that sheaf and the resulting singular closed subscheme \(\operatorname{Sing}(f)\).

def-trf-first-fitting-singular-subscheme vs lem-sc-relative-differentials-affine-chart-derivation: the existing node proves the affine derivation description of relative differentials; it does not define Fitting ideals or the singular closed subscheme.

lem-trf-nodal-family-fitting-singular vs lem-trf-projective-nodal-family-geometry: the new node is the general flat locally finitely presented nodal-family theorem for the Fitting singular subscheme, including its unramifiedness and arbitrary-base-change formation, while the item adds projectivity, connectedness, nonemptiness, finite geometric fibres, and the full projective-family conclusion.
