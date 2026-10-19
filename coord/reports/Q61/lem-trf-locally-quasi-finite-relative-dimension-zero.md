# Q61: lem-trf-locally-quasi-finite-relative-dimension-zero

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-locally-quasi-finite-relative-dimension-zero.json`: statement; split using existing affine-chart and ring-level results; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the 18 step/node citations.
- `report.md`: this report. `searches.jsonl` is the search command's log; `prepare.py` is sandbox-only preparation material.

## New nodes

None. Zero new nodes and zero new Mathlib leaves.

## Attachments

None. The project search for the exact blueprint tag and for LocallyQuasiFinite, fibre dimension, and relative dimension found related results, but no sorry-free declaration stating this item. In particular `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean` proves dimension preservation under a universally closed surjective locally quasi-finite morphism; that is a different statement. Its discrete-fibre statements do not themselves identify the minimum-over-neighbourhoods dimension at a point.

## WANTED

None. All sources used are available locally.

## Audit of the imported item

The statement agrees with Stacks Tag 0397 (`morphisms.tex`, `lemma-locally-quasi-finite-rel-dimension-0`, lines 5642–5675). Its global equivalence is the final assertion of the source. It assumes locally finite type and uses dimension at a point of the whole fibre, NOT dimension of the local ring at that point. No statement correction or dispute is needed. The item had no proof or Lean attachment record. Its source, statement, statement dependencies, creation metadata, blueprint ancestry, and inherited Mathlib searches are retained.

The DAG already contains `lem-weil-pbc-ring-quasifinite-zero-fibre-dimension`, reviewed 2026-10-14, which proves the corresponding ring-level equivalence. This is reused, rather than creating another isolated-point/dimension-zero node or another clause of the item. I read its statement and proof and checked that its dependency closure does not contain this item. Its argument uses the locally Noetherian zero-dimensional discrete-space route of the second proof of 0397, specifically Properties 0H7C and 0AAX. This delivery writes the affine reduction to that result, with proof origin `agent` because this affine organization is our reconstruction rather than the verbatim organization of 0397.

## Searches and blueprint route

Whole-DAG tag/keyword searches included 0397, 02G4, 02G5, `lemma-quasi-finite-at-point-characterize`, isolated points and dimension zero. Whole-blueprint searches with `tools/blueprint_refs.py` used `quasi-finite`, `isolated`, and `dimension zero`; no blueprint node duplicates the item's full assertion. The ancestor command gives `lem-trf-local-term-locality`, as recorded in the item. I read the chapter and unit records and the current main-20261015 ancestor statement. The inherited creation chain uses this as the 0397 input to the proper-flat finite-dense-open argument (0B48), below the contracting-local-term route. No chapter, unit, or ancestor is changed. The existing ring lemma is a generic tool from another unit and is declared in `split_report.tool_uses`.

Fresh Mathlib searches were run through msearch with leanfinder, loogle, grep and leansearch. A second semantic phrasing asked about isolated fibre points and local topological Krull dimension. I read the returned hits and inspected `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`, especially `locallyQuasiFinite_iff_isDiscrete_preimage_singleton` at line 276 and the fibre-finiteness result at line 265. These characterize discrete fibres or finite fibre morphisms; they do not state the equality of the topological dimension at a point with zero. The second phrasing also returned `IsLocallyArtinian.of_topologicalKrullDim_le_zero`, which concerns global Krull dimension under a locally Noetherian hypothesis, not this local-at-a-point equivalence. Thus the item is not a single Mathlib leaf. Fresh queries and actual returned names are appended to `mathlib_searches` and recorded in `searches.jsonl`; inherited Q74 searches remain identified by their existing entries. No new node needs searches.

## Review by Q61

I read Stacks 0397 in full, both proofs, and Properties 0H7C (`lemma-isolated-dim-0-locally-noetherian`, lines 1373–1387). The latter explains exactly why the dimension is a neighbourhood minimum and why zero gives an isolated point in the Noetherian setting. The existing ring-level lemma already carries this non-elementary content, and is cited rather than reproved or left implicit. I also read Morphisms 01T2 (`lemma-locally-finite-type-characterize`, lines 2673–2700), Schemes 01I4 and 01JQ (affine fibre products), and Topology 0055, definition and the following open-neighbourhood remark. These justify the reduction and dimension comparison without any Noetherian assumption on the base.

Step 1 uses the statements of `lem-weil-pbc-affine-opens-basis` to choose V around s and U inside the open f^{-1}(V), and `lem-weil-pbc-affine-open-spec-points` to use their canonical spectrum charts. `def-weil-affine-spectrum` describes the induced map on primes, giving p=phi^{-1}(q). `def-pc-scheme-fibre` supplies the unique point above x. `lem-weil-pbc-lft-affine-pairs` says precisely that every such affine ring map is finite type. I verified that its hypothesis is locally finite type, exactly the item's hypothesis; no quasi-compactness or finite presentation is inserted.

Step 2 uses `lem-weil-pbc-affine-open-stalk-localization` to identify O_{S,s} with R_p. Quotienting the corresponding maximal ideals gives kappa(s)=kappa(p) by `def-weil-residue-field`. This ensures that the ring-level lemma's field is the scheme fibre's field. `lem-weil-pbc-fibre-product-affine-spectra` identifies the restricted fibre with Spec(A tensor_R kappa(p)) and specifies its projection map; `lem-weil-pbc-fibre-ring-primes-bijection` identifies the precise prime over q. The homeomorphism clause of `def-pc-scheme-fibre` applies to both U→V and X→S, identifying the former's space with the open subspace U intersect f^{-1}(s) of the latter's space. I wrote this comparison out through those two subspace homeomorphisms, rather than assuming an uncited base-change theorem. `lem-weil-pbc-homeomorphism-krull-dimension` identifies dimensions of corresponding open neighbourhoods. Taking the minima using `def-kun-topological-dimension-at-point`, and applying `lem-weil-pbc-dimension-at-point-open-subspace`, proves the stated local-dimension equality. The open-subspace lemma really states equality of dimensions at a point, not just a bound for global dimensions. This is a routine composition of the cited statements, with no extra finiteness or separation hypothesis.

Step 3 uses `pqf-def-quasifinite` to choose the witnessing affine pair for quasi-finiteness at x; it does not assume quasi-finiteness of an arbitrary chart. On this pair `lem-weil-pbc-ring-quasifinite-zero-fibre-dimension` supplies exactly the forward implication with finite type phi and the correct primes p,q. Step 2 then supplies the equality with the whole fibre's local dimension.

Step 4 starts from the zero dimension hypothesis, uses a chart from step 1, and uses step 2 and the reverse implication of the SAME ring lemma. Its conclusion is quasi-finiteness of phi at q, exactly what the affine witnesses in `pqf-def-quasifinite` require. Quantifying over x gives local quasi-finiteness. Step 5 only assembles the implications and checks the empty case, so it alone is marked elementary. For each cited node I opened its statement; `citations.json` quotes that statement verbatim, including the clauses just described. No step relies on a cited node's proof instead of its statement.

I checked delivery-errors B–E: the item remains self-contained, no new node or hollow definition is introduced, every non-elementary input is an existing cited node, there is no duplicated node or whole-conclusion child, and the proof dependencies are exactly the union of the steps' uses. The existing ring node's path does not return to this item. Every step is below 2000 characters (753, 1378, 600, 585, 246); step 2's comparison is explicit and uses the stated fibre homeomorphisms and dimension lemmas, not an unnamed comparison theorem. The split retains the unit route and records its only non-closed off-unit theorem as a generic tool.

Edge cases: for X empty both pointwise conditions are vacuous, including empty fibres. Finite nonreduced field schemes, such as Spec(k[epsilon]/epsilon^2), have dimension-zero singleton fibres and are included; no reducedness or etaleness is asserted. At the generic point of A^1_k the local ring has dimension zero but every open neighbourhood has dimension one, so the hypothesis fails, as it must: this explicitly checks the two meanings of dimension have not been confused. The base can be non-Noetherian: the ring lemma requires only a finite type ring map and forms a finite type algebra over the residue field. Nothing in the affine comparison assumes a finite fibre, flatness, properness, separation, a perfect field, or invertibility of coefficients.

## Unfinished work

None in the stage-1 split. Delivery validation is recorded by the delivery tool; no Lean was written and no compiler or build command was run.
