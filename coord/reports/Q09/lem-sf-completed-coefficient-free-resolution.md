# Stage-1 report: lem-sf-completed-coefficient-free-resolution

Group Q09; 2026-10-21. Direct delivery, authored and self-reviewed by this worker.

## Files written

- `dag/nodes/sec-six-functors/lem-sf-completed-coefficient-free-resolution.json`: item split into six proof steps; statement unchanged; no Mathlib match.
- `citations.json`: twelve step/node citations, each with a verbatim quotation checked against the current node statement.
- `report.md`: this report. `searches.jsonl` is the search command's original log. The local construction script is not part of the node delivery.

New nodes: 0. New Mathlib leaves: 0. All mathematical ingredients already exist.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, quotient towers, completed coefficients and uniformizers, and read `SixFunctors/ProEtale/CompletedIntegral.lean`, `CategoryTheory/DerivedCategory/Monoidal/TensorMappingCone.lean` and the reduction discussion in `SixFunctors/Etale/Derived/ProjectionFormula/Reduction.lean`. The completed ring and quotient projections are defined, but no declaration gives all clauses of this item. The generic scalar-cone results alone are not an attachment for the coefficient-sheaf resolution or the free-cell completeness clause.

## WANTED

None. All documents used in this split are locally present. No source was downloaded.

## Audit of the item and blueprint

The original node was statement-only; no previous sandbox split or report existed. Read the fixed six-functors chapter and `sk-rem-sf-pf-done` unit, and the main-20261015 statement and proof of `lem-fix-weil-operations`. This is the supporting completed coefficient calculation beneath the local projective models for tensor evaluation, not a new unit route. No chapter, unit, target, statement, or maintainer-owned field is changed.

The statement is true for arbitrary schemes, with no quasi-compactness or boundedness hypothesis. The proof stays in modules over the actual limit ring sheaf B_T throughout; it does not replace B_T by the constant R sheaf or invoke completeness of that constant sheaf. The scalar extension target is a quotient-coefficient derived category until its explicit restriction to B_T-modules in step 5.

The original source points to Stacks 09C3 (`proetale.tex`, `lemma-local-structure-constructible-complex`) and 099I (`algebraization.tex`, `lemma-restriction-derived-complete-equivalence`). I read both. They explain the surrounding local-model use, but neither is used as a black-box proof of the three clauses. The actual supporting arguments read are Stacks 093J/093M (`sites-modules.tex`, `lemma-constant-exact` and `lemma-completion-flat`), 06YQ/06YS/06YP/06YM (`sites-cohomology.tex`, bounded flat K-flatness, unbounded K-flat resolutions, preservation of quasi-isomorphisms, exact tensor on the homotopy category), and `derived.tex`, `remark-double-complex-as-tensor-product-of`, plus Bhatt-Scholze Propositions 3.1.9-3.1.10, 3.2.3(1), and 4.2.8. The proof is marked as document-based, with each specialized elementary calculation written explicitly.

Two existing citations have source metadata slips; their mathematical statements supply exactly what is used and are not edited here. `lem-pc-bounded-above-flat-kflat-site` says the bounded-above flat K-flat theorem, but calls it 06YS: the correct tag is 06YQ (`lemma-bounded-flat-K-flat`), while 06YS is existence of resolutions. `lem-pc-tensor-mapping-cone-iso` cites 07A3 as a cone-comparison source; 07A3 is actually `lemma-K-flat-two-out-of-three`. For its correct tensor-cone statement I checked the construction behind 06YM and `derived.tex`, `remark-double-complex-as-tensor-product-of`; step 6 cites these places. These are bibliographic corrections in the report, not statement disputes.

## Searches and reuse

Searched the whole DAG for completed quotient coefficients, constant-sheaf exactness, K-flat complexes, surjective towers, and tensor-cone comparison. Read the existing nodes selected below, their full statements and their dependency closures; none reaches this item, so their use makes no cycle. The parent split's recorded ingredient list agreed with the direct searches. Blueprint searches `completed coefficient free resolution`, `scalar multiplication cone`, and `surjective tower` each returned zero imported blueprint matches; the ancestor command gives `lem-fix-weil-operations`. The item's `same_as` remains empty and its already-specific `from.place` is retained.

Ran the mandatory search command for the item with LeanFinder twice, Loogle, LeanSearch and Mathlib grep. All five completed successfully and are recorded exactly in `searches.jsonl` and appended to `mathlib_searches`; inherited searches are preserved. Loogle's sole result is the complete lattice of submodule sheaves. Semantic results concern period rings or ordinary module adic completion. I read the scalar completion tensor results in `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean` (finite-coordinate bijectivity at line 191, finite Noetherian tensor equivalence at line 328): they concern ordinary modules, with no pro-etale sheaf derived limit or unbounded scalar reduction. The `CategoryTheory/Sites` grep returned no hits. No result states this item or specializes to it in one line.

## Not duplicates

No new nodes were created. In particular, the completed-constant-sheaf reduction, bounded-flat K-flatness, surjective pro-etale tower and tensor-cone lemmas were reused instead of restated. `lem-weil-pbc-completed-constant-sheaf-reduction` is an ingredient of this item, not its duplicate: it gives flatness and the finite quotient identification, and does not assert the free-cell derived-limit reconstruction or the unbounded reduction triangle.

## Review by Q09

I checked the six steps with their sources and all cited node statements open. The new-node checks B1-B10 are vacuous because there are no new nodes. The item's mathematical statement and all its original statement dependencies are preserved; its notions have the definitions already listed there. Every step is marked non-elementary because each invokes an existing theorem; the short algebra, finite-coordinate and unit-map calculations are written inside the steps. Every step is below 1,200 characters, so there are no long steps hiding a new lemma.

Step 1 uses `lem-weil-l-adic-extension-integers-dvr` for the domain/PID property and the nonzero uniformizer, and clause (1) of `lem-weil-pbc-constant-module-section-properties` for exactness on sections. I checked that the latter assumes a Noetherian coefficient ring: the preceding PID property makes every ideal principal, hence finitely generated. The kernel of the scalar quotient map is explicitly varpi^n R, and no exactness of arbitrary pro-etale sections is assumed. The section-exactness theorem is used only on constant module sheaves. Quotient transitions are actual surjections of constant modules, giving epimorphisms of B_T-modules when restricted.

Step 2 uses `lem-weil-pbc-completed-constant-sheaf-reduction` exactly for flatness over the constant R sheaf and the canonical derived quotient identification. Flatness gives ordinary tensor and preserves the preceding sequence. I verified A=R is Noetherian, I=(varpi), all exponents are positive, and the inverse limit in its statement is the same B_T. The map b tensor r-bar to q_n(b)r-bar fixes the augmentation. This proves exactness before naming the free complex, and is not a new node restating a clause.

Step 3 uses `lem-pc-bounded-above-flat-kflat-site` for a bounded two-term complex over the ringed pro-etale site. Its statement is the required general ringed-site theorem, irrespective of the metadata slip noted above. Tensoring with a finite sum of copies of B_T is a finite sum of identity functors, which establishes the flatness needed for the same theorem on free cells.

Step 4 uses `lem-pur-derived-change-of-rings` to compute free-cell scalar extension by its K-flat representative, `lem-weil-proetale-surjective-tower-derived-limit` for the derived limit with its projections, and `def-weil-derived-limit` for the Roos triangle. The tower theorem allows any commutative ring sheaf, so its ring is B_T, not the varying quotient rings. The tower consists only of sheaves in degree zero and its transitions were proved epimorphic in step 1. I read Bhatt-Scholze's proof of 3.1.10 and its exact-products/repleteness inputs. The inverse limit and the quotient maps are identified coordinate by coordinate. Shifts preserve products because they are equivalences; the Roos triangle then shifts with the specified projections. There is no use of inverse limits commuting with arbitrary direct sums.

Step 5 uses `lem-pc-kflat-resolution` for an arbitrary unbounded complex, `lem-pur-derived-change-of-rings` for its derived quotient model, and `lem-weil-pbc-total-tensor-homotopy-cone-signs` specifically for preservation of quasi-isomorphisms with arbitrary endpoints by a K-flat tensor factor. I checked these exact clauses: it would be incorrect to use only a theorem about quasi-isomorphisms between two K-flat complexes, since R_{n,T} need not be K-flat. Restriction leaves the underlying complex unchanged. The augmentation on the degree-zero term gives x tensor 1, proving the derived scalar unit normalization without a boundedness or flat-cohomology assumption.

Step 6 uses the full inclusion-compatible statement of `lem-pc-tensor-mapping-cone-iso`, not merely a tensor object isomorphism, and the cone-triangle convention in `def-weil-abstract-derived-category`. This carries the inclusion Q to Cone(varpi^n) to exactly the middle reduction arrow from step 5. All claims about a distinguished triangle are justified by this definition of the derived triangulation. The connecting map has the sign of the existing cone convention; the item only prescribes the middle arrow, which is tracked explicitly.

For E1-E7 I checked n=1, arbitrary n>1, r=0, the empty scheme, a free cell in either a positive or negative degree, M=0, M=B_T, and M=R_{1,T}. In the last example reduction genuinely has a degree -1 Tor contribution: the proof retains it through the multiplication cone. It never assumes the quotient is flat over B_T or that reduction is underived. No extra geometric hypotheses, wrong coefficient category, non-small index category, unsupported transport, circular lemma, or SGA reference occurs. All off-unit statement dependencies are generic algebra or derived-category tools, declared with reasons in `split_report.tool_uses`; the unit itself has no substitute for these foundational calculations. `citations.json` records every cited node in every step and each quote was mechanically checked as a literal substring of that node's statement.

The preliminary server `review_split` passed with zero new nodes. Final dry-run and delivery results are recorded below when complete.

## Unfinished work

None in the one-level split. The cited existing nodes remain the independent DAG tasks they already were; no Lean or compiler was run.
