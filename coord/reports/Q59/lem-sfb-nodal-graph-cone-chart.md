# Stage-1 worker report: lem-sfb-nodal-graph-cone-chart

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-graph-cone-chart.json: statement; split into six steps, no Mathlib match for the whole assertion.
- citations.json: one entry for every use in the item's proof; full statements are quoted verbatim so the hypothesis and conclusion used can be read together.
- searches.jsonl: actual msearch log, retained unmodified.
- report.md: this report.

Zero new nodes, zero Mathlib leaves. No Lean was written and no compiler, Lake or build command was run. The repository and launcher were only read.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id, graph conormal terminology and nodal terminology returned no project declaration giving this assertion. The few nodal occurrences were examples in unrelated docstrings. Existing Mathlib differential comparisons are cited through the existing DAG leaf lem-trf-formally-etale-differentials-base-change, rather than claimed as an attachment to this item.

## WANTED

None. All proof sources used are locally present.

## Corrections and scope

The item was unsplit, had no proof or proof dependencies, and had no repair note. The sandbox initially had no item copy or completed delivery. Its statement, statement dependencies, source and blueprint ancestry are retained. The proof clarifies that the unique augmentation-preserving comparison means the unique inverse maps on infinitesimal graph neighbourhoods supplied by formal etaleness; it does not assert uniqueness of arbitrary ambient etale neighbourhood morphisms. No normalization of total spaces is used.

The proof uses the general flat base-change theorem only for base change of the centre D_U -> D. Replacing the ambient graph by U and W instead uses the augmented-etale theorem, which does not require the graph ideal to be the extended ambient ideal. Conflating these two operations would leave a gap.

The existing ancestry is from the relative graph-cone Steps 4-5 of the branch-double-cover argument, below the direct-image alteration reduction. The blueprint ancestor command returns None for this existing chain; the inherited from.node=null and via list are preserved. I read the chapter record, unit record and current main-20261015 unit text. No chapter or unit file is changed.

## Mathlib and duplicate searches

The five searches in searches.jsonl were executed with the required msearch command for Q59 and this item. Both semantic phrasings were read. StandardEtalePair and StandardEtalePresentation concern standard etale presentations; SetLike.GradeZero, HomogeneousLocalization and ProjectiveSpectrum concern general graded/localization structures; the Weierstrass hits concern a different polynomial equation. None gives this graph-cone chart calculation. The Loogle hits include KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale and its map formula; I read Mathlib/RingTheory/Etale/Kaehler.lean:31-61 and Basic.lean:42-49 and used the already existing differential-comparison node. Grep returned no matching nodal graph-cone declaration. No unavailable service has been recorded as a negative result.

DAG searches by the source tags 0CBY, 0C3I, 07ZA, 0H1D and 0635, by graph/conormal terminology, and by differential and monomial terminology found the exact existing tools cited in the split. Blueprint searches for nodal and conormal returned no duplicate item; the normal-cone definitions found by the latter are definitions, not this comparison theorem. No new node is proposed.

## Not duplicates

No new nodes; no new/existing node pairs require differentiation. In particular lem-sfb-augmented-etale-associated-graded, lem-pur-conormal-algebra-flat-base-change, lem-trf-nodal-family-etale-local-model, the Fitting node and the differential nodes are reused rather than copied.

## Review by Q59

I read Stacks algebra.tex Tag 0H1D (lemma-formally-etale-lift-infinitesimal), including the successive unique lifts and the graded conclusion, and Tag 0H93 (lemma-formally-etale-omega), whose last assertion is the needed differential comparison. I also read algebra.tex Tag 00RU (lemma-differential-seq); the proof here instead writes the universal-derivation calculation explicitly. I read divisors.tex Tag 0635 (lemma-conormal-algebra-functorial-flat) and Tag 0C3I (lemma-base-change-and-fitting-ideal-omega), more-algebra.tex Tag 07ZA (lemma-fitting-ideal-basics, part 3), and curves.tex Tag 0CBY (lemma-etale-local-structure-nodal-family), including its stated hypotheses and the three etale arrows. The pure monomial calculation is written by the worker and is marked as such. No new-node source is needed, because there are no new nodes. No SGA source is used.

Step 1 uses the universal derivation of def-sc-relative-differential-sheaf and the actual minors definition in def-trf-first-fitting-singular-subscheme. I checked that each appears in the cited statement. Assigning the two generator derivatives and differentiating uv-h gives precisely the relation (v,u); taking the one-by-one minors then gives (u,v). These are elementary calculations, with no regular-sequence, injectivity or Noetherian hypothesis imposed on the relation map.

Step 2 uses the exact statements of the existing etale base-change and cancellation nodes to make U -> X_V etale. The relative differential sheaf base-change node gives the canonical pullback isomorphism for arbitrary base change. The formally-etale differential node requires both Omega=0 and H1=0; I corrected the draft's reliance on terminology alone by citing lem-weil-pbc-etale-ring-map-iff-etale-affine, which explicitly supplies both conditions for the affine etale charts. The Fitting node states arbitrary ring-extension compatibility for finitely generated modules, which applies since the morphisms are locally finitely presented. The equality of centres is scheme theoretic. D_U -> D is the stated etale base change of U -> X.

Step 3 uses lem-sfb-graph-cone-gluing only for its definition on affine graph neighbourhoods and its restriction identifications. The flat conormal base-change node explicitly asserts an isomorphism for a Cartesian centre square with flat ambient map; here the ambient map is the base change of D_U -> D. The two further ambient maps are etale base changes. On each small affine neighbourhood of the graph the quotient is the same affine centre, so A -> C/J is surjective. This is exactly the hypothesis of lem-sfb-augmented-etale-associated-graded, whose statement explicitly avoids needing J=IC. I checked the direction of each map and invert the W comparison only after its isomorphism is obtained. No global graph closedness or separatedness assumption is used.

Step 4 takes h=0 on D_U from the centre calculation, so the ambient ring is A[u,v]/(uv), including over a nonreduced A. The coefficient argument proves uniqueness of normal form even over rings with zero divisors: the ideal generated by the monomial uv has only mixed monomials. It proves the precise description of every J^n, the degree-zero part, positive-degree bases and every product. It is an elementary polynomial calculation, not an application of a newly named clause of the item. No further node is hidden here.

Step 5 uses the canonical-map and naturality sentences of the augmented-etale statement and the explicit [a] tensor r formula in the flat conormal statement; these are in the quoted statements, not borrowed from their proofs. Coordinate restriction commutes with the normal-form map term by term. The graph-cone gluing statement supplies the overlap identifications. Thus this step proves algebra, multiplication, coordinate and restriction compatibility, rather than asserting an unexplained transport.

Step 6 uses lem-trf-nodal-family-fitting-singular for its equality of the nonsmooth set and the underlying set of D, then lem-trf-nodal-family-etale-local-model for its three etale maps and a point over each nonsmooth point. I checked every hypothesis against the item: flat, locally finitely presented, pure one-dimensional nonempty geometric fibres, and exactly the completed local nodal rings. The point lands in D_U by the centre equality already proved. This establishes surjectivity of the family of etale maps of centres.

I tested the empty centre, h invertible, h=0, the smoothing uv=t, characteristic two, and nilpotent coefficients such as A=k[epsilon]/(epsilon^2). The presentation uses no division by 2 and makes no assumption that h is a nonzerodivisor. Graph replacement does not assert that normalization commutes with base change. Existing proof dependencies were checked for a path back to the item; none occurs. Every uses entry is in proof_deps, and every citation quote is an exact part of the live node statement. All six proof steps are below 2000 characters, and I also examined each for an inline non-elementary lemma: the non-elementary comparisons are all cited existing nodes, while the two explicit computations are elementary. B-E were checked for self-contained data, correct source tags, genuine decomposition rather than relabelling, hypotheses, edge cases, and compatibility. Generic tools from other units are declared in split_report.tool_uses for the maintainer to judge.

## Unfinished work

None in this stage-1 split. Existing dependencies can themselves remain unsplit, as required by one-level splitting. Validation and delivery results are recorded below after running the required tool.
