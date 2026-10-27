# Stage-1 report: lem-sfb-tame-galois-curve-normalization-smooth

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-tame-galois-curve-normalization-smooth.json`: item, statement, seven proof steps, status split. The statement is unchanged. Mathlib verdict: no declaration found giving all clauses under these hypotheses.
- `citations.json`: one entry for each of the 25 step/node citations, quoting the complete statement verbatim so that the exact hypotheses and conclusion are available together.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. The proof reuses 23 existing nodes; the elementary deductions stay in its steps. `prepare.py` is a sandbox-only preparation script, and `searches.jsonl` is the search command's log; neither is a proposed project file.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for Galois curve normalization, smooth normal curves, and normalization/residue degrees found no project declaration stating every clause. The regularity results for smooth schemes alone do not attach this item. No compiler or Lake command was run.

## WANTED

None for this split. The inherited blueprint provenance mentions a previously wanted local de Jong PDF, but this item's complete local argument is supported by the available Stacks sources. No new assertion is based on that unavailable PDF.

## Corrections and scope

The imported statement is retained, including imperfect fields, a possibly empty branch scheme, degree one, and no projectivity hypothesis. The missing content was the complete proof. I supplied the localization of the normalization before applying DVR ramification, proved closedness rather than assuming it, and separated normality of a residue extension from its separability. In particular, a finite Galois function-field extension does not by itself have separable residue extensions. The invertibility of its degree is used to exclude the inseparable part.

The proof continues the inherited local branch-point step of the tame normalization route. I read the current chapter and the main-20261015 unit/direct-image proof. This is an auxiliary local algebra/curve input, not a change to the unit's alterations or coefficient route. The existing `blueprint.from.node = null` and the entire inherited `via` chain are preserved, consistently with the output of `blueprint_refs.py ancestor`. Its detailed `from.place` and the split report identify the local de Jong normalization step it serves. Whole-blueprint searches for Galois normalization, separable degree/tower/transitivity, 09EB and 0B8Y found no additional blueprint node stating this item.

## Not duplicates

No new nodes. In particular I reused `lem-sbc-dvr-galois-normalization-ramification-dvd` (09EB), `lem-exc-dvr-residue-normal-action` (09ED), `lem-exc-normal-field-degree-factors`, `lem-zl-separable-permanence` (09HB), and `lem-sfb-normal-curve-separable-point-smooth` (0B8Y). The more general separability search actually found `Algebra.IsSeparable.trans`; the DAG search then found its existing leaf `lem-zl-separable-permanence`, so no redundant leaf was added.

## Review by Q61

I read the item's two principal sources in the local Stacks TeX: more-algebra.tex Tag 09EB, `lemma-galois-conclusion`, including its DVR/Galois hypotheses and the formula `[L:F]=nef`; and varieties.tex Tag 0B8Y, `lemma-regular-point-on-curve`, including the separable residue-field proviso on its smoothness clause. For the connecting steps I read algebra.tex Tag 0307, `lemma-integral-closure-localize`, Tag 00PD, `lemma-characterize-dvr`, and Tag 00U3, `lemma-etale-over-field`; fields.tex `lemma-irreducible-polynomials`, `lemma-finite-purely-inseparable`, `lemma-separable-first`, `definition-insep-degree`, `lemma-separable-degree`, and Tag 09HB `lemma-separable-permanence`; more-algebra.tex Tag 09ED `lemma-galois-galois`; and descent.tex Tag 036U `lemma-smooth-smooth-local-source`. There are no new nodes requiring separate source reviews.

For step 1 I opened the four cited statements: finite morphisms are affine with finite section algebras; the etale algebra lemma gives an actual finite product of finite separable fields; the closed immersion is a closed topological embedding; and the residue-field lemma gives the required isomorphism. Thus the field attached to a point of D is indeed kappa(x), not a different residue extension. Closed points in a finite product of fields follow by projecting the product idempotents; no extra finiteness theorem is hidden here.

For step 2 I read the curve affine local-model statement, which supplies a Noetherian domain of dimension exactly one and the compatible stalk identification. The general smooth-scheme regularity node has no perfect-field or dimension assumption. The regular-dimension-one DVR node supplies precisely the implication needed after those hypotheses have been established. The affine function-field node identifies Frac(R) with F; the elementary inclusions R subset R_p subset Frac(R) give Frac(R_p)=F. I did not infer normality of C from normality of Y.

For step 3 the normalization definition supplies the affine integral closure B, while the finite-morphism definition supplies its finite R-module structure. Since q contracts to the maximal p, B/q is a finite-dimensional domain over R/p, exactly the hypothesis of the cited finite-dimensional-domain field lemma. The specialization argument upgrades affine closedness of y to closedness in Y, without assuming that all affine-closed points in arbitrary schemes are globally closed. Only after that do I apply the curve local-model node to Y and its affine chart.

For step 4 I read both localization nodes in full. The integral-closure node applies to R into L with S=R minus p; S consists of nonzero elements because R embeds into F and L, so localizing L changes nothing. The localization-prime node gives both the localized local-ring isomorphism and the induced residue isomorphism with the same scalar maps. Consequently the DVR divisibility node is applied to the integral closure of A in L, with its own maximal-ideal prime, not to a merely similar normalization. The localized prime is explicitly maximal because its quotient is the field B/q, unchanged by inverting S. Its hypothesis [L:F] divides n is met by n=d, and it states residue-degree divisibility without requiring an invertible n.

For step 5 I also opened the existing algebraic-closure existence leaf (09GT) and used its existence clause to supply the closure required by the degree-factor theorem. The residue-normality node has exactly this DVR, finite normal separable field extension, integral closure, and maximal prime as input. It states normality even when the residue extension is inseparable. That verifies the extra hypothesis of the existing characteristic-p normal-field degree-factor leaf. Its stated formula gives the p-power factor dividing f and hence d; invertibility forces this factor to be one. The relative separable-closure definition states that its elements are separable. In characteristic zero I wrote the leading-coefficient derivative argument and used the existing irreducible-derivative criterion rather than claiming perfection of the base. Every non-elementary input of this step is therefore a cited statement.

For step 6 I checked that the existing separability-permanence node states separable algebraic transitivity, and the degree-multiplicativity node supplies finiteness as well as the formula. The normal-curve smoothness node assumes a closed point, an integrally closed local domain, and a finite separable residue field. Closedness was proved in step 3, normality is in the item's hypotheses, and residue separability and finiteness were established in steps 1 and 5. No assumption is missing.

For step 7 the pointwise clause of the etale-source smoothness node states exactly that the smoothness of a morphism at the image point is equivalent to smoothness of its etale composite at the source point. Thus it applies on the assumed etale complement, and no assertion about normalization commuting with a general base change is used. Smoothness on a cover is its local definition, as recorded in the cited smooth-morphism definition. This last cover includes every point, not merely closed points.

The generic off-unit tools are explicitly declared in `split_report.tool_uses`: the closed-immersion residue-field isomorphism, smooth-scheme regularity, localization residue comparison, DVR Galois divisibility, DVR residue normality, and etale-source smoothness. Each is used as its stated general theorem; no unit-specific geometric route is replaced. Existing Mathlib leaves and closed declarations are reused as such.

I checked delivery-errors B through E against these files: no new definition, no statement-only node with a hidden proof, no fabricated search, no node relabeling a clause, and no new node at all. The proof has actual algebraic reductions, and its proof_deps are exactly the union of uses. Every cited node was opened, and every citation quote is copied from its statement rather than from its proof. All seven steps are below 2000 characters; the longest is 1180 characters and makes its characteristic-p and characteristic-zero cases explicit.

For small cases I checked the empty branch scheme (the etale-complement step covers all Y), d=1 (f divides 1 and the separability argument allows exponent zero), characteristic zero, and an imperfect positive-characteristic base. The latter is precisely why I did not identify normal curves with smooth curves before proving separable branch residue fields. Ramified points with f=1 are allowed: the proof never assumes e=1. I found no statement dispute to repair.

## Unfinished work

None in the authorized stage-1 scope. Existing unsplit dependencies are cited by statement and remain their own future items. The server dry-run result is recorded below; delivery follows the last passing dry run.

## Validation

The first server dry run exited successfully: `OK (not pushed)` at `78ee4f1100f`, with server preflight passed. After that pass I added the explicit maximal-quotient calculation and the existing algebraic-closure existence citation. The required dry run is executed again on these amended files before the push.

The amended proof also passed server preflight: `OK (not pushed)` at `7a7c01e662e`. The final report corrects the measured longest-step length to 1180 characters; the proof and citations are unchanged after that pass.

## Returned delivery repair

The interrupted push reached independent review as branch head `983e7c3b227`. The return of 2026-10-23 04:28 UTC says the reader approved the split but landing refused it because completion in the project's DAG had not been promoted to the live DAG the queue reads. It directs rebasing onto the current DAG, rereading changed citations, and pushing again. This is a landing-state failure, not a mathematical objection or a request to change the statement.

On resumption I verified that the interrupted delivery process had exited and read the server's return before issuing another delivery. I compared every one of the 25 quoted citation statements against the current repository; all are unchanged, as is the item's statement. Thus there are no changed dependency statements requiring a revised proof. I retained the seven proof steps, all previous search records, citations and source review. The delivery tool now packages these files against its freshly fetched current `origin/sheaf-dag`, preserving current maintainer fields. The required server dry run precedes the new push. No repository, launcher, Lean file, or maintainer promotion metadata was edited.


## Repair of returned head f9bd2b408a1

The current return is the entry dated 2026-10-23 05:21 UTC, for head `f9bd2b408a1`. Like the earlier return, it records the independent reader's approval and a refusal to land because the side completion was not promoted to the live queue DAG. I have not treated either approval as a completed landing or altered promotion metadata.

I resumed the retained sandbox rather than reconstructing the delivery. Before editing, the required server dry run fetched the current `origin/sheaf-dag`, rebased the split through the delivery tool's field-preserving overlay, and passed preflight at `62c97e0c388` (`OK (not pushed)`). I then compared the sandbox item against the current read-only DAG field by field. Its statement, statement notions, source, chapter/unit and blueprint provenance are unchanged; the retained differences are the seven-step proof, its dependency list, proof origin, split status, logged searches and split report. No current maintainer metadata is replaced by this repair.

I reopened all 23 distinct cited nodes and checked all 25 step/node quotes against their current statements: every full quoted statement is still identical. The review above therefore still applies step by step, including the closed-point local-model hypotheses, the localization scalar maps, the normal residue extension, and the separable-residue-field proviso in the curve smoothness criterion. There is no changed cited statement requiring a mathematical alteration to the already approved proof. I reread the local source statements 09EB, 09ED, 0B8Y, 0307, 00PD, 00U3, the field separability statements, and the source-local smoothness statement; none calls for an additional hypothesis on this assembly. The step lengths remain 669, 685, 796, 962, 1180, 581 and 627 characters. No hidden long step, new node or new Mathlib leaf is introduced.

This report and the item's split summary now explicitly identify the current return and the completed dependency audit. The final dry run is run after these amendments, and the push is made only after that invocation exits successfully. Rebasing is performed by the required delivery tool against the freshly fetched current DAG, with current maintainer fields preserved. The maintainer's live-promotion action remains outside the worker's authorized files.
