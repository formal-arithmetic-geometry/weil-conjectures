# Stage-1 delivery: lem-per-bounded-genus-rational-model

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-bounded-genus-rational-model.json`: item, statement, split into seven proof steps; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-surface-modification-h1-exact.json`: statement-only subsidiary lemma, unsplit; no Mathlib match. Stacks 0AXF.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-normal-modification-extension.json`: statement-only subsidiary lemma, unsplit; no Mathlib match. Stacks 0B3X and 0BFN with the normality argument in 0B4P.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-nagata-surface-normalized-domination.json`: statement-only subsidiary lemma, unsplit; no Mathlib match. Stacks 0BBT and 0BFT, convention 0BBS.

`citations.json` quotes the actual full statement of every node cited by every step; in particular the multi-clause exact-sequence and domination citations include all clauses being used. It is a sandbox validation artifact. No Lean was written or compiled. Only sandbox files were written, and no git command was run in the shared repository.

## Attachments

None. Searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item tag and by bounded genus, rational singularities, reduction to rational singularities, normalized blowups and modifications. There is no declaration covering the item or the three new statements. Chow modifications and unrelated ring-theoretic modifications do not assert these claims. The upstream master checkout was also read as reference, not treated as proof evidence.

## WANTED

None. The relevant Stacks source files and tag-to-label index are available locally.

## What was wrong or incomplete

The earlier sandbox had the unchanged unsplit item, `research.py`, `search-results.json` and `searches.jsonl`; it had no report and no completed proof. Retained these artifacts and read the search results rather than rerunning them. Retained the item's inherited searches and appended the already logged Q15 item queries. Each new node records the exact queries and output belonging to its concept in `search-results.json`; all were actual invocations of the unmodified launcher msearch command. Each concept has LeanSearch, LeanFinder, Loogle and grep searches, with a second semantic phrasing. All services in these saved results succeeded; no failed request was represented as a negative result.

The mathematical statement is unchanged. The inherited item had doubled TeX command backslashes; these were corrected as typography only, without adding hypotheses, removing cases or changing a conclusion. The condition on closed points of local dimension two is retained. It makes the rational-singularity predicate well-typed with its dimension-two definition. The Stacks source's shorthand “every closed point” is not used to introduce a different predicate in other dimensions.

A tempting reuse, `lem-per-excellent-surface-normalized-domination`, requires excellence. The item assumes only Nagata, so that lemma cannot be applied. The new domination statement is the Nagata theorem actually stated in 0BBT, not an assertion that Nagata implies excellent.

The source finishes by dominating its maximal model and invoking rationality propagation. Here the same domination is taken immediately after choosing the maximal model: 0AXF and length additivity show that the dominating tower is maximal too. Apply the source's identical local-modification test to that tower. This retains the maximality, globalization and normalized-domination route and removes the need for a separate local-dimension check in the propagation argument. It does not replace a unit step or assume a resolution theorem.

## Unfinished work

None for this one-level split. The three new nodes intentionally have no proof and join the unsplit queue. Their statements are independent geometric/cohomological tools, not clauses asserting the item's rationality conclusion. Mechanical validation and delivery results are recorded below after running the required commands.

## Not duplicates

lem-per-nagata-surface-normalized-domination vs lem-per-excellent-surface-normalized-domination: the existing theorem assumes an excellent normal surface; the new theorem assumes only a normal Nagata local surface and cannot be deduced from the excellent specialization under the item's hypotheses.

lem-per-nagata-surface-normalized-domination vs lem-per-excellent-normalized-blowup-tower: the existing statement gives geometry of a prescribed tower over an excellent scheme; the new statement constructs a tower dominating an arbitrary given modification over a Nagata local surface.

lem-per-nagata-surface-normalized-domination vs lem-per-normal-surface-exceptional-curves: the existing statement supplies finite exceptional-curve data under excellence, not a dominating tower over a merely Nagata base.

lem-per-nagata-surface-normalized-domination vs lem-per-normalized-surface-graph-exceptional-injection: the existing statement compares exceptional curves of a normalized dominating graph of excellent surfaces; it does not give a normalized point-blowup tower over a Nagata base.

lem-per-nagata-surface-normalized-domination vs lem-per-surface-resolution-normalized-refinement: the existing theorem starts with a regular resolution and constructs a regular endpoint; the new theorem starts with any proper birational model and asserts domination, without a regularity hypothesis or conclusion.

lem-per-nagata-surface-normalized-domination vs lem-per-bounded-genus-rational-model: the item starts with bounded cohomology and must prove rationality; the new lemma has no boundedness or rationality assertion, and instead dominates an arbitrary specified model. Its domination map is what transports maximal cohomology length to the tower.

lem-per-local-normal-modification-extension vs lem-per-local-normalized-blowups-globalize: the existing statement only globalizes prescribed finite normalized point-blowup towers. The new statement extends an arbitrary proper normal modification which is an isomorphism on the punctured local spectrum; an arbitrary modification need not be a prescribed tower.

lem-per-surface-modification-h1-exact vs pqf-lem-leray-lowdegree: the existing generic Leray sequence has a possibly nonzero H2 term and no assertion of global generation of the first higher image. The new geometric surface lemma supplies a short exact sequence and finite-support/global-generation assertions. These require the surface geometry in 0AXF and are not a two-line specialization of the generic spectral sequence.

## Review by Q15

I read `resolve.tex` at 0B4P (`lemma-reduce-to-rational`), its definition 0B4N, the entire statement and proof of 0AXF (`lemma-exact-sequence`), the normalized-blowup definition 0BBS, the statement and proof of 0BFT, and the statement and the geometric setting of 0BBT. I also read `limits.tex` at 0B3X (`lemma-modifications`) and 0BFN (`lemma-modifications-properties`), and `coherent.tex` at 02KH (`lemma-flat-base-change-cohomology`) and 01XB (affine vanishing). The chapter and unit records were read; this is an auxiliary surface-resolution input in the ancestry of `lem-per-artin-gabber-affine-curve`, rather than the key Fourier unit statement. No chapter, unit or target was changed.

For step 1, I opened `def-per-rational-surface-singularity` and `def-weil-pbc-module-length`: the former quantifies over exactly the proper integral normal birational models being chosen and gives a single finite bound for all lengths. The latter makes the bounded set a subset of the natural numbers. Choosing its largest attained value is elementary; I did not create a node for finite integer maximization or for length-zero implying zero.

For step 2, I checked that the new domination lemma takes an arbitrary prescribed modification and gives a map from its tower endpoint to that modification. The new 0AXF statement applies to a diagram with both composites proper over the same two-dimensional normal Noetherian local base and with the lower model normal; it supplies the injection used here. `lem-weil-pbc-length-additive-short-exact` explicitly states additivity even allowing infinite length, while the bound in this application ensures finiteness. No excellence or projectivity assumption is slipped into the invocation. Length comparison makes the tower endpoint attain the same maximum.

For step 3, the same exact-sequence statement supplies not just the short exact sequence, but global generation of the final higher-image sheaf. I checked that the proof uses this clause: zero global sections alone would not force an arbitrary sheaf to vanish. The length-additivity node supplies the displayed equality; the length definition directly proves that a nonzero module cannot have length zero. `lem-weil-pbc-proper-composition` says exactly that composites of proper maps are proper, so the additional model is in the bounded collection. All function fields remain identified by the composite isomorphism, a direct fact about isomorphisms.

For step 4, the new domination statement explicitly gives Nagata affine coordinate rings and normality. `lem-weil-pbc-nagata-localization` explicitly supplies Nagata and Noetherian localizations. At a tested point the dimension-two hypothesis is from the item, not inferred from a dimension formula over a noncatenary base. For a nonclosed point of its local spectrum the height is zero or one. I opened `lem-sc-normal-dim1-dvr`, which assumes exactly a one-dimensional Noetherian normal local domain, and `lem-per-normal-modification-codimension-one`, whose first two clauses cover the generic point and the DVR points. The local modification is proper with normal, hence reduced, source, as required. These clauses justify the punctured-spectrum hypothesis needed by the extension lemma.

For step 5, I checked the extension statement against 0B3X and 0BFN: the complement of the closed point is quasi-compact because the scheme is Noetherian; the proper maps involved are of finite presentation over a Noetherian base. Its additional normality assertion is exactly the source's local-ring argument in 0B4P: outside the point the scheme is unchanged, and above it the local rings are the local rings of the prescribed normal local model. Integrality follows from this normal local description and the common dense generic point; no unsupported normalization or finiteness of normalization is needed for this extension. The resulting global model is a proper normal modification, so the vanishing from step 3 applies.

For step 6, I opened the actual statements of `lem-weil-pbc-localization-flat`, `def-weil-flat-morphism`, `lem-pc-flat-base-change-cohom`, `lem-pc-affine-higher-direct-image-cohomology-vanishing` and `pqf-lem-leray-lowdegree`. The first applies to the affine localizations defining the map from the local spectrum; the second defines the required flatness stalkwise. The base-change lemma gives the sheaf isomorphism, not just a cohomology formula over two affine bases. Its morphism is the proper extension g, hence qcqs, and its coefficient is the quasi-coherent structure sheaf. After its first higher image vanishes, the affine higher-image vanishing statement at p=1,q=0 kills H1 of the ordinary pushforward. The exact Leray sequence then has zeros on both sides of H1(Y,O_Y). Thus this step really proves the source's “clearly” inference, without confusing a definition of higher images with a base-change theorem. These off-unit statements are declared generic tools in `split_report.tool_uses`.

For step 7, the vanishing is for every normal local modification, exactly the quantifier in the rational-singularity definition. The endpoint's other properties were already provided by the domination construction. I kept the empty tower, the identity modification and the case of bound zero: with bound zero step 3 still works and no strict increase of length is asserted. Testing the three new statements with identity maps gives a zero final term in the exact sequence, the identity global extension, and an allowed tower of length zero. The extension has the necessary punctured-isomorphism hypothesis and is not falsely asserted for an arbitrary proper map with extra components. No assertion that normalized blowups are finite or proper without the Nagata hypothesis is made; it is their normalization maps that are finite.

Before creating the nodes I searched the whole DAG by the tags and concepts and ran `tools/blueprint_refs.py search` for rational singularities, modification, normalized blowups, Leray, closed points and the tags 0AXF, 0B3X and 0BBT. I opened the related statements listed above. No imported blueprint node states a new lemma. The same-tag existing statements are distinguished in the Not duplicates section, rather than bypassing the excellent/Nagata distinction. All three new nodes introduce their own objects, carry statement dependencies, have an exact ancestor and nonempty provenance place, and contain empty proofs and proof-dependency lists. Saved Mathlib hits were read: normalization constructions and rational-map representatives do not give finite Nagata normalization or domination; local-spectrum Hom descriptions do not extend modifications; cotangent and group-cohomology exact sequences do not give the surface coherent result. No one-line specialization was found.

I checked B–E against the actual statements and sources: no proof is hidden in a new statement, no new node merely relocates local rationality, no used clause is taken from a cited proof rather than its statement, and no non-elementary step is left marked elementary. All seven steps are shorter than 2000 characters. The corrections made in this pass were completing the formerly empty proof, replacing the unusable excellent domination candidate by the Nagata theorem, and expanding the globalization/local-cohomology inference. There is no mathematical statement dispute.

## Validation

The standalone server `review_split` check passed before packaging. The required full dry run and push are recorded after completion.
