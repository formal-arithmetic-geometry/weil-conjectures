# Stage-1 report: lem-sfb-common-regular-surface-resolution

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-common-regular-surface-resolution.json`: item, statement unchanged, four-step split of Stacks Tag 0C5S.
- `dag/nodes/sec-six-functors-basics/lem-sfb-surface-rational-map-point-resolution.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep. This is elimination of indeterminacy for a map to an arbitrary proper target, not simultaneous resolution of two surfaces.
- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-birational-surface-factorization.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep. This factors an already supplied proper birational morphism.
- `citations.json`: verbatim statements for every citation of every item step.
- `searches.jsonl`: actual search-command log; all services answered for these searches.

Two new nodes, zero new Mathlib leaves. Existing leaves for finite-type Noetherianity, proper composition and proper-over-separated are reused.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id, the blueprint tag, regular/birational surfaces, point blowups, and rational-map resolution. The hits on rational maps, affine birationality and unrelated regular local rings do not prove the item or either new theorem. No unfinished project proof is treated as an attachment. Read the Mathlib rational-map and birationality source at the locations returned by the search command: representatives and partial isomorphisms are not extension after point blowups or morphism factorization.

## WANTED

None. All mathematical sources used for this split are present locally.

## Problems found and corrections

The imported statement is faithful to Tag 0C5S, including the specified identification: the proof there starts with the given invertible rational map, not an arbitrarily chosen birational correspondence. No hypothesis or conclusion has been changed.

The item was unsplit and supplied no proof dependencies. The split exposes separately the elimination-of-indeterminacy theorem (0C5H) and the proper-birational-morphism factorization theorem (0C5R). Neither new statement repeats a clause of the item: the former needs only one surface and an arbitrary proper target; the latter assumes the proper morphism that must first be constructed in the item. In particular, we do not replace the target by another common-resolution lemma.

The blueprint ancestor command reports `None` for this item's existing `blueprint.from.node`. Kept that inherited value and its full provenance chain, with precise additional source places in each new node; did not invent a blueprint ancestor. Whole-blueprint searches for regular surfaces, rational maps, birationality, 0C5H, 0C5R and 0C5S found no matching theorem. The generic blueprint proper-target-extension corollary supplies an arbitrary admissible blowup, not a tower of reduced point blowups. The unit's direct-image/alteration prerequisite is retained; no unit or chapter change is made.

## Unfinished work

No part of the assigned one-level split is left unfinished. The two new statement-only nodes remain unsplit, as required. In particular the substantial conormal and contraction argument inside 0C5R belongs to the future split of that theorem, not an unmentioned assumption in the proof of the present item.

## Not duplicates

lem-sfb-surface-rational-map-point-resolution vs lem-sfb-local-surface-maximal-blowup-geometry: the existing node describes one blowup of a two-dimensional regular local scheme; the new node extends a prescribed dense-open map to an arbitrary proper target after a finite tower.

lem-sfb-surface-rational-map-point-resolution vs lem-sfb-dvr-nodal-chart-blowup-calculus: the existing node calculates the specific nodal models xy=pi^n and their charts over a DVR; the new node resolves indeterminacy of arbitrary maps from regular surfaces over any base.

lem-sfb-surface-rational-map-point-resolution vs lem-sfb-regular-point-blowup-geometry: the existing node gives integrality, regularity and properness of a supplied single point blowup; it does not construct any tower on which a rational map extends. Those geometric properties are the preservation clauses of the new indeterminacy theorem, not its main assertion.

lem-sfb-surface-rational-map-point-resolution vs lem-per-local-surface-maximal-blowup-geometry: the existing node describes a single maximal-ideal blowup of a regular local surface, with its exceptional curve; the new node constructs a tower extending a given map to an arbitrary proper target.

lem-sfb-surface-rational-map-point-resolution vs lem-per-regular-point-blowup-acyclic: the existing node gives geometry and R^1 vanishing of one supplied point blowup; the new node constructs a rational-map resolution and makes no cohomology assertion.

lem-sfb-surface-rational-map-point-resolution vs lem-per-surface-tower-discard-regular-centers: the existing node changes a normal excellent surface tower while preserving neighbourhoods of its singularities; it does not extend a specified map to a proper target. The new node starts with a regular surface, without excellence.

lem-sfb-surface-rational-map-point-resolution vs lem-per-surface-point-blowup-geometry: the existing node describes a single blowup, including strict-transform formulas, under excellence and ampleness; it gives no indeterminacy elimination, and the new node assumes neither excellence nor an ample sheaf.

lem-sfb-surface-rational-map-point-resolution vs cor-nagata-conrad-proper-target-extension: the latter gives an admissible blowup in an arbitrary ideal, not domination by a finite tower of reduced closed point blowups through regular surfaces. Specializing it does not yield the new statement in one line.

lem-sfb-surface-rational-map-point-resolution vs lem-sfb-regular-point-blowup-domination: the existing node dominates a supplied modification with finite regular closed-point support; it does not extend rational maps across codimension-one points or construct such a modification from a map to a proper target.

lem-sfb-proper-birational-surface-factorization vs lem-sfb-regular-point-blowup-domination: domination produces a new tower mapping to the given source; factorization identifies the supplied proper morphism itself as a point-blowup composite. Domination does not give that identification.

## Review by NI

I read the item against `literature/stacks-project/resolve.tex`, Tag 0C5S (lemma-birational-regular-surfaces), including its proof. The four steps preserve the exact rational map appearing there. I also read 0C5H and its proof: extend across codimension one, extend after a modification, and dominate the remaining finite set of regular surface points by point blowups. I read 0C5R and its proof, including the descent through the last point blowup, the exceptional-curve conormal argument, and induction on contracted curves. Those are the precise two statements deferred as new nodes. I did not infer factorization merely from domination.

For the preservation clauses of the new indeterminacy node, I read resolve.tex 0AGR and 0AGQ, divisors.tex lemma-blow-up-integral-scheme (02ND) and lemma-blowing-up-projective (02NS), and morphisms.tex lemma-finite-type-noetherian (01T6). The reduced closed point ideal is finite type on a Noetherian scheme and is nonzero on an integral surface. Its blowup is integral and proper and stays Noetherian. At a two-dimensional regular centre the regular-parameter blowup has regular local rings of dimension two at closed exceptional points (0AGR); outside the centre nothing changes. A closed centre of local dimension one is Cartier and its blowup is an isomorphism. Thus global dimension two is retained even when the original surface has closed points of local dimension one. These are general blowup facts accompanying 0C5H, not an extra excellence, perfectness, algebraic-closure or projectivity assumption. The new factorization node is the statement of 0C5R, with birationality written out by a dense-open isomorphism and the usual convention of factorization up to isomorphism, including length zero.

Step 1 uses exactly `def-weil-proper-morphism` (proper implies finite type and separated) and the statement of `lem-weil-pbc-finite-type-over-noetherian` (finite type over a Noetherian scheme gives a Noetherian source). I opened both. The base S has precisely the Noetherian hypothesis that this leaf requires, and both structural maps are proper by the item. Constructing f from the supplied open isomorphism is elementary.

Step 2 uses exactly the new indeterminacy theorem. Its source is T_1, now verified Noetherian, integral, regular and dimension two; its target T_2 is proper over the same S. Its open U_1 is dense and the map is over S. The cited statement explicitly returns the regular integral Noetherian surface W, the proper point-blowup projection, and agreement on the entire inverse image of U_1. The latter is nonempty, hence dense in integral W. No properness of g is assumed at this stage.

Step 3 uses the full statements of `lem-weil-pbc-proper-composition` and `lem-weil-pbc-proper-over-separated`, which I opened. The first applies to W -> T_1 -> S. The second has h:W -> S proper, q:T_2 -> S separated from Step 1, and q g = h because g is an S-map. It therefore actually states the required properness of g. Birationality needs no extra theorem: on the displayed dense opens it is the composite of the isomorphism p with the prescribed alpha. We do not need an assertion that the entire inverse image of U_2 is this open.

Step 4 uses exactly the new proper-birational factorization statement. Its two surfaces and the morphism satisfy every hypothesis by Steps 1--3. This is why 0C5R is applicable here but would not have been applicable to the initial rational map. Composing every intermediate tower map with T_2 -> S supplies its S-structure; the identification of its top with W is over T_2, hence over S. The restriction formula from Step 2 proves preservation of the chosen birational identification. These final observations are elementary assembly, not new lemma nodes.

I checked B--E against these files and sources: both new nodes are self-contained statements with empty proofs and proof dependencies; all notions have defining nodes or explicit inline meanings; every item citation is backed by its verbatim statement in citations.json; no proof-of-a-node construction is used; every non-elementary operation is one of the cited statements. The whole-DAG and blueprint searches exclude duplicates, and the same-tag comparisons above distinguish every existing source match. All recorded Mathlib queries were actually run through msearch.py and their hits read, including the second phrasings; none states the required geometric theorem. All four proof steps are shorter than 2000 characters.

Small cases checked: alpha extending to a global isomorphism permits both towers to have length zero; a single point blowup against its base gives a tower of length one on one side and zero on the other; an already global proper birational map uses a zero-length initial tower and the factorization theorem on that map; arbitrary residue fields cause no requirement that a closed point be rational; S need not be separated or excellent. Integral dimension-two hypotheses exclude empty and zero-dimensional schemes. The map-to-proper-target hypothesis is retained in the new indeterminacy theorem, and regularity on both sides is retained in the factorization theorem, so neither new statement incorrectly promises singular-surface resolution without excellence. No SGA source is used.
