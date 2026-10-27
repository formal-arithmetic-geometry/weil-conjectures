# Stage-1 report: lem-sfb-quasifinite-closed-nowhere-dense-image

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-quasifinite-closed-nowhere-dense-image.json`: item, statement; split in six steps using existing DAG nodes. Mathlib verdict: no match for the item.
- `citations.json`: 11 step/node entries, each quoting the cited statement verbatim.
- `report.md`: this report.
- `searches.jsonl`: six searches made through the required msearch command; retained the item's inherited seven search records as well.

There are 0 new nodes and 0 new Mathlib leaves. No Lean was written or compiled. The shared repository and launcher were only read, apart from invoking their prescribed remote checking and delivery interfaces.

## Attachments

None. Searched live `lean/WeilConjectures/` for the exact blueprint id and for nowhere-dense/quasi-finite notions. The existing closed affine-factorization declaration `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_isQuasiFinite_affine` in `QuasiFiniteAffineOpenInFinite.lean:52` supplies an existing dependency, not the item. Topological stratification declarations and generic-fibre dimension lemmas do not state the image assertion.

## WANTED

None. All sources used are present locally.

## Corrections and route

The imported statement is correct and unchanged, as are its statement dependencies. Stacks morphisms.tex Tag 03J2, label lemma-image-nowhere-dense-quasi-finite, states exactly the assertion, including the distinction between nowhere dense and closed image. The node initially had no proof. There is no repair note for this item and no earlier sandbox split/report to resume.

I read SETUP's three levels, GOAL, the chapter and unit records, the latest blueprint's six-functors-basics/sk-thm-sf-ctf-stability unit and its direct-images proof. The inherited blueprint ancestry has from.node=null and blueprint_refs.py ancestor prints None; these inherited fields are preserved. The split supplies the last prerequisite named in from.place, rather than replacing a six-functor step. The 03GU affine factorization is declared in split_report.tool_uses as the generic scheme-theoretic tool taken by the source's own proof. The other cross-unit statement dependencies used in the proof are existing Mathlib leaves. The finite-image theorem is already in this unit.

## Not duplicates

No node was created. Searches of the entire DAG for 03J2, 03GU, 03J0, 03HO, the factorization and nowhere-dense keywords, together with blueprint_refs.py searches for 03J2 and quasi-finite nowhere dense, led to reuse of `lem-weil-pbc-quasi-finite-affine-open-in-finite` (03GU) and `lem-sfb-finite-image-nowhere-dense` (03HX). The latter assumes finite, whereas the item assumes quasi-finite. `lem-weil-pbc-quasifinite-fp-finite-factorization` additionally assumes finite presentation and so was not applied. The small topology arguments of 03J0, 03HO and 03HP are written in elementary steps rather than manufactured as new nodes. The current blueprint has no second node stating this item.

## Review by Q14

I checked the node and proof against delivery-errors B through E, with Stacks morphisms.tex 03J2 open. I read 03GU (lemma-quasi-finite-affine) and the existing affine-factorization node and Lean declaration, the finite-image statement and proof node for 03HX (lemma-image-nowhere-dense-finite), topology.tex 03J0 (lemma-image-nowhere-dense-open), 03HO (lemma-nowhere-dense), and 03HP (lemma-nowhere-dense-local). For the affine reduction I also read morphisms.tex 01T2 (lemma-locally-finite-type-characterize), 01SH (lemma-morphism-affines-affine), and 01S7 (lemma-affine-separated). All sources are Stacks or the current blueprint, with no SGA route.

Step 1 takes finite type and isolated fibres from pqf-def-quasifinite, and the finite affine cover of the inverse image of an affine open from def-weil-finite-type-morphism. Both statements explicitly say these things. The restriction of the closed T is closed, and every open contained in it is an ambient open contained in T, so its empty interior is a direct topological argument. There is no assumption that X or Y is globally affine or quasi-separated.

Step 2 is a hypothesis check rather than an unproved assertion that arbitrary restrictions stay quasi-compact. I read the complete statements of lem-weil-pbc-lft-affine-pairs, lem-weil-pbc-morphism-affine-schemes-affine, lem-weil-pbc-affine-morphism-permanence, def-weil-finite-type-morphism, def-pc-scheme-fibre and pqf-def-quasifinite. The affine-pair criterion applies both ways and passes local finite type to the restriction because all the affine pairs are also pairs in the original schemes. The restriction has affine source and target, so the affine-map theorem applies and permanence (3) gives quasi-compactness. Their conjunction is finite type. The fibre homeomorphism in def-pc-scheme-fibre explicitly identifies the set-theoretic subspace fibre with the scheme fibre; a singleton isolated in the original fibre remains isolated in its open subspace. This verifies exactly the finite-type and isolated-point hypotheses for quasi-finiteness, without assuming finite presentation or using a definition node for a permanence theorem.

Step 3 uses only the statement of lem-weil-pbc-quasi-finite-affine-open-in-finite. Its source and target are the affine schemes chosen in step 1, and step 2 proves its quasi-finiteness hypothesis. Its conclusion gives every piece used: affine Z, open immersion j, finite pi, and the equality of the composite with the restriction. It is a generic 03GU tool; it neither restates this item nor assumes its conclusion.

Step 4 uses the actual homeomorphism onto an open subset supplied by def-weil-open-immersion. The proof in topology 03J0 is expanded: an ambient open inside the closure intersects that open image in an open contained in the closed nowhere dense image of T, so that intersection is empty; it then cannot contain any point of the closure. Thus the closure C is nowhere dense. This uses no unrecorded comparison theorem and is elementary; in particular j(T) is not claimed closed in the ambient Z.

Step 5 uses the full statement of lem-sfb-finite-image-nowhere-dense, which gives both closedness and nowhere denseness for the image of a closed nowhere dense subset under a finite map, without surjectivity, flatness, Noetherianity or reducedness. Those precise hypotheses hold for pi and C. Taking the closure of the subset g(T) remains inside the closed image pi(C), proving the desired conclusion. I checked that no dependency cycle is introduced by reading the finite-image node's proof dependencies: it uses its section-cover lemma and does not depend on the present quasi-finite item.

Step 6 cites no non-elementary assertion. Its induction on the finite number of affine pieces includes the empty union, and the two-set proof is written explicitly using complements of closed sets. The gluing argument uses the displayed local closure identity on an open subspace; a neighbourhood can be intersected with that open, which proves the identity directly. An ambient open contained in the closure consequently meets every affine chart in the empty set and is empty. Thus it proves exactly nowhere denseness, with no claimed closedness of f(T).

I read the Mathlib hits rather than treating them as matches. The semantic search returned `Topology.IsInducing.isNowhereDense_image`; I read GDelta/Basic.lean:200-262. It applies to an inducing map, a hypothesis unavailable for an arbitrary quasi-finite morphism (e.g. a disjoint union of two copies of a point mapping to a point). Constructible-image, dominant-to-image and quasi-finiteness declarations do not assert nowhere denseness. Two distinct semantic phrasings, Loogle, LeanSearch and grep were actually run through msearch; exact queries/results are retained in the log and node. There is no unavailable search mislabelled as no match.

Small cases checked: T empty and empty source/target give empty image; the induction also permits an empty cover. A closed point in the affine line under the identity is nowhere dense, as is its finite-map image. For the open immersion A^2 minus the origin into A^2, the punctured x-axis is closed and nowhere dense in the source but its image is not closed, showing why the closure argument is needed. Without quasi-compactness, infinitely many copies of A^1 mapping identically to A^1 and the closed subset consisting of one closed point in each copy can have a dense image (over an infinite algebraically closed field); hence the finite cover is essential and is justified by finite type. No statement dispute or hidden extra hypothesis was found. No step exceeds 2000 characters, no new statement-only node contains a proof, and proof_deps is exactly the union of uses. Every cited statement was opened and copied verbatim into citations.json, satisfying the C4 check rather than relying on its source tag alone.

## Unfinished work

None in the stage-1 split. The first server review_split and delivery dry run both passed. After correcting the report's affine-factorization declaration line from 49 to 52, the final dry run is repeated before direct delivery; the delivery commit is reported by the prescribed tool.
