# Worker report

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-space-separated-lqf-permanence.json: statement unchanged; four-step assembly, 1881 characters, replacing the returned six-step 4445-character proof.
- dag/nodes/sec-purity-real-sheaves/lem-a1-space-lqf-atlas-refinement.json: statement, unsplit; no Mathlib match. Pullback atlas tests and common refinement with arbitrary etale charts, including the local-quasi-finiteness consequence.
- dag/nodes/sec-purity-real-sheaves/lem-a1-space-open-chart-tests.json: statement, unsplit; no Mathlib match. Open scheme tests, section injectivity and representable etale composite charts.
- dag/nodes/sec-purity-real-sheaves/lem-a1-space-monic-diagonal-tests.json: statement, unsplit; no Mathlib match. Natural diagonal test isomorphism for a monomorphism into a base change and its represented closed-immersion consequence.

These three independent jobs retain the old argument at comparable granularity; none states all the permanence conclusions. Each has an empty proof, empty proof_deps and null proof_origin. citations.json supplies a verbatim statement excerpt for every use of every assembly step. searches.jsonl contains the actual search command results. The old searches of the item are preserved; no prior sandbox item/report existed (only dispatcher marker files). The live node supplies the returned proof, reviewed history, citations, Lean record and provenance. Its released stage-1 repair note expressly reopens it despite its earlier review.

## Attachments

None. Searching WeilConjectures by the item tag and by chartwise/algebraic-space permanence found no complete project declaration. The recorded theorem AlgebraicGeometry.AlgebraicSpace.space_separated_lqf_permanence in lean/Sheaf/AlgebraicGeometry/SpaceSeparatedLqfPermanence.lean has its proof `sorry`; its signature matches all clauses but is not an attachment. No Lean was written and no compiler, Lake or build tool was run.

## WANTED

None. All cited Stacks sources were available locally.

## What was wrong and what changed

The human's return requires spreading the old six arguments across at least two new statement-only jobs, while preserving the statement and a <=3000-character assembly. I extracted three jobs, retaining scheme local-quasi-finiteness base change and the representable-scheme final deduction in the assembly. The report below preserves the complete prior proof text, rather than silently shortening away its arguments. The order and mathematical route are unchanged; no disputed statement or new hypothesis was needed. The item retains all maintainer-owned fields and original Mathlib searches. The chapter and unit records were read and are unchanged. This is the existing auxiliary representability branch under lem-a1-affine-hc0, not a change to either Rankin--Selberg unit step. The current main-20261015 chapter/unit/ancestor text was read alongside their DAG records.

## What remains

The three new nodes deliberately remain unsplit for independent workers, as the repair order requires. Stage-1 server preflight results are recorded below after validation.

## Not duplicates

lem-a1-space-lqf-atlas-refinement vs lem-a1-scheme-lqf-etale-source-locality: the scheme lemma is an input to the common-refinement inference; it supplies neither the pulled-back algebraic-space atlas nor the represented refinement and test isomorphisms.
lem-a1-space-open-chart-tests vs lem-weil-pbc-field-point-factors-through-closed-immersion: unique lifts of field-valued points through scheme closed immersions do not state injectivity over arbitrary scheme tests or composition of algebraic-space charts.
lem-a1-space-open-chart-tests vs lem-weil-pbc-field-point-factors-through-immersion: the existing residue-field and field-point lifting assertions concern scheme immersions; the new job concerns arbitrary algebraic-space open tests and etale chart composition.
lem-a1-space-open-chart-tests vs lem-weil-pbc-separated-cancellation: scheme separatedness of immersions and cancellation do not state the new section injectivity and composite-chart test isomorphisms.
lem-a1-space-open-chart-tests vs lem-weil-pbc-descend-etale: descending an etale scheme map along an inverse limit has different hypotheses and conclusion from the open-test/chart calculation.
lem-a1-space-open-chart-tests vs lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink: shrinking a pointed scheme neighbourhood does not give arbitrary algebraic-space-source monomorphy or scheme tests of composite charts.
lem-a1-space-open-chart-tests vs lem-weil-pbc-smooth-zero-differentials-affine-open-etale: its smooth scheme restriction criterion with vanishing differentials is not the new open representable transformation assertion.
lem-a1-space-open-chart-tests vs lem-sfb-finite-etale-clopen-restriction: restriction of finite etale scheme maps over an irreducible base imposes hypotheses absent here and does not state the new sheaf/test assertions.
lem-a1-space-open-chart-tests vs lem-weil-pbc-open-immersion-etale: the scheme implication is an ingredient only; the new job also gives monomorphy on all scheme sections and the represented scheme tests for charts over arbitrary algebraic spaces.


lem-a1-space-lqf-atlas-refinement vs lem-a1-space-separated-lqf-permanence: the item is the designated re-split parent; the new node states explicit atlas/test/refinement data, assumes local quasi-finiteness only of U_B -> B, and proves no separatedness or open-restriction theorem.
lem-a1-space-lqf-atlas-refinement vs lem-sfb-stack-proper-locally-quasifinite-composition: the existing node compares proper/lqf stack composition and algebraic-space properties; it does not supply the pulled-back scheme atlas or the two refinement projections and test isomorphisms.
lem-a1-space-lqf-atlas-refinement vs lem-sfb-dm-lqf-atlas-test: the stack equivalence relates intrinsic and chartwise local quasi-finiteness; it does not state the concrete base-changed atlas/test isomorphisms or common-refinement projections of the new node. Citing the equivalence alone would lose the old step 1 argument the human requires preserving.
lem-a1-space-lqf-atlas-refinement vs lem-trf-fibre-product-atlas-tests: the existing node constructs a fibre-product atlas from two surjective atlases over a sheaf with representable diagonal; the new node compares that pulled-back atlas with a possibly nonsurjective chart and states the scheme-locality inference.
lem-a1-space-lqf-atlas-refinement vs lem-trf-space-etale-source-atlas-detection: that node detects representable/chartwise etaleness of maps, not the Stacks scheme local-quasi-finiteness of maps from arbitrary charts to B.
lem-a1-space-open-chart-tests vs lem-weil-pbc-etale-composition-cancellation: the existing scheme composition theorem is an ingredient; the new node proves the sheaf section-injectivity and explicit representable-chart pullback identifications.
lem-a1-space-open-chart-tests vs lem-weil-pbc-open-immersion-monomorphism: the existing node has scheme source and target; the new node allows algebraic spaces and states the chart tests as well.
lem-a1-space-open-chart-tests vs def-a1-space-open-subspace: that definition names open subfunctors; it does not state etale chart composition and monomorphy for any morphism tested as open.
lem-a1-space-monic-diagonal-tests vs lem-a1-space-separated-lqf-permanence: designated re-split parent; the new node is a natural test isomorphism for every monomorphism into X_B, without any local-quasi-finiteness or open hypothesis.
lem-a1-space-monic-diagonal-tests vs lemma-nagata-diagonal-base-change: the latter concerns diagonals under scheme base change only; it has no algebraic-space subobject Y or arbitrary scheme test of its diagonal.

DAG searches covered all files for tags 03XL, 0ABM, 03XJ, 03KL, 03KQ, 03XK, 03KY, 03MJ, 02WK and 02WL, and keywords atlas, chart, open and diagonal/monomorphism. The blueprint_refs search covered the whole imported blueprint for quasi-finite, atlas, diagonal, algebraic space, monomorphism and the tags 03XJ, 03KL, 03KQ, 03MJ, 02WK, 02WL. No blueprint node states one of these explicit test-data assertions; same_as is empty. The ancestry command returned lem-a1-affine-hc0 and the new via lists insert this item before its inherited via list. The Mathlib candidates and related DAG statements were opened before deciding their scope.

## Review by N9

I read spaces-morphisms.tex Tag 0ABM, label lemma-base-change-quasi-finite-locus, including its U,V,V',U' atlas diagram; Tag 03MJ, lemma-local-source-target, especially its common-refinement diagram and the surjectivity needed for descent; Tag 03XJ, definition-locally-quasi-finite; and Tags 03XL/03XK, lemma-base-change-quasi-finite and lemma-composition-quasi-finite. These justify the first extraction in exactly the Stacks scheme sense, including local finite type. I also read descent.tex Tag 03X4, lemma-locally-quasi-finite-etale-local-source, and the existing scheme locality node. In the extracted job, U_B is an actual scheme fibre product; W -> V is surjective etale and W -> U_B is etale, so the two scheme-locality directions used by the old argument have precisely their needed hypotheses. Arbitrary B -> T is permitted. No separatedness, quasi-compactness or Noetherian assumption has appeared in this extraction.

For the second extraction I read spaces.tex Tag 02WK, lemma-composition-representable-transformations-property, and morphisms.tex Tags 02GP/02GN, lemma-open-immersion-etale and lemma-composition-etale; schemes.tex Tag 01L7, lemma-immersions-monomorphisms, supplies scheme monomorphy. The new statement exposes both the pullback scheme O_H and the canonical identification of the composite chart's test, so its future worker has an independent job rather than an instruction to reuse the parent's proof. The original section argument is preserved below: two sections over the same c give sections of O_H -> H over 1_H, and scheme monomorphy equates them. The composite chart is representable because its every scheme test is the scheme V times_O O_H; its projection is the composition of the two etale scheme maps, with no surjectivity requirement on V.

For the third extraction I read spaces-morphisms.tex Tags 03KL/03KQ, lemma-base-change-separated and lemma-composition-separated, and Tag 03KY, lemma-match-separated. The asserted test isomorphism uses X times_T X, not X times_S X, and Y times_B Y, not Y times_T Y. Its map from D exists since the common beta maps to the same T-section. On every further H -> D, equality x_1=x_2 is equivalent to equality of the pairs (x_i,beta), and section-injectivity of j equates this to y_1=y_2. This is natural in H, hence yields the isomorphism over D. Closed immersion is then supplied by the actual original diagonal hypothesis, not a representability-only definition. This extraction is more general than open restriction and does not require local quasi-finiteness.

I opened the statement of every assembly citation. Step 1 uses def-trf-algebraic-space for the surjective etale atlas, lem-trf-space-fibre-products-etale-covers for existence of X_B, the new atlas/refinement statement for both its atlas and all-chart conclusion, and precisely clause (2) of lem-weil-pbc-separated-lqf-base-change for U_B -> B. Step 2 uses the new open-test statement for both monomorphy and chart composition; applying the established all-chart assertion of step 1 is just substitution. Step 3 uses the new diagonal-test statement with the identity or open monomorphism, and the parent's separatedness assumption supplies its last hypothesis. Step 4 is the old identity-chart argument: def-weil-etale-morphism permits the identity chart, def-pc-fibre-product gives the scheme Z times_B Z, and def-weil-proper-morphism defines separatedness as a closed diagonal. No other non-elementary inference is concealed there. The two generic off-unit tools already accepted on the parent remain declared in split_report.tool_uses. The new nodes belong to the parent's unit.

Small-case checks: empty X and B give empty base-changed atlases, with surjectivity onto the empty target valid; empty O has vacuous section-injectivity and empty charts. The identity open inclusion gives the X_B conclusion. Scheme sources recover the usual scheme statement. Dropping atlas surjectivity is invalid: an empty atlas cannot detect local quasi-finiteness of A^1_k -> Spec k. Dropping section-injectivity in the diagonal job is invalid: for X=B=T=Spec k and Y the two-point disjoint union, the off-diagonal test has empty equality locus for Y but the full one-point equality locus for X. Nilpotents are allowed, since the test formula is an isomorphism of functors, not a claim about underlying point subsets. No finite type restriction on the base change or on the test schemes is used.

Mathlib searches were run through msearch.py and read as returned, twice by concept before declaring absence. The atlas results concern schemes; QuasiFinite.lean explicitly says Mathlib's LocallyQuasiFinite does not impose local finite type. Open-immersion results include scheme monomorphy; the relative-property instances in Representable.lean lines 389-440 provide separate ingredients, not the full combined test-data assertion. Diagonal.lean lines 95-215, 309 and 396 provide general pullback squares and isomorphisms; they still require monomorphy, pullback pasting, and comparison of represented scheme tests to obtain the new diagonal statement, so this is not a one-line specialization. None of the three nodes is a Mathlib leaf. Each has all search kinds, complete object introductions, definition dependencies, precise source tags and labels, and no proof text inside its statement. No SGA source is used. No new step exceeds 2000 characters. The human's explicit re-split instruction, rather than the ordinary preference to keep short arguments inline, requires these separate jobs.

I corrected only bookkeeping during this repair: the final assembly's old step numbers now refer to the new four-step proof, and concurrent search records were allocated to the right node by inspecting their exact query strings. I checked delivery-errors B through E against these concrete files: statement-only shape and sources, verbatim citation availability, absence of a cycle back to the parent, preservation of hypotheses, and no restatement of all parent clauses. There is no statement dispute.

## Preservation of the returned arguments

The following is the complete returned six-step proof, retained for the future workers and the maintainer. Old steps 1 and 2 belong to lem-a1-space-lqf-atlas-refinement, except the scheme-base-change application which remains in assembly step 1. Old steps 3 and 4 belong to lem-a1-space-open-chart-tests, except the application of the already established all-chart assertion which remains in assembly step 2. Old step 5 belongs to lem-a1-space-monic-diagonal-tests and its two specializations are assembly step 3. Old step 6 remains assembly step 4. Thus no argument has been replaced by an unproved assertion with a broader, vaguer statement.

### Old step 1

Choose a representable surjective etale atlas $h_U\to X$ using [def-trf-algebraic-space]. By the hypothesis on every chart, the scheme morphism $U\to T$ is locally quasi-finite. The fibre product $X_B$ exists as an algebraic space by [lem-trf-space-fibre-products-etale-covers]. Put $U_B=U\times_T B$. On scheme tests, $h_{U_B}=h_U\times_X X_B$: on a test scheme $H$, a section is a pair $(u,\beta)$ with $f\circ u=b\circ\beta$. For every scheme $D\to X_B$ its atlas pullback is $D\times_{X_B}h_{U_B}\cong D\times_Xh_U$, which is a scheme surjective etale over $D$ by the original atlas definition. Thus $h_{U_B}\to X_B$ is representable surjective etale. The scheme map $U_B\to B$ is locally quasi-finite by clause (2) of [lem-weil-pbc-separated-lqf-base-change], applied to $U\to T$ and the arbitrary map $B\to T$.

Cited nodes: def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers, lem-weil-pbc-separated-lqf-base-change.

### Old step 2

Let $h_V\to X_B$ be any representable etale chart. The fibre product $W=h_V\times_{X_B}h_{U_B}$ is represented by a scheme. Its projection $p:W\to V$ is surjective etale because it is the scheme test of the atlas from step 1; its other projection $q:W\to U_B$ is etale because it is the scheme test of the chart $V\to X_B$ [def-trf-algebraic-space]. Apply the forward assertion of [lem-a1-scheme-lqf-etale-source-locality] to $q$ and the locally quasi-finite scheme map $U_B\to B$. Hence $W\to B$ is locally quasi-finite. Since $W\to B$ is also $W\xrightarrow{p}V\to B$, apply the converse assertion to the surjective etale $p$. This proves $V\to B$ locally quasi-finite for every chart, precisely the required chartwise property for $X_B\to B$.

Cited nodes: def-trf-algebraic-space, lem-a1-scheme-lqf-etale-source-locality.

### Old step 3

Write $j:O\to X_B$ for the open inclusion. For a scheme $H\to X_B$, the scheme $O_H=H\times_{X_B}O\to H$ is an open immersion by hypothesis, and hence etale by [lem-weil-pbc-etale-composition-cancellation](1). For any representable etale chart $h_V\to O$, its composite to $X_B$ is representable etale: on the same scheme test $H$, the pullback is $V\times_O O_H$, a scheme etale over the scheme $O_H$ by [def-trf-algebraic-space], and the composite to $H$ is etale by [lem-weil-pbc-etale-composition-cancellation](2). Step 2 applies to this chart of $X_B$, giving $V\to B$ locally quasi-finite. Since $V$ was arbitrary, $O\to B$ is chartwise locally quasi-finite.

Cited nodes: def-trf-algebraic-space, lem-weil-pbc-etale-composition-cancellation.

### Old step 4

The inclusion $j$ is a monomorphism of sheaves. Indeed, suppose $a_1,a_2\in O(H)$ have the same image $c\in X_B(H)$ for a scheme $H$. They give two sections of the scheme open immersion $H\times_{c,X_B}O\to H$, both lying over $1_H$. These sections are equal by [lem-weil-pbc-open-immersion-monomorphism], so $a_1=a_2$. This proves injectivity on every $H$, which is precisely monomorphy for these set-valued sheaves. The identity inclusion $X_B\to X_B$ is also a monomorphism.

Cited nodes: def-trf-algebraic-space, lem-weil-pbc-open-immersion-monomorphism.

### Old step 5

Take $Y=X_B$ or $Y=O$, and the monomorphism $j_Y:Y\to X_B$ from step 4. Let $D$ be any scheme with a map to $Y\times_B Y$, represented by $y_1,y_2\in Y(D)$ with the same image $\beta\in B(D)$. Let $x_i\in X(D)$ be their images. The scheme test of $\Delta_{Y/B}$ represents equality $y_1=y_2$. On every further scheme test $H\to D$, equality $x_1=x_2$ is equivalent to equality of $(x_1,\beta),(x_2,\beta)$ in $X_B(H)$, and then to $y_1=y_2$ by monomorphy of $j_Y$. Consequently, naturally over $D$,
$$D\times_{Y\times_B Y}Y\ \cong\ D\times_{X\times_T X}X.$$
Here the map $D\to X\times_T X$ is $(x_1,x_2)$; it exists because both $f(x_i)$ equal the image of $\beta$ in $T$. These identifications use the equality description of sheaf fibre products [def-trf-algebraic-space] and the fibre-product universal property [def-pc-fibre-product]. The right side is a scheme closed-immersed in $D$ by the assumed separatedness of $f$. Thus the left side is a scheme closed-immersed in $D$ as well [def-weil-closed-immersion]. This proves the required separatedness of both $X_B\to B$ and $O\to B$ on every scheme test.

Cited nodes: def-trf-algebraic-space, def-pc-fibre-product, def-weil-closed-immersion.

### Old step 6

Finally suppose $O=h_Z$ for a scheme $Z$. The identity chart of $h_Z$ is representable etale: every scheme pullback is an identity, etale directly from the definition [def-weil-etale-morphism]. Applying step 3 to that chart gives the scheme map $Z\to B$ locally quasi-finite. The fibre product $Z\times_B Z$ is a scheme by [def-pc-fibre-product]; taking it as the scheme test by the identity map in step 5 says that the scheme diagonal $Z\to Z\times_B Z$ is a closed immersion. This is exactly separatedness of a scheme morphism in [def-weil-proper-morphism]. Taking $Y=X_B$ in steps 2 and 5 already supplies the in-particular clause.

Cited nodes: def-weil-etale-morphism, def-pc-fibre-product, def-weil-proper-morphism.

## Validation history

The first full dry run stopped before pushing because nine same-tag comparisons were not individually listed under Not duplicates. I opened every listed statement and added the precise distinctions above. The standalone server review_split had passed; the complete dry run is being repeated after this report correction.


## Current-DAG rebase repair, 2026-10-22

The current return is the landing refusal “completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it)”, rather than a rejection of the mathematical split. I retained the delivered sandbox, all three extracted statements, the full six-step old proof, and the exact logged searches. The initial required dry run completed successfully at 70840fb4076 before this repair. The delivery tool constructs its temporary worktree from the current DAG; no git command was run in the shared repository.

I compared every field of the retained item with the current read clone. Only proof, proof_deps and split_report differed before this repair: the live item still carries the exact six-step returned proof (also byte-for-byte equal as parsed JSON to old-proof.json), the identical statement and statement dependencies, and the same maintainer-owned metadata. None of the three extracted node ids exists in the current DAG. The released stage-1 repair note still explicitly orders this re-split, so the live item's historical reviewed record does not close the repair. No metadata was restored from a stale branch.

I re-read all current cited statements, including statement dependencies of the three new jobs: def-pc-scheme, def-pc-fibre-product, def-trf-algebraic-space, def-weil-closed-immersion, def-weil-open-immersion, def-weil-etale-morphism, def-weil-proper-morphism, pqf-def-quasifinite, lem-trf-space-fibre-products-etale-covers and lem-weil-pbc-separated-lqf-base-change. They support the same uses, without new hypotheses. The scheme-locality input still allows non-surjective etale precomposition and requires surjectivity for the converse; I also re-read its statement and the old scheme open-immersion and etale-composition inputs. The atlas and diagonal assertions keep their actual bases B and T, with arbitrary base change b.

I made a concrete clarification to assembly step 4: it now takes an arbitrary representing isomorphism e:h_Z ≅ O as its chart and uses the fibre-product universal property to identify its diagonal test with Z → Z ×_B Z. This avoids treating an arbitrary representation as literal equality. An isomorphism has identity affine ring maps in its scheme tests, so the cited etale definition applies; this is a definition check. The assembly still has fewer than 3000 characters. The other three assembly steps and all three new statements are retained. I expanded citations.json from short matching fragments to the clauses actually used: existence of the atlas, the full atlas/refinement data, both monomorphy and chart composition for the open test, the diagonal-test isomorphism, and the fibre-product universal property. Every excerpt is verbatim in its current statement.

This repair is part of my Review by N9 above. I re-opened Stacks 03KL/03KQ/03KY/03MJ/03XJ/0ABM/03XK/03XL, 02WK and 03X4, and the current chapter/unit and ancestor blueprint text. The duplicate searches were checked against the current DAG, including the newer generic monomorphism lemma lem-sfb-space-lft-monomorphism-separated-lqf: its map has scheme target and its local-finite-type hypothesis is absent from the new diagonal-test statement, so it supplies neither that test isomorphism nor the two chart constructions. The recorded Mathlib hits and the actual source declarations in QuasiFinite.lean, Representable.lean and Diagonal.lean were re-read, with no changed search question requiring repeated service searches. The project search still finds no completed WeilConjectures declaration for this item; the Sheaf theorem at line 76 still ends in sorry. Empty sources and opens, the identity open, and arbitrary representing isomorphisms satisfy the same edge-case checks described above. No new mathematical hypothesis, statement dispute, SGA citation or Lean edit is introduced.
