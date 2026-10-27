# Q15: lem-sfb-symmetric-abel-image-geometry

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-symmetric-abel-image-geometry.json`: item split into ten proof steps; original statement retained, statement dependencies completed, original source/creation/blueprint provenance and original search records retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-abel-differential-boundary.json`: statement-only prerequisite computing the infinitesimal Hilbert-to-Picard map and its kernel. No Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-small-degree-divisor-sections.json`: statement-only prerequisite for the section count of every degree-one effective divisor in positive genus, and existence of a divisor with one section in every degree from zero to the genus. No Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-regular-codimension-one-cartier.json`: statement-only generic scheme-geometric prerequisite for an integral codimension-one subvariety of a smooth variety to be Cartier. No Mathlib match.
- `citations.json`: one entry per step/node citation, quoting the actual statement verbatim.

## Attachments

None. I searched the entire project source for the item tag, Abel maps, Abel–Jacobi maps, symmetric powers and Picard universal families. `WeilConjectures/AlgebraicGeometry/Picard/Jacobian.lean` constructs the Hilbert-to-Picard map and proves degree-g surjectivity, but does not give all of the item's normalized-family, closed-immersion, birational-image and Cartier clauses. Its partial coverage is already represented by the existing Picard nodes. Neither a coordinate Jacobian of a Weierstrass curve nor an abstract image in an abelian category is an attachment for this item.

## WANTED

None. The sources used are present in the repository; no download or compiler was used.

## What needed repair

The imported item was statement-only, with no argument. Its statement is correct under the stated positive-genus and fixed-representing-isomorphism hypotheses, and I have not changed it. The scheme structure on the effective-divisor image needs an argument: a bijection on geometric points does not itself prove the statement about scheme-theoretic images. Likewise generic injectivity alone is insufficient in positive characteristic. The proof now uses the infinitesimal Abel calculation and a finite-unramified local argument, and spells out restriction of the scheme image to the resulting open isomorphism.

I initially searched a possible new generic proper point/tangent criterion, but did not create it: the existing proper finite-fibre neighbourhood, cotangent criterion, unramified locus and finite unramified singleton-fibre statements already give the necessary local argument in Step 6. The searches for that discarded candidate remain truthfully in `searches.jsonl` and the saved result files. No searches have been invented. Five fresh searches per delivered new node and per item were executed with the required command (LeanFinder twice, LeanSearch, Loogle, grep); I read their results. Searches find Weierstrass-coordinate Jacobians, analytic manifold tangent spaces, cotangent-complex boundary maps, basic closed-immersion interfaces and reduced/integral schemes. They do not state these three prerequisites. The additional exact local-criterion search also gives only basic immersion interfaces.

The nearest-blueprint-ancestor command prints `None` for this item. I retained its inherited `blueprint.from.node: null` and its detailed route description, and prepended this item to each new node's inherited `via` list, as instructed by the ancestor command. Searches of the whole imported blueprint for Abel maps, tangent spaces, differentials, linear systems, nonspecial divisors, Riemann–Roch, Cartier divisors and Tags 0B2G/0BXH found no blueprint statement duplicating a new node. The existing degree-g Abel-surjectivity result is used rather than recreated. This remains a prerequisite below the alteration/curve-level-structure route recorded in the item's provenance, not a replacement of any unit step.

## What is unfinished

Nothing in this one-level split. The three new nodes intentionally carry statements and searches only; their proofs are future stage-1 items. There are no new Mathlib leaves.

## Not duplicates

lem-sfb-abel-differential-boundary vs lem-sc-pic-tangent-space: the existing node identifies only the tangent space of the Picard scheme at the identity; the new node computes the tangent space of the divisor Hilbert scheme and the differential of its specific Abel morphism, including the exact kernel sequence.

lem-sfb-abel-differential-boundary vs lem-sc-hilb-to-pic-morphism: the existing node constructs the Abel morphism and describes its field-valued points; it states no differential or tangent-space calculation.

lem-sfb-small-degree-divisor-sections vs det-picard-f-representable-chart: the chart node assumes an open Hilbert locus and gives its Picard interpretation and smooth dimension, not nonemptiness or the one-section assertion in each degree.

lem-sfb-small-degree-divisor-sections vs sk-thm-picard-rr: Riemann–Roch gives a relation between h0 and h1, not existence of these nonspecial effective divisors, nor exclusion of a nonconstant function with a single simple pole.

lem-sfb-regular-codimension-one-cartier vs lem-per-surface-codimension-one-cartier-part: that node concerns the Cartier part of an arbitrary subscheme on a regular surface, and does not apply to a Jacobian of arbitrary dimension with the integral codimension-one subscheme as the whole divisor.

lem-sfb-regular-codimension-one-cartier vs lem-weil-pbc-smooth-scheme-over-field-regular: smoothness gives regular ambient local rings, not a local equation for a specified codimension-one integral closed subscheme.

lem-sfb-regular-codimension-one-cartier vs lem-sc-smooth-regular: the existing statement concerns local regularity of smooth curves, not Cartier divisors on smooth varieties of arbitrary dimension.

lem-sfb-regular-codimension-one-cartier vs lem-sc-dimension-locally-algebraic: that node gives invariance of the dimension on nonempty opens; it does not produce a locally principal ideal.

lem-sfb-regular-codimension-one-cartier vs lem-weil-pbc-finite-type-domain-dimension-local-ring: that node is the dimension formula for finite-type domains, not the no-embedded-points Cartier criterion.

lem-sfb-regular-codimension-one-cartier vs lem-sc-integral-locally-algebraic-affine-opens-dimension: the existing statement compares dimensions of two nonempty affine opens of an integral scheme; it asserts no locally principal equation for a closed subvariety.

lem-sfb-regular-codimension-one-cartier vs lem-weil-pbc-finite-type-domain-dimension-local-ring-chains: the existing statement gives common lengths of maximal prime chains of a finite-type domain; it gives no Cartier criterion for an integral closed subscheme.

lem-sfb-regular-codimension-one-cartier vs lem-weil-pbc-finite-type-domain-dimension-local-ring-localization: the existing statement equates the dimension of a finite-type domain with its local dimension at a maximal ideal; it does not assert that a height-one ideal is locally principal.

lem-sfb-regular-codimension-one-cartier vs lem-sbc-nowhere-dense-closed-fibre-dimension: the existing statement gives strict dimension drop for a nowhere-dense closed subset in a fibre; neither regularity nor generation of its ideal by a non-zero-divisor is asserted.

lem-sfb-regular-codimension-one-cartier vs lem-per-normal-surface-exceptional-curves: the existing statement concerns the finite collection of exceptional curves of a proper birational surface modification; it neither concerns arbitrary-dimensional smooth varieties nor asserts the generic Cartier criterion.

lem-sfb-regular-codimension-one-cartier vs lem-sc-curve-base-change-relative-dimension-one: the existing statement concerns smooth relative dimension one after changing the base of a curve; it says nothing about arbitrary integral codimension-one closed subvarieties of a smooth variety.

lem-sfb-regular-codimension-one-cartier vs lem-sc-finite-type-nonclosed-closure-closed-points: the existing statement gives infinitely many closed specializations of a nonclosed point; it provides no assertion about equations for an integral closed subscheme.

lem-sfb-regular-codimension-one-cartier vs lem-sc-integral-locally-algebraic-opens-dimension: the existing statement equates dimensions of an integral scheme and a nonempty open; it does not make a codimension-one integral closed subscheme Cartier.

lem-sfb-regular-codimension-one-cartier vs lem-sc-positive-dimensional-locally-algebraic-closed-points: the existing statement gives infinitely many closed points in a positive-dimensional irreducible closed subset; it says nothing about principal ideal sheaves.

## Review by Q15

I read the standing brief, the stage-1 contract, SETUP's chapter/unit/node levels, GOAL, the worker role, the current chapter and unit records, and both copies of delivery-errors B through E. I extracted Milne's AV PDF locally into this sandbox and read Chapter III pp.86–89, 91–93, 100–103 and the paragraph before Theorem 6.6 on p.105. I also read the actual Stacks statements and proofs of 02UP (`more-morphisms.tex`, `lemma-proper-finite-fibre-finite-in-neighbourhood`), 04DG (`etale.tex`, `lemma-finite-unramified-one-point`), 0B2G (`varieties.tex`, `lemma-injective-tangent-spaces-unramified`), 056S (`varieties.tex`, `lemma-smooth-regular`) and 0BXH (`divisors.tex`, `lemma-codimension-1-is-effective-Cartier`), with tags checked in the tag-label table.

For the differential prerequisite, Milne's Theorem 5.1(b) and the end of its proof on p.103 give the needed kernel dimension. The more precise boundary formulation is the following first-order refinement: a first-order Cartier divisor with local equation f_i - epsilon a_i gives a normal section a_i/f_i modulo regular functions; on overlaps the change of the transition function for O(D) is 1 plus epsilon times the difference of these local lifts. Its Picard deformation class is therefore the Cech boundary, up to the chosen sign. The sequence 0 -> O -> O(D) -> O_D(D) -> 0 identifies its kernel with H0(O(D))/H0(O), and H0(O)=k. This works with repeated points and in positive characteristic; no division by r!, trace on symmetric quotients, or separability assumption is made. This is a genuine infinitesimal lemma, not a restatement of any clause of the item.

For the small-degree prerequisite, I checked Milne's proof of Proposition 2.3 and Lemma 5.2. A second section of O(Q) would produce a nonconstant function with pole divisor bounded by the single point Q. Such a function gives a degree-one map to the projective line, forcing this smooth proper curve to have genus zero. For the existence assertion, start with the zero divisor and h1=g, choose a point where a nonzero residual canonical section does not vanish, and lower h1 by one at each of r steps; Riemann–Roch then gives h0=1. The hypothesis g>=1 is necessary for the degree-one assertion: it fails on the projective line. At r=0 the zero divisor has one section, and at r=g the residual h1 is zero. I recorded just the existence needed here, not an unnecessary generic-open-locus theorem.

For the Cartier prerequisite, 0BXH requires absence of embedded points, pure codimension one and regular ambient scheme (or UFD stalks). An integral Z has only its generic associated point. A dimension-(n-1) integral subvariety of an n-dimensional variety has codimension one by the finite-type dimension formula; smoothness gives regularity by 056S. This applies in every dimension, not only on a surface. I tested n=1 (a reduced point), n=2 and a higher-dimensional Jacobian. A nonreduced subscheme with an embedded component is deliberately excluded: dimension alone would not give this result.

I opened every existing node used by the proof and read its statement, not its proof, for the following checks. The complete statements copied to `citations.json` are literal substrings, and say precisely the facts taken below.

1. The projective-proper node supplies properness, the smooth connected curve node supplies integrality, and the base-change-integrality node gives geometric integrality with the given P. The fixed Jacobian definition supplies a representing isomorphism, not an existence theorem requiring additional choices. The rigidified Picard split node supplies the universal H0/base-change condition for this curve and the description by pairs for all T. Evaluating the identity and using naturality constructs the family; the group identity gives its trivial zero fibre. No extra hypothesis on T is imposed.
2. The Hilbert-curves statement gives a smooth proper variety of dimension r, not merely a representable set. The existing degree-decomposition statement gives tensor-translation isomorphisms on the whole Picard functor. The Hilbert-to-Picard statement gives the actual morphism and its divisor-line-bundle description. The divisor-line-bundle comparison identifies its convention with the rational-function divisor convention. All hypotheses are over this algebraically closed, hence separably closed, field and geometrically integral curve.
3. I kept the rank-one Hilbert identification as an elementary argument: a unital rank-one finite locally free algebra is O_T, so a rank-one divisor is a graph, with no descent or unproved symmetric-quotient comparison needed. The Hilbert functor definition explicitly supplies its arbitrary-T points. For the inverse graph construction, proper base change makes C_T -> T proper and thus separated, and the existing separated-section lemma makes the graph closed; these two scheme-geometric facts are explicitly cited. Functoriality is written out.
4. The divisor-class theorem gives linear equivalence from equality of invertible-module classes. The global-functions statement makes the ratio of equal-divisor sections a scalar. The closed-point residue statement and the Jacobson statement are used on the finite-type fibre, ensuring singleton closed points really imply a singleton underlying fibre. The new differential statement gives injectivity when h0=1. This avoids the false inference that singleton k-points automatically make a fibre reduced.
5. The proper-over-separated statement applies because the source is proper and the abelian target is separated. The reduced-image statement gives the reduced scheme structure on the closure of the image. Its topological closure is irreducible since H_r is integral, so W_r is integral. This node supplies the scheme-structure assertion rather than an informal point-set identification.
6. I checked the exact inputs of 02UP and 04DG: properness and the finite singleton underlying fibre for the former; finiteness, unramifiedness, singleton fibre and the identity residue extension k/k for the latter. The tangent/cotangent node gives surjectivity on cotangent spaces, and the rational unramified criterion applies at closed rational points of locally finite type schemes. The unramified-locus statement gives an actual source open. Removing the proper image of its complement makes the whole remaining inverse image unramified. No mere pointwise unramifiedness is substituted for 04DG's global hypothesis.
7. The degree-one section count applies at every point because g>=1. Local closed immersions then cover the target, adding the open complement of the proper image. The Jacobson node rules out a nonempty closed complement of this covering. The Zariski-local closed-immersion node states exactly the local-to-global property required here.
8. The small-degree node gives a specific good divisor for each r. The scheme-image restriction node requires quasi-compactness and quasi-separatedness: both hold for the proper map. On its closed-immersion neighbourhood, the image is the quotient by the same ideal, hence an actual scheme isomorphism. The nonempty opens are dense since the source and image are integral. The dimension node gives dimension equality on those opens, and the Hilbert-curves node gives r. This proves birationality even in positive characteristic.
9. The existing Abel-surjectivity node includes d=g and all required projective/geometrically integral hypotheses. Smooth-over-field regularity and regular-connected integrality apply to the abelian variety J. The reduced-image node then identifies W_g with J as a scheme; surjectivity on points alone is not used to erase a nonreduced structure.
10. J has dimension g by the fixed-Jacobian definition, and W_(g-1) is integral of dimension g-1 by the preceding steps. These are the exact hypotheses of the generic Cartier lemma. The final image identification under tensor translation is proved from the universal property of the scheme-theoretic image, with the inverse translation giving the reverse containment.

The proof's longest step is below 2000 characters; no long-step exception is needed. The only elementary-marked step is the rank-one algebra/graph identification, where the argument is present. Each new statement introduces its own objects and references the defining notions. New nodes have no proof, proof dependencies or hidden proof sketch. Existing generic tools from other units are declared in `split_report.tool_uses`; they are prerequisites below the unit's fixed route. I found no statement dispute, source error, missing literature, unsupported Lean attachment, forbidden SGA citation or reason to change a target.

## Validation record

The preliminary server `check_dag` reported no finding introduced by this sandbox or on its nodes. The first delivery dry run stopped at the duplicate-tag check: the secondary dimension tags in the Cartier prerequisite also occur in nine dimension/specialization nodes. I opened those statements and added the required individual comparisons above; none states the Cartier criterion.

The next dry run passed preflight at `abd41fcefcf` (not pushed). In a final C1 audit I added explicit references to the Hilbert functor definition, proper base change and the separated-section closed-immersion theorem in the rank-one graph step, and regenerated the citation entries. The final dry run below validates that precise version.


## Repair of the L promotion return (2026-10-22)

L approved the mathematical split but refused landing because the side-project completion had not been promoted to the live DAG. This repair retains the approved ten-step argument, its sources, the three statement-only prerequisites, all saved search results and the search log. The delivery is rebuilt on the current server DAG by the required delivery tool; no repository file or launcher script was edited.

I compared the retained item with the current shared node. The current node is still unsplit with an empty proof. Its statement, source, creation record, chapter, unit and blueprint provenance agree with the retained version. The differing fields are exactly the stage-1 split fields: proof, proof dependencies, proof origin, completed statement dependencies, additional truthful searches, status and split report. The three new prerequisite ids are still absent from the current DAG. There is no released repair note changing the route or requiring a further split.

I re-read all 31 existing node statements cited by the ten steps. Each complete statement is identical, after whitespace normalization, to the complete statement preserved in citations.json; all 50 step/node citations still quote the statement they use. Thus no cited mathematical statement changed from the returned delivery's saved evidence. In particular I rechecked the arbitrary-base rigidified Picard description in Step 1, representability and tensor translation in Step 2, the proper-base-change and separated-section inputs in Step 3, the finite singleton fibre and globally unramified hypotheses in Step 6, the quasi-compact/quasi-separated restriction of scheme images in Step 8, and the degree-g surjectivity in Step 9. These current statements still give exactly those inputs, with the hypotheses verified in the signed review above.

I revisited Milne III Lemma 1.8, Proposition 2.3, Theorem 5.1 and Lemma 5.2, and the paragraph defining the theta divisor before Theorem 6.6, together with Stacks 0BXH. The edge cases r=0, r=g and g=1 and the positive-characteristic tangent argument still apply. The retained search-result files and searches.jsonl confirm the previous no-match findings; the statement and search questions have not changed, so no search was invented or needlessly repeated. No new node or Mathlib leaf was added by this repair.

The first required dry run of the retained version completed successfully and wrote the sandbox readiness record at 2c6304b64fc. That process had exited before this report and the split-report summary were updated. A fresh dry run validates this explicit repair record and the delivery rebased on the current DAG, followed by the authorized push.


## Resumed promotion repair verification (2026-10-22)

The required first dry run of the retained split exited successfully: `OK (not pushed)` at `6432f50b7da`. I then compared all seven differing fields of the current unsplit item with the retained delivery: only proof, proof dependencies, proof origin, statement dependencies, Mathlib searches, status and split report differ. The mathematical statement and provenance agree. None of the three new prerequisite ids is present in the shared DAG, and there is no repair-note override. This is the promotion repair requested by L, retaining the already approved proof rather than replacing its route.

I reopened all current cited statements and compared the complete saved quotations: all 50 step/node entries agree after whitespace normalization, across 31 existing dependencies and the three retained new nodes. No cited statement changed relative to that saved evidence, so no proof or citation adjustment was necessary. In particular the rigidified Picard statement explicitly includes arbitrary base change; the degree decomposition includes translation on the whole functor; and the local immersion argument uses a finite map which becomes everywhere unramified after removing the proper image of the complement of its unramified locus. The scheme-image restriction is applied to the proper, hence quasi-compact and quasi-separated, Abel map.

I reread Milne III Lemma 1.8, Proposition 2.3 and Lemma 2.4, Theorem 5.1 and Lemma 5.2, and the theta-divisor paragraph before Theorem 6.6, together with Stacks `lemma-codimension-1-is-effective-Cartier` (0BXH). The existing section-count and tangent prerequisites still support r=0, r=g, g=1 and positive characteristic. Each proof step is shorter than 2000 characters. Searches of the project for the exact blueprint tag and the geometric notions find the existing partial Picard/Jacobian tools, not a declaration of all clauses of this item. I also reopened the retained search log (26 entries) and saved results; the unchanged mathematical questions require no repeated search. All original sources, searches, proof text and citations are preserved. The next dry run checks this updated repair record on the current server DAG before the authorized push.

## Current-DAG rebase audit (2026-10-23)

The retained version was compared with the current shared DAG before this repair dry run. The current item is still the same unsplit statement with the same chapter, unit, source and blueprint provenance; only the retained stage-1 fields differ. The three prerequisite files (`lem-sfb-abel-differential-boundary`, `lem-sfb-small-degree-divisor-sections`, and `lem-sfb-regular-codimension-one-cartier`) are still absent from the current DAG, so the split remains applicable.

I reopened every distinct cited node used by the ten proof steps (34 distinct nodes, 50 step citations). The complete quotations in `citations.json` remain verbatim substrings of the current node statements, with no missing or extra step/node citation. In particular, the current statements still provide the rigidified Picard universal property and arbitrary-base condition (Step 1), Hilbert representability and tensor translation (Step 2), the proper-base-change and separated-section inputs for the rank-one graph (Step 3), the singleton-fibre and tangent inputs (Step 4), proper scheme-theoretic image and reduced-image structure (Step 5), the finite/unramified local closed-immersion criterion (Step 6), the local-to-global closed-immersion criterion (Step 7), quasi-compact scheme-image restriction and dimension of nonempty opens (Step 8), degree-(g) surjectivity and regular connected integrality of the Jacobian (Step 9), and the codimension-one Cartier criterion (Step 10).

I reread the retained Milne AV excerpts for Theorems 1.7, Proposition 2.3, Theorem 5.1, Lemma 5.2 and Theorem 6.6, and the Stacks source for Tags 0BXH, the proper finite-fibre lemma and the finite unramified singleton-fibre lemma. The edge cases (r=0), (r=g), (g=1), repeated divisors, and positive characteristic remain covered. The project Lean search still finds no declaration tagged for this item or a complete Abel-image geometry result. No statement, source, dependency, search record, quotation, or proof step required correction.

The required initial dry run of the retained delivery exited with `OK (not pushed)` at `d25c7ad6af9`. The split-report date and summary now record this current-DAG audit, and the final dry run below validates the updated repair record before pushing.
