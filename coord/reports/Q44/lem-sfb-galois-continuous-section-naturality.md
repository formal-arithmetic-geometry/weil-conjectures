## Worker report

Group Q44, stage 1, item lem-sfb-galois-continuous-section-naturality, 2026-10-22. The sandbox initially contained only dispatcher markers; there was no previous proof, report or search log to resume. The live item was unsplit, with no repair note. I retained the statement, its nine statement dependencies, source and creation metadata, and all five inherited Q55 Mathlib-search records. No Lean was written or compiled.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-galois-continuous-section-naturality.json: seven proof steps and their exact dependency union, agent proof origin, blueprint place/search result and split report; status split.
- citations.json: fourteen citations, one for each node used by each proof step, quoted verbatim from its statement.
- report.md: this report and author review.

No new nodes and no new Mathlib leaves. searches.jsonl records five actual Q44 searches; prepare.py is sandbox-only preparation code and is not a delivery file.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and continuous-section, Galois-section and continuous-ring comparison terminology. No declaration gives the full assertion. In particular the declaration for ContinuousRingUniverse.comparison_isIso is under lean/Sheaf and proves an ingredient, not the whole item. It is used through its existing DAG node, not asserted to be an attachment.

## WANTED

None. The Hemo--Richarz--Scholbach and Bhatt--Scholze PDFs, Stacks source and relevant project/Mathlib source files were all available locally.

## Findings and changes

The imported item had no proof and did not establish that its coefficient-coordinate isomorphisms were the adjoint-normalized ones. I supplied the proof, keeping its hypotheses and all conclusions. The main inputs already existed: lem-sfb-continuous-ring-universe-realization gives invertibility of the canonical ring comparison, and lem-weil-pbc-locally-constant-prime-spectrum gives the topology of the test objects. There is no need to create a new section-coordinate lemma or a separate coefficient-naturality lemma, both of which would merely repeat clauses of the item. The naturality follows by computing both adjuncts, not by invoking an unspecified natural isomorphism.

I also explicitly justified that W_q is a legitimate object of the small pro-etale site: the separable-cover node gives weak etaleness, and the existing base-change/composition theorem gives it for the nerve. The zeroth face is evaluated as an underlying map of spaces: changing the base geometric map does not operate on the coefficient field. No perfectness or algebraic closedness of the separably closed geometric field is used.

There is no statement dispute. The equality of degree-zero sections with A is interpreted by the asserted canonical ring identification, as in the source, not as a literal equality of set-theoretic encodings.

## Sources and existing-node search

I read Hemo--Richarz--Scholbach Example 3.1 on printed page 6, including its topological-ring functor, the continuous-function realization and the scheme-pullback paragraph. I read Bhatt--Scholze Examples 4.1.4 and 4.1.9--4.1.10, Lemma 4.1.6, and Lemma 4.2.12 with its proof on printed page 30. The general source is HRS; the additional normalized adjunction and simplex calculations are explicitly marked agent work.

For the test-space identification I read Stacks limits.tex, Tag 01YW, label lemma-directed-inverse-system-affine-schemes-has-limit, and the existing project's LocallyConstant.homeomorphPrimeSpectrum and evaluation formula, lean/WeilConjectures/RingTheory/Spectrum/Prime/LocallyConstant.lean:93--95 and 100--287. I read Mathlib/AlgebraicGeometry/Limits.lean:604--647 (finite sigmaSpec and its coprojections), GammaSpecAdjunction.lean:600 (Spec.reflective), and the statement of every cited node. The prime-spectrum result is the existing closed project theorem, not an unproved claim inferred from its definition.

The whole DAG was searched by continuous-ring, continuous-functions, profinite test, prime-spectrum and 4.2.12 wording. Whole-blueprint searches with tools/blueprint_refs.py used continuous sections, continuous ring, profinite test, totally disconnected and locally constant; none states this item. The existing general realization, test-object, spectrum and ultrametric/component nodes were opened before choosing the dependencies. I used no new nodes. blueprint_refs.py ancestor reports no imported ancestor in the inherited created.item chain, so the inherited null ancestor and via chain are preserved; from.place names the actual direct-images proof paragraph and the parent coordinate step instead of inventing an ancestor. The current main-20261015 direct-images proof (3) and its unit were read. This is a generic-field calculation below that route, not a replacement of the unit's proof.

## Mathlib searches

All five Q44 queries in the item's appended mathlib_searches were run with the prescribed batch2/msearch.py and recorded by it in searches.jsonl. Both LeanFinder phrasings, Loogle, LeanSearch and source grep were available and returned hits. The exact query strings and summaries are in the node. I read the results rather than treating a nonempty hit list as a match.

The first LeanFinder query found general naturality lemmas and sheaf-module adjunctions; the second found InfiniteGalois.profiniteGalGrp and its limit descriptions. Neither gives a normalized continuous-coefficient section comparison. Loogle found AlgebraicGeometry.continuousMapPresheaf and its map/component/sheafness declarations. LeanSearch found TopCat.continuousFunctions, its pullback and continuous-map ring structures, condensed sheaf constructors and locally constant precomposition. The grep of AlgebraicGeometry found continuous site functors and ElladicCohomology. I read Mathlib/AlgebraicGeometry/Sites/ConstantSheaf.lean:40--138 and the continuous-functions context of Topology/Sheaves/CommRingCat.lean. These construct continuous-function objects; they do not identify the actual inverse image from the condensed point with that object with the required adjoint normalization. Consequently this item is not a Mathlib leaf. No search was fabricated or recorded as unavailable when it succeeded.

## Not duplicates

No new nodes. The finite-partition calculation is included in step 2, and the coefficient and simplex calculations remain proof steps. In particular I did not create copies of lem-sfb-continuous-ring-universe-realization, lem-weil-pbc-locally-constant-prime-spectrum, the normalized set-coherence nodes, or one clause of this item.

## Review by Q44

I checked the seven steps with the node files and the sources open. HRS Example 3.1 asserts the continuous-function realization for topological ring coefficients and their functoriality; BS Lemma 4.2.12 supplies the source's continuous-map sheaf interpretation. Our nonarchimedean metric field meets the needed hypotheses without completeness. No new lemma statement needs a separate source review because no new node was created.

Step 1 is the explicit ultrametric clopen-ball argument. Hausdorffness is metric separation. For a point z outside B(a,r), taking the ball of radius |z-a| about z keeps the distance to a equal to |z-a|, by applying the ultrametric inequality in both directions. Thus the separation argument really gives total disconnectedness, also for a trivial absolute value; it is not an assumed completeness result.

Step 2 uses exactly the limit formula in def-sfb-profinite-test-objects, the finite-coproduct-to-product-spectrum isomorphism and coprojection formula in lem-weil-pbc-finite-affine-coproduct-spectrum, and the canonical ring-colimit/scheme-limit assertion in lem-weil-pbc-spec-small-colimit-limit. These statements really concern the diagrams used here. The index is the small set of finite clopen partitions of S, not an unrestricted category of all quotient presentations. Compactness gives finite image of a locally constant function; its nonempty fibres are a finite clopen partition. Surjective quotient maps give injective pullbacks, and common refinement compares any two representatives. This is the full elementary argument for the colimit LC(S,Omega); no tensor/colimit interchange is hidden in this step.

Step 3 uses the entire explicit homeomorphism and prime-ideal formula of lem-weil-pbc-locally-constant-prime-spectrum, with R the field Omega, so its spectrum is one point. I checked that the cited statement allows arbitrary commutative R and empty S. I compared the label to the projection in def-sfb-continuous-ring-canonical-comparison using clopen characteristic functions, whose values 0 and 1 survive the map from integers to any field. Thus the coordinates really are the prescribed geometric labels, not just some homeomorphism with S. Separably closed but nonperfect Omega causes no change.

Step 4 uses def-sfb-continuous-ring-canonical-comparison for the actual adjunct f maps to f composed with pi_S, and lem-sfb-continuous-ring-universe-realization for invertibility of that canonical comparison and its multiplication/unit preservation. The latter node states a result for every totally disconnected topological ring in universe u and every scheme X in that universe; step 1 verifies this hypothesis for A and B, and the project's compatible universe lifts are retained. I also read lem-sfb-separable-cover-finite-coordinates: its statement expressly makes v weakly etale and a covering; I take only this conclusion. The cited lem-weil-pbc-weakly-etale-composition-base-change expressly gives the two closure operations needed to form W_q as a site object. I corrected the initial draft to include those two citations rather than leave objecthood implicit. Ring-sheaf isomorphisms evaluate to ring isomorphisms on these objects, so no exactness of global sections is assumed. The unit equation fixes normalization before evaluation, and the degree-zero calculation uses a one-point space.

Step 5 cites the postcomposition formula for the condensed ring morphism in def-sfb-continuous-map-condensed-ring-map, and the actual adjunct from the canonical-comparison definition. Applying naturality of the adjunction Hom bijection to both composites gives precisely the two functions displayed in the proof. They agree by associativity. No source is asked to provide coefficient naturality when its statement provides only invertibility: the naturality calculation is written out and is elementary. Phi_X is a morphism since continuity and all pointwise ring operations commute with the continuous ring map. The hypotheses require continuity, with no isometry or completeness assumption on the field map.

Step 6 takes restriction as precomposition directly from the canonical comparison's F_{A,X} definition. It calculates each increment map from the vertices assumed in the item: tail for deletion zero, adjacent multiplication in the given order for an interior deletion, truncation for the last deletion, and insertion of the identity for a repetition. No new finite-Galois tensor hypothesis is introduced, and I do not apply the stronger galois-limit-nerve-faces statement without its finite-stage hypotheses. At the moved base vertex Spec(g_1) fixes the sole underlying topological point; hence a function into A has no extra Galois action on its value. I explicitly checked q=1, where both faces act on A by constant functions, and q=2, where the interior deletion gives g_1 g_2, not its reverse. Commutation with coefficient maps is the displayed function-composition identity.

Step 7 uses the monoidal natural comparison explicitly stated by sk-def-sfb-pullback-from-point-comp, and the transported ring structure in sk-def-sfb-pulled-back-coefficients. Thus multiplication and unit, not just underlying additive sheaves, are preserved. Applying naturality to the condensed ring map also gives its coefficient compatibility. This is an application of the cited statement, not a new derived or scalar-extension argument.

For B1--B8 I checked that there are no new statement-only nodes, no introduced undefined objects, no extra data or hypotheses, no proof in a leaf and no claimed new Mathlib match. The item statement is unchanged and its TeX remains singly escaped. For B9--B10 I checked blueprint provenance/searches and the absence of an attachment for the whole item. For C1--C4, each non-elementary ingredient above is a node citation, all fourteen quotations are copied from the cited statement, and no proof-internal construction is used as if it were a conclusion. C5--C8 were checked by the whole-DAG search and a read-only traversal of the cited dependencies: none reaches this item. The sole off-route nonclosed theorem is the generic continuous-ring realization; split_report.tool_uses explains its use. The spectrum node is already Lean-closed; the two scheme-limit/coproduct nodes and weak-etale closure are Mathlib leaves.

For D1--D5, no content was moved into a new lemma and the source's informal naturality was replaced by actual equations. Every step is shorter than 2000 characters, and I still checked for hidden subclaims: the finite-partition argument and adjunction calculation are fully written out. The underlying topological realization is explicitly cited, not silently reproved. For E1--E7 I checked S empty (zero function ring), S one point, G trivial, q=0, the two q=1 faces, the interior q=2 face and a degeneracy, the trivial absolute value, a separably closed nonperfect geometric field and a noncomplete coefficient field. Empty products and empty schemes are included by the cited spectrum and coproduct statements. No added hypothesis, coefficient-action twist or source error was found. No SGA source or forbidden route was used.

## Unfinished work

None in the one-level split. Existing cited statements retain their own stage states; this delivery does not claim to prove their Lean declarations. The required server preflight is run after this report is written.
