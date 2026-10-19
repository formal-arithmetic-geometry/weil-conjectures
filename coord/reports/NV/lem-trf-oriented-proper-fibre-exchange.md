# Worker report: lem-trf-oriented-proper-fibre-exchange

## Files written

- dag/nodes/sec-trace-formula/lem-trf-oriented-proper-fibre-exchange.json — statement, split into six steps; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-oriented-derived-cohomology-continuity.json — statement-only unsplit node; no Mathlib match. Its hypotheses involve a whole qcqs inverse diagram with affine transitions, and its conclusion is continuity on the limiting oriented site. It contains no properness or geometric-fibre conclusion.
- citations.json — every step/use pair, with the complete verbatim cited statement so that the hypotheses remain visible.

## Attachments

None. Searches by the item tag, oriented/vanishing-topos notions, and fibre/exchange terminology in /home/ubuntu/weil-src-slopmaster2/WeilConjectures found no declaration of this statement. The master checkout is reference only and also has no item-tag declaration. No Lean was written and no build or compiler was invoked.

## WANTED

WANTED: archival copy of Orgogozo, Modifications et cycles proches sur une base générale, author draft, Lemma 9.1.1 and the two consequences preceding Proposition 9.1.2, printed pp. 19–20, for lem-trf-oriented-proper-fibre-exchange. I read those pages online at the URL already in the item's source; the PDF is not in the repository's literature directory. Per the brief, I did not download it. The local ILO PDF was read after extracting text in this sandbox.

## What was wrong and what changed

The incoming node had the three statements and no proof. I did not change its statement or add any hypotheses. The new proof follows Orgogozo's localization/proper-base-change/local-topos route and expands the two stated consequences into calculations on the actual adjunction-defined arrows. I preserved the inherited blueprint ancestry through the constructibility chain and the unit sk-i-curve-zero; I read the current main-20261015 contracting-local-term proof, not the refuted internal-Hom stalk argument. This item is a generic infrastructure input on that route, not its key unit statement, so no realized fields were changed.

The source's notation for the geometric fibre as a closed immersion must not be copied literally for an arbitrary chosen geometric field. If Omega extends the separable closure of the residue field, the fibre map need not be a closed immersion. The proof instead uses ordinary proper base change along Spec Omega and checks the projection comparison at geometric points of that fibre. This requires no correction of the item's statement.

## Searches

The inherited item searches were read and retained: they return ordinary topological stalks, presheaf module pushforwards and tensor pullbacks, not the oriented proper-fibre theorem. For the new continuity node I ran LeanFinder twice with distinct formulations, LeanSearch, Loogle, and two Mathlib greps with msearch.py. All ran successfully; searches.jsonl and the new node contain the exact tool/query/results records. The closest hits concern global sections of structure sheaves under affine scheme limits (AlgebraicGeometry.AffineTransitionLimit), not arbitrary sheaf cohomology on oriented topoi. No leaf is claimed.

Before creating it I searched the whole DAG for oriented products, inverse limits and continuity, the source tags 09YP/09YL, and the Lean source for the notion; blueprint_refs searches included “oriented continuity”, “cohomology inverse limit”, “09YP” and “cofiltered inverse system”. The existing general site-colimit theorem does not identify the finite triple site of the geometric limit with that colimit, and the existing ordinary etale continuity theorem concerns schemes rather than oriented products. This geometric identification and its derived version are the genuine input left in the new node. It is not a two-line consequence of the statements currently cited, nor a clause of this item moved to a child.

## Review by NV

I read Orgogozo Lemma 9.1.1 and the paragraph of consequences on printed pp. 19–20 online, and I read local ILO Exposé XI 1.10(b), 2.2–2.7, especially the exact second projection in 2.3 and the limit-localization comparison in 2.7. I also read Stacks sites.tex lemma-colimit-sites (09YL), sites-cohomology.tex lemma-colimit (09YP), and etale-cohomology.tex theorem-proper-base-change and lemma-proper-base-change, including its bounded-below spectral-sequence passage. The new continuity statement makes explicit the qcqs and affine-transition hypotheses needed in that limit argument. Its fixed-stage coefficients, small cofiltered index, bounded-below condition, and natural restriction maps match those inputs. Its source is not a reference to any prohibited SGA document; the source cites ILO and the Stacks tags directly. Since the Orgogozo archival copy is missing and I expand the derived argument, proof_origin is honestly “agent”.

Step 1 uses the explicit universal-property inverse-image formula and the derived module adjunction recorded in def-trf-oriented-nearby-cycles. Those statements specify exactly the morphism and the counit used; forming the mate after substitution is elementary. I checked that its two projections are the fibre inclusion and constant t and that its orientation is c. There is no assumption that the map t to s is an identity.

Step 2 uses the affine-neighbourhood node for smallness, cofilteredness and initiality; the strict-henselization definition for the component limits; and the oriented slice node for the actual slices. The universal-product formula gives the inverse-image triples, rather than a claim taken from the proof of a definition. The new continuity node supplies precisely the comparison of their cohomology with Q. The site-point node supplies exact stalk colimits. Proper base-change permanence, separated implies quasi-separated, affine schemes are qcqs, and qcqs permanence verify every geometric hypothesis on the inverse diagram. In particular X times_Y U is not asserted affine: it is proper over affine U, hence qcqs. The transition is affine because it is a base change of a map between the affine U's. Derived composition normalization supplies the comparison on K-injectives with the adjunction units and counits. These are generic tools declared in split_report.tool_uses; they do not replace a step of the contracting-correspondence argument.

Step 3 repeats continuity for first-projection neighbourhoods, now with the other two affine components fixed. The local-projection node really says that p2_* equals the canonical-section inverse image and is exact; it is not merely a definition of that section. The strict-henselization functoriality node verifies that the localized first arrow is local and both local schemes are strictly henselian, since x lies over s. The strictly-henselian sections/stalk statement and the module/abelian derived-evaluation statement then calculate derived global sections as the (x,t,c) stalk, with the germ map. I corrected an audit mistake here: the classification of etale topos points is not the conservativity theorem. The final version cites lem-weil-pbc-derived-stalk-conservative, whose statement actually detects derived abelian isomorphisms, and scalar forgetting reflects kernels and cokernels. The exact module stalk calculation supplies the underlying abelian stalk calculation. The fibre map is allowed to have an enlarged geometric field.

Step 4 uses module proper base change, not the finite-ring-only corollary: the item allows an infinite commutative ring killed by m. The node det-properbasechange-modules states the required bounded-below module result for any commutative ring provided underlying cohomology is torsion. Here m kills every module cohomology sheaf of R pi_* A, so the condition holds. h^ell is proper by the cited permanence node. Sections over strictly henselian Y^ell equal the y-stalk, including for the chosen algebraically closed extension Omega. The cited derived composition and mate-pasting statements ensure the composite is theta_z from Step 1, rather than merely some abstract isomorphism between its endpoints. Every comparison is the restriction map induced by the same counit.

Step 5 applies the already proved formula to both proper maps h and h_T. I checked the actual fibre identification: use the same field Omega for y' and its composite y, so (X_T)_{y'} equals X_y and no extra field-extension invariance is smuggled in. The universal property identifies the coefficient pullbacks including their orientations, and mate pasting identifies the pulled-back comparison with the identity on that cohomology. The oriented-point conservativity node explicitly states its assertion for arbitrary schemes and derived constant modules, so its hypotheses do not secretly require Noetherian or finite-presentation assumptions.

Step 6 uses ordinary module proper base change again, the equality p_f,1 phi_z=i from Step 1, and the derived adjunction from the nearby-cycle definition. The two fibre coefficients are the same exact inverse image of B, and the mate-pasting node identifies the specified first-projection arrow with the identity on this common complex. Oriented conservativity then detects invertibility. No constructibility, invertibility of m on S, bounded cohomological dimension or finite Tor hypothesis entered either consequence.

For small cases I checked h=id (all maps become identities), X empty (both sides are zero), m=1 (the zero coefficient ring), a geometric point with field larger than the strict-local residue field, a nontrivial specialization t to s, and an arbitrary non-Noetherian base after restriction to affine neighbourhoods. For the new continuity statement I checked constant inverse systems, a single terminal stage, empty X or Y, arbitrary negative shifts of a sheaf, and a constant ring of infinite cardinality killed by m. The bounded-below condition is essential to the usual finite-diagonal hypercohomology passage; the statement keeps it. It asserts continuity for a fixed-stage complex, not descent of every object at the limit.

I checked B1–B10: the new node has a self-contained TeX statement, no proof sketch, no proof steps or proof dependencies, honest searches and no claimed Mathlib match, and the correct blueprint ancestor and via list. I checked C1–C8: each used non-elementary fact has an explicit node, the cited statements have been read, the exact verbatim statements are in citations.json, and off-unit generic inputs are declared. I checked D1–D5: the item itself carries the localization, local-germ, proper-base-change and two exchange arguments; the new node contains no proper-fibre conclusion. I checked E1–E7 as described above; no source statement or target was weakened. Each non-elementary step is under 2000 characters, and I separately inspected the two localization steps for a hidden comparison: their substantive limit comparison is exactly the new node, while their sections/stalk and composition comparisons are explicitly cited.

## Unfinished work

No clause of the item's split is left unfinished. The new continuity lemma is deliberately statement-only for its own future one-level split. No Mathlib leaves were created. The required server dry run and push follow this report.

## Not duplicates

lem-trf-oriented-derived-cohomology-continuity vs def-weil-pbc-arrows-functor: The existing The functor taking a category to its set of arrows is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs def-weil-pbc-filtered-colimit-hom-fibers: The existing Hom fibers in the filtered arrow colimit is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs def-weil-pbc-finite-precoverage: The existing Finite indexed precoverage closure axioms is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-affine-etale-colimit-presentation: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-affine-etale-finite-colimit-construction: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-affine-etale-site-colimit: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-cohomology-colimit-of-sites: The existing theorem assumes a given colimit presentation of sites and states abelian-sheaf cohomology continuity. The new node has geometric qcqs-diagram hypotheses and must establish that the limiting oriented triple site has that presentation, then pass to bounded-below module complexes.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-of-sites: The existing The colimit of an inverse system of sites with finite coverings is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-of-sites-cech-complex: The existing The Cech complex of the colimit sheaf on a colimit of sites is the colimit of the Cech complexes is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-of-sites-cech-complex-colimit-data: The existing Canonical stage Cech complex colimit cocone is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-of-sites-cech-complex-transport: The existing Transport of finite covering products is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-of-sites-reduced: The existing Category colimit site construction after category witness is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-of-sites-sections: The existing Sections of the colimit sheaf on a colimit of sites (degree 0) is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-presieve-indexed-presentation: The existing Finite presieve reindexing over a fixed stage target is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-cech-cocone-construction: The existing Canonical cocone of stage Cech complexes is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-axioms: The existing Finite covering axioms for the transported precoverage is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-axioms-finitebasechange: The existing Finite base change in the colimit precoverage is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-axioms-finitecomposition: The existing Finite composition in the colimit precoverage is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-axioms-hasisos: The existing Singleton isomorphisms cover in the colimit precoverage is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-axioms-haspullbacks: The existing Covering pullbacks exist in the colimit category is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-construction: The existing Finite covering axioms and continuity on a fixed category colimit is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-continuity: The existing Continuity and pullback preservation for the transported precoverage is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-families-at-stage: The existing Finite one-layer covering lifting over fixed stage targets is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-families-lift: The existing Simultaneous finite covering-family lifting is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-covering-pullback-stage-presentation: The existing Common stage presentation of prescribed covering pullback squares is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-finite-product-sections: The existing Finite products of stage sections on a colimit site is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-finite-restriction-family-lift: The existing Finite restriction arrows and triangles lift at one refinement is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-site-scalar-section-comparison: The existing Scalar stage-section representatives and eventual zero is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-acyclic-replacement: The existing Acyclic replacement and pointwise boundaries for a colimit-site coefficient system is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-boundary-diagrams: The existing Boundary diagrams of normalized compatible short exact systems is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-class-descent: The existing Finite-stage existence of classes for cohomology on colimit sites is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-cohomology-diagram: The existing Cohomology diagram and comparison cocone for a unital-in-degree coefficient system is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-connecting-ladder: The existing Lower-degree connecting ladder for colimit-site cohomology is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-corrected-lift: The existing Corrected lower-degree lifts for vanishing classes is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-degree-zero-descent: The existing Degree-zero finite-stage existence on a colimit of sites is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-eventual-vanishing: The existing Finite-stage detection of vanishing for cohomology on colimit sites is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-exact-ladder: The existing Exact cohomology ladder before finite-stage correction is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-short-exact-systems: The existing Normalized compatible short exact coefficient systems is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-colimit-sites-zero-comparison-injective: The existing Degree-zero stage comparison is injective is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-acyclic-replacement: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-affine-corrected-lift: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-affine-degree-zero-kernel: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-affine-eventual-zero: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-affine-exact-ladder: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-cohomology-affine-comparison: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-cohomology-class-descent: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-cohomology-connecting-ladder: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-cohomology-degree-zero-descent: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-cohomology-eventual-vanishing: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-compatible-exact-systems: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-finite-cech-coefficient-composition: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-finite-cech-coefficient-data: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-finite-cech-coefficient-differential: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-finite-cech-coefficient-identity: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-finite-cech-coefficient-laws: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-finite-cech-coefficient-leg: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-finite-cech-colimit: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-finite-cech-complex-colimit: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-finite-cech-stage-data: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-injective-colimit-acyclic: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-scalar-section-colimit: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-scalar-section-continuity: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-scalar-section-representatives: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-limit-scalar-section-zero-eventually: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-etale-pullback-section-composition: This existing ordinary-etale construction/calculation concerns scheme sites; the new statement concerns the oriented triple site of three simultaneous limits and arbitrary bounded-below constant-module coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-abelian-groups-exact: The existing Filtered colimits of abelian groups are exact is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-categories: The existing The filtered colimit of a system of categories; finite diagrams and morphisms come from a stage is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-category-descent: The existing Finite-diagram and Hom descent from the object and arrow colimits is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-category-finite-functor-lift: The existing Construct a finite functor from finite-list lifts is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-category-finite-lift: The existing Finite object and arrow lists lift with relations is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-category-iso: The existing Invertible representatives from lifting finite functors is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-category-list-equality: The existing Finite object and arrow lists agree at a common refinement is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-category-structure: The existing The category structure induced on the filtered object colimit is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-fiber-laws: The existing Category axioms for filtered arrow fiber operations is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-fiber-operations: The existing Identity and composition on filtered arrow fibers is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-finite-iso-lift: The existing Finite isomorphisms lift above fixed stage objects is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-functor-descent: The existing Descent of compatible functors from an object-and-arrow filtered colimit is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-iso-presieve-representation: The existing Isomorphisms in the filtered colimit category have covering stage representatives is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-preserves-pullback: The existing A pullback stable at later stages is preserved in the category colimit is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-pullback-exists: The existing Factorization existence for a stable pullback image is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-filtered-colimit-pullback-hom-ext: The existing Joint monicity of stable pullback image projections is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-weil-pbc-fixed-site-degree-zero-representatives: The existing Degree-zero representatives for a filtered colimit on a fixed site is abstract finite-site/category/sheaf bookkeeping; it does not identify the geometric oriented triple site of simultaneous scheme limits or state its bounded-below module cohomology continuity.

lem-trf-oriented-derived-cohomology-continuity vs lem-trf-oriented-affine-neighbourhood-limit: the existing statement identifies limits of ordinary schemes U times_V W and their pointed index category; it gives no cohomology theorem for arbitrary sheaves on the oriented site.

lem-trf-oriented-derived-cohomology-continuity vs lem-trf-oriented-point-cohomology: the existing statement computes stalks only for R psi_* of a complex on X times_S Y; continuity here applies to arbitrary oriented-site coefficients.

lem-trf-oriented-derived-cohomology-continuity vs lem-trf-qcqs-oriented-triple-presentation: the existing statement gives a finite-cover triple site and inverse images of triples, not inverse-limit descent of its objects/arrows/coverings or derived cohomology.
