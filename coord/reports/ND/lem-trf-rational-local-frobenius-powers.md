# Worker report: lem-trf-rational-local-frobenius-powers

## Files written

- dag/nodes/sec-trace-formula/lem-trf-rational-local-frobenius-powers.json: statement, split into seven steps; unchanged statement; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-completed-stalk-reparametrization-coherence.json: statement-only unsplit auxiliary lemma; no Mathlib match. It concerns completed stalk functors and source automorphisms without any Weil structure or periodic point.
- citations.json records the exact statement excerpts used by all eleven step citations. searches.jsonl contains the actual msearch invocations. The notes/write_split.py script only generates this sandbox's nodes and citations.

## Attachments

None. The exact blueprint tag has no match in WeilConjectures/. I also searched Frobenius/stalk/power/conjugacy terminology, and read WeilSheaf/LocalFrobenius.lean:76–140, WeilSheaf/StalkCharpoly.lean:584–650 and the transport definitions in WeilSheaf/StalkFrobenius.lean and WeilSheaf/Stalk.lean. AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAtGeometricFiberPoint has sorry at LocalFrobenius.lean:93; its WeilComplex wrapper is about cohomology sheaves over PadicAlgCl, not E-linear isomorphisms of entire stalk complexes. The charpoly and trace power results are likewise weaker and at the sheaf/PadicAlgCl stage. They do not attach to this item. No declaration was found for the completed comparison lemma.

## WANTED

None. The blueprint proof, Stacks sites.tex and proetale.tex, and the supplied comparison-node interfaces are available. The proof is marked agent-written: Stacks supplies the ordinary stalk formulas, not the full completed-adic enhancement.

## Corrections and scope

The imported statement is retained exactly. Its source reparametrization is already correct. There is no statement dispute. The misleading shortcut in the blueprint is “those proofs apply verbatim”: lem-trf-local-frobenius-conjugacy and lem-trf-frobenius-degree-formula assume finite coefficients and an invertible finite Weil structure, so their operator clauses cannot be applied to phi_E or to a noninvertible integral denominator-clearing map. The degree lemma states only a trace equality, also insufficient for the operator identity requested here.

The replacement below the fixed unit route explicitly constructs the comparisons and transports, identifies the actual normalized fixed-point operator, and proves the cyclic-product identities. It uses the finite conjugacy node only for its geometry-only clause (1), instantiated with the zero finite strict Weil complex. It uses no trace law. The chapter and unit are unchanged, and this item is not the unit's key node, so no unit record is changed.

## What remains

This stage-1 item is fully split. The new completed comparison lemma is intentionally not split, has no proof or proof dependencies, and enters the queue as one new statement-only item. No Lean was written or compiled. There are no new Mathlib leaves.

## Not duplicates

lem-trf-completed-stalk-reparametrization-coherence vs lem-trf-proetale-pullback-stalk-coherence: the existing node is for ordinary derived complexes over a finite constant ring; the new node identifies completed integral and raw rationalized fibers, including the specified simultaneous-tower normalization and point-sections transport.

lem-trf-completed-stalk-reparametrization-coherence vs lem-pur-proetale-inverse-image-stalk: the existing node is an inverse-image/stalk comparison for sheaves of sets or abelian groups, with naturality; it does not address completed module pullback, rational morphisms, composition coherence or the prescribed source-automorphism point transport.

lem-trf-completed-stalk-reparametrization-coherence vs lem-cbc-proetale-classical-stalk: the existing node identifies an ordinary sheaf stalk with evaluation on a strict localization and gives exactness; it states none of the completed comparisons or their equations.

lem-trf-completed-stalk-reparametrization-coherence vs lem-cbc-proetale-comparison-stalk: the existing node compares etale and pro-etale stalks of an ordinary sheaf under nu^*; the new node has neither that site-comparison functor nor that conclusion.

lem-trf-completed-stalk-reparametrization-coherence vs lem-cbc-proetale-sheafification-geometric-stalk: the existing node preserves a geometric stalk under abelian sheafification; it has no completed pullback or source-automorphism coherence conclusion.

lem-trf-completed-stalk-reparametrization-coherence vs lem-weil-pbc-inverse-image-stalk-germ: the existing node specifies a unit/germ comparison for ordinary abelian etale sheaves; the new node concerns completed pro-etale module complexes and their rationalizations, not this unit formula.

lem-trf-completed-stalk-reparametrization-coherence vs lem-weil-pbc-finite-etale-unit-stalk-inclusion: the existing node specifies the reverse-adjunction unit for a finite etale morphism as a stalk inclusion; no such unit or finite etale hypothesis occurs in the new node.

lem-trf-completed-stalk-reparametrization-coherence vs lem-coef-exponential-dependent-product-representation: the existing node represents dependent products by mapping-space homotopy fibers in a quasicategory; it does not state any stalk theorem. The shared tag is incidental to its source list.

lem-trf-completed-stalk-reparametrization-coherence vs lem-coef-infinity-iterated-slice-mapping: the existing node identifies coherent iterated-slice mapping spaces; the new node has no slices or mapping-space conclusion.

lem-trf-completed-stalk-reparametrization-coherence vs def-coef-space-base-change: the existing node defines a base-change functor between slices of the infinity category of spaces; it neither defines nor proves completed stalk comparisons.

Additional concept searches found lem-per-adic-heart-pullback-fibres (heart-level t-exactness/fibers), lem-wf-rational-stalk-exact (short exact sequences of rational Weil sheaves), and lem-weil-local-frobenius-conjugacy-class (cohomology-stalk conjugacy). None states the new coherence lemma. lem-trf-integral-pullback-comparison-realization gives composition comparisons before taking point sections, and lem-trf-local-frobenius-transport-normalization addresses a fixed rational point and its Frobenius, not arbitrary source reparametrization. Both are reused, not recreated. The new lemma is not a clause of the item: it has no Weil map, no closed point, and no operator/power/conjugacy assertion.

## Review by ND

I read the item's main-20261015 thm-trf-l-function-euler-product.proof.md, Step 1 Local powers, the two finite-coefficient proof files it invokes, and the chapter and sk-thm-trace-transport records. The unit's Step 5 requires precisely the local-power grouping implemented here. I read Stacks Tag 05V1, sites.tex lemma-point-morphism-sites, its proof using Tag 0F4F lemma-point-functor, and Tag 0993, proetale.tex lemma-classical-point with the preceding exactness paragraph. These give the finite germ comparisons. The new lemma explicitly states its extra completed construction and is attributed to an agent refinement, rather than attributing that entire assertion to those Stacks tags.

For the new lemma I checked the full statements of lem-trf-proetale-pullback-stalk-coherence, lem-trf-integral-pullback-comparison-realization, def-weil-finite-coefficient-point and def-weil-inverse-image-pullback-comparison. Its intended argument realizes the natural finite c/r diagrams on the simultaneous strict quotient systems, using the given comparison families, and then rationalizes. One must retain these diagram maps and their homotopies, not infer equality of derived morphisms from equality of separate reductions. At the point, the restriction/insertion map sends the same section to the germ with the source lift reparametrized by delta, giving c j = r; successive source maps have the ordinary composition law. Sections preserve the products in the cone realization, and the finite maps preserve quotient transitions. This is a genuine comparison/normalization lemma requiring later proof, not a two-line elementary consequence of a definition. I corrected a draft quantifier so J_v(M) always has M on the target of v. I also made the contravariant order explicit: delta followed by epsilon on the source corresponds to beta composed with alpha on fields. The statement has no proof sketch, proof steps, or proof dependencies.

Step 1: I opened lem-trf-local-frobenius-conjugacy and used exactly clause (1), which enumerates all lifts and identifies the rational points when e divides m. The zero complex over A_1 is bounded constructible of finite Tor amplitude and has the unique invertible zero Weil map; hence the strict-Weil hypothesis in def-trf-strict-weil-complex is satisfied without placing any condition on the given phi_E. def-trf-scheme-frobenius gives the affine formulas for both g and Phi. Substitution yields Phi v = g v Spec(sigma), with the correct source, and hence g^m v = v Spec(gamma^m) at a periodic lift. No coefficient-dependent operator conclusion was taken from the finite lemma.

Step 2: I checked the new lemma's c composition equation, r-c square, identity maps and r composition order. Inverting these equations gives the displayed Q_{i+j} formula, with source M_{G^{i+j}v} and target (P_i P_j M)_v under the specified comparison. The field maps here are powers of sigma and commute. The explanation is the elementary substitution of those three stated equations, not a new unproved stalk-coherence claim.

Step 3: prop-trf-rational-frobenius-integral-model explicitly defines the E-stage iterates as the ordered product of pullbacks of phi_E. lem-trf-integral-pullback-comparison-realization explicitly says its composition maps are associative and unital and their rationalizations satisfy the same equations. The written induction splits that ordered list without using lem-trf-iterated-weil-cocycle, whose statement is only finite-coefficient. def-weil-weil-sheaf-complex explicitly requires phi_E to be an isomorphism in D^b_c(X,E); applying functors to it gives the inverses needed here.

Step 4: I checked the new lemma's naturality for arbitrary rational morphisms, not merely integral morphisms. Applying it to phi^{[j]} and combining steps 2 and 3 gives the three-factor calculation for T_i T_j. All products have source K_{E,G^{i+j}v} and target K_{E,v}; the isomorphisms are not claimed to be periodic. This part is an elementary calculation from already stated identities.

Step 5: I opened lem-trf-local-frobenius-transport-normalization and read its full statement. It identifies the actual scheme/Galois-normalized tau with successive point transports at the finite, completed-integral and E stages, under precisely the strict-system composition families used by the new lemma. Its hypotheses require the given finite-field datum, ell unequal p, a separated finite-type X_0 and y rational over F_{q^m}; all hold here. Its statement explicitly includes integral realization and rationalization, so no coefficient stage is silently identified. The new lemma's c j = r equation, with its compatibility with v and repeated automorphisms, turns this transport into r_{v,gamma^m} after c. The inverse r at g^m v has source K_v and is therefore the same map, with no scalar normalization freedom. The E-stage operator formula of prop-trf-rational-frobenius-integral-model then gives F_{y,m}=T_m^v. Neither cited result requires an integral Weil isomorphism.

Steps 6 and 7: these cite no new facts. I checked the induction T_{re}^v=(T_e^v)^r using G^e v=v, then both decompositions of T_{i+m}^{z_0}. Their typed equality is T_i F_{y_i,m}=F_{y_0,m} T_i, so multiplying on the left by T_i^{-1} gives the requested orientation T_i^{-1} F_x^r T_i. The same T_i works for every r because it was constructed before choosing m. All starting lifts are exhausted by step 1.

I checked B1–B9: the new node is statement-only, introduces the schemes, points, rings, categories and map normalizations, has definition dependencies and explicit Stacks tags/labels, uses single TeX escapes, and has blueprint ancestry through this item. Whole-DAG and blueprint searches by reparametrization, pullback-stalk, completed stalk and the shared Stacks tags found the comparisons distinguished above. Every recorded Mathlib query was run through msearch.py; the second semantic phrasing and inspected candidates did not provide the completed theorem. TopCat.Presheaf.stalkPullbackIso, Topology/Sheaves/Stalks.lean:335, is for topological presheaves. Point.sheafFiberComapIso, CategoryTheory/Sites/Point/Comap.lean:69, is an ordinary sheaf-fiber comparison, and SheafOfModules.pullbackComp, Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:167, has no completed strict-system or point-transport normalization. They are ingredients, not one-line specializations of the new result.

For C1–C4 and D1–D4 I opened every cited statement and copied the relevant verbatim excerpts into citations.json. Every non-elementary step is supplied by a stated node, and the item retains the actual cocycle, cyclic-product and conjugacy arguments. It uses no proof internals of a dependency. The new node's statement is independent of all local Frobenius conclusions. The report declares the off-unit generic geometry/operator tools without changing maintainer-owned tool_uses. No source route through SGA is used.

For E1–E6 I tested the point case X_0=Spec F_q: g z is Spec(gamma), so the reparametrization is indispensable even at e=1. The formula then reduces to ordinary powers of the rational Weil map. For K_E=E^2 with phi_E=diag(1,ell), the integral map may fail to be invertible; the proof still gives rational conjugacy. I tested e=2 with unequal-dimensional notation for the two stalk objects and isomorphisms a_0:V_1->V_0, a_1:V_0->V_1: the two one-circuit maps are a_0 a_1 and a_1 a_0, and a_0^{-1}(a_0 a_1)^r a_0=(a_1 a_0)^r. I checked K=0, r=1, i=0, identity scheme maps, alpha=1, inverse source automorphisms, and a shifted complex; no dimension or degree-zero assumption enters. Empty X_0 has no closed x, so the assertion is vacuous. Every proof step is shorter than 2000 characters; the non-elementary comparison has been isolated as the one new node. No unresolved mathematical correction remains in the item.
