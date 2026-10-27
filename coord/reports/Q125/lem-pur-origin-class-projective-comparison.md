# Q125 repair: lem-pur-origin-class-projective-comparison

1. Files written: dag/nodes/sec-smooth-purity/lem-pur-origin-class-projective-comparison.json (existing statement unchanged, five assembly steps); lem-pur-closed-support-open-counit.json (new statement, unsplit, no Mathlib match); lem-pur-compact-point-source-normalization.json (new statement, unsplit, no Mathlib match). Both new nodes are independent statement-only tasks with no proof or proof dependencies. citations.json contains verbatim statement excerpts for every use; searches.jsonl retains real search results. returned-proof.json and the appendix below preserve the old proof.
2. Attachments: none. The upstream WeilConjectures search for the blueprint tag and origin/projective class terminology gave no exact project declaration. The existing Sheaf.AlgebraicGeometry.OriginClassProjectiveComparison theorem origin_class_projective_comparison ends in sorry at line 105 and cannot be attached.
3. WANTED: none.
4. The returned split was mathematically detailed but had 4967 characters of proof and no separate tasks. This repair changes the DAG granularity as explicitly required. It does not dispute or weaken the statement, change its coefficient category, or modify Lean. No source error was found.
5. Nothing mathematically remains unfinished for the one-level split. The two new unsplit statements deliberately await separate workers.

## Repair of the numbered return

The return has one substantive request: spread the old argument into at least two comparable new statement-only nodes and assemble them in at most 3000 characters. The new counit node collects old steps 2 and 3 and the formal naturality portion of old step 4. It introduces arbitrary schemes, an arbitrary closed-support module sheaf, and an arbitrary derived target, so it is not the Kummer comparison or one of its special clauses. The new compact-source node collects old step 5: canonical derived global sections of a rational closed point and the exact section-one identity used in old step 6. It applies on an arbitrary proper Noetherian scheme, does not mention a divisor, twist or Kummer class, and assumes the support counit invertible rather than repeating the first task. Their statements have comparable size (about 1600 and 1900 characters). The parent retains old step 1 verbatim, explicitly obtains the supported-Kummer restriction, applies the new generic counit identity, applies the new compact-source identity, and performs old step 6's Chern-class assembly. The final five steps total 2286 characters. Every step is below 2000 characters.

## Review by Q125

I read the current main-20261015 rank-one Thom proof, Step 2, and the old sk-prop-an unit, particularly Step 5(d), lines 248--257. The current proof's passage from supported to compact class is the reason this comparison is needed; the old unit supplies the precise positive Chern normalization. I also read the current Cartier-Kummer proof's relative-cone construction, pullback paragraph and forgetting-support paragraph. This is the lecture-notes/blueprint route, and no SGA source is used. I read the chapter and unit records, the three-level route rules, and both copies of delivery-errors B--E.

For the counit task I read Stacks etale-cohomology.tex Tag 03S3 (definition-extension-zero), including the module-sheaf adjunction and its underived section formula, and Tag 095L (lemma-ses-associated-to-open) with its geometric-stalk proof. I read derived.tex Tag 015F (lemma-right-derived-exact-functor), which says exact functors are computed termwise even in unbounded categories. This supplies exact localization, while the actual localized adjunction/counit is specified by the existing def-weil-exact-derived-adjunction. The generic task retains the sheaf restriction rho, its identity on B of the fibre product, vanishing off k(Z), invertibility of the actual e, and naturality for every derived arrow, including shifted targets. The previous proof's support argument is preserved below: F vanishes on an open neighbourhood of the complement because k(Z) lies inside U; applying the open/closed exact sequence makes e invertible. This is a separate argument and not an arbitrary isomorphism between the two objects. I removed an unnecessary Noetherian hypothesis from this generic statement; its argument works on arbitrary schemes. It is not just counit naturality: that is in Mathlib, whereas the small-etale support/restriction and localization normalization are additional content.

For the compact-source task I read etale-cohomology.tex Tags 03QP (proposition-finite-higher-direct-image-zero), 03QT (theorem-equivalence-sheaves-point), and 03QU (lemma-compare-cohomology-point); sites-cohomology.tex Tags 03FD (lemma-cohomology-modules-abelian-agree) and 0D6E (lemma-derived-pushforward-composition). The closed support is finite, the composite qk is the identity, and the field is algebraically closed. These facts give RΓ(Y,F) concentrated in degree zero with canonical H0=A. The new statement asserts the derived isomorphism beta, not merely isomorphisms degree by degree. The normalization is the restriction of the actual constant section 1, so beta RΓ(u) eta=id; since both derived objects are A[0], the identity is determined by the value on 1 in the heart. Its inverse composed with RΓ(e) gives lambda and the identity needed in the parent. The new statement keeps the proper compactification and Noetherian assumptions needed by def-amb-etale-compact-support and explicitly defines Noetherian. It assumes e is invertible so the two new tasks can be proved independently.

Parent step 1 uses exactly def-pc-divisor-line-bundle (dual Cartier ideal) and def-pc-projective-space-twist (positive transition rule). I checked the frames f0=t, f1=1, g0=t^-1 g1 and section coordinates t,1, so this is x1 in O(1), not O(-1). It is the same elementary calculation as the returned proof.

Parent step 2 takes the canonical restriction and the actual invertible e from lem-pur-closed-support-open-counit. The hypotheses hold for the two closed embeddings of Spec Omega into A1 and P1 and the standard open chart. This node states both the sectionwise restriction and the actual localized-counit normalization used by the step.

Parent step 3 uses the pullback clause of lem-asd-ordinary-supported-kummer, not its proof: the restricted origin is still Cartier since its equation t is a non-zero-divisor. lem-asd-etale-finite-twist-pullback gives the roots/tensor identification of the target including its shift. The counit node explicitly states epsilon_M j!c_U = c e for arbitrary derived M, so it applies to L_P[2]. This preserves the old prohibition on inferring an equality of derived arrows only from restriction. Each quoted statement was opened and checked.

Parent step 4 uses the exact lambda and closed-unit identity asserted by lem-pur-compact-point-source-normalization. P1 is proper and Noetherian over Spec Omega and q k=id. The invertibility assumption is supplied by step 2. The finite coefficient ring remains an arbitrary finite commutative ring killed by N, with no flatness assumption.

Parent step 5 uses the actual compactification functor on morphisms in def-amb-etale-compact-support and the formula c_D u_D=c1(O(D)) in the statement of lem-asd-ordinary-supported-kummer. Applying the functor to the step-3 equality and substituting the step-4 identity yields precisely the displayed expression; step 1 gives O(D0)=O(1). There is no generator rescaling and no identification of supported with compact cohomology. citations.json was checked as literal substrings of these statements, not paraphrases of their proofs.

Edge cases checked: A=0 gives zero objects and the unique invertible map 0→0; section-one normalization is still meaningful since 1=0. N=1 forces A=0 and causes no false nonzero-generator assertion. For positive characteristic, N is invertible as required by the Kummer node. A need not be flat over Z/N: the supported Kummer node already uses derived scalar extension. For the generic support lemma, Z empty and U=Y give the expected zero and identity cases, and arbitrary B need not have finite stalks. For the compact-source lemma, disconnected Y does not affect the section restriction to the one closed point; the rational point has precisely residue field Omega, not a nontrivial residue extension.

I searched the full DAG by statements and Stacks sources, and blueprint_refs.py by closed support/counit, extension by zero, compact point, supported closed, point normalization, geometric point cohomology and closed point; none states either full new task. Existing ordinary finite-open comparison supplies a sheaf-level ingredient, not its actual localized derived counit on all shifted targets; the pro-etale extension-coherence node uses a different site. The geometric-point cohomology node supplies only the point computation, not the closed-unit and compact-source derived comparison. The broader product/proper-support compatibility node has fixed coefficient-field conventions, finite-Tor product assertions and an image-of-supported-class map; it does not state the section-one source identification on the present arbitrary algebraically closed field and arbitrary finite A. Existing declarations under Sheaf are not upstream attachments, and the parent declaration has sorry.

The Mathlib searches were all run with msearch.py. I read every returned signature: Scheme.Modules.restrictAdjunction concerns Zariski structure-sheaf modules and the other direction of adjunction; stalkSkyscraperSheafAdjunction concerns topological sheaves; Γevaluation and germ_stalkClosedPointTo_Spec concern the structure sheaf; none states the etale derived source assertion. The Loogle counit_naturality hit is genuine general naturality, but does not imply the support statement in one specialization. Both semantic services, Loogle, and source grep have results recorded literally with digests. The second semantic phrasing was LeanSearch for each new task, independent of the first LeanFinder question.

## Not duplicates
lem-pur-closed-support-open-counit vs def-pe-finite-discrete-presentation-encoding: the existing statement concerns Specified finite-discrete section-action presentation encoding; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs lem-sbc-higher-image-raw-pullback-composition: the existing statement concerns Composition of explicit raw cohomology pullbacks; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs src-sbc-exact-functor-plus-unit: the existing statement concerns The bounded-below right-derived unit of an exact functor is invertible; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs lem-sbc-higher-image-raw-pullback-identity: the existing statement concerns Identity of explicit raw cohomology pullback; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs def-sbc-tower-derived-evaluation-interchange: the existing statement concerns Canonical exact derived tower evaluation interchange; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs def-weil-exact-derived-adjunction: defines localization of a supplied exact adjunction; it does not assert restriction to a closed support or invertibility of its open counit.

lem-pur-closed-support-open-counit vs def-coef-system-derived-transition: the existing statement concerns Canonical localized semilinear transitions of strict coefficient systems; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs def-sf-scalar-reduction-categories-restriction: the existing statement concerns Completed and finite coefficient module categories and scalar restriction; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs lem-weil-isomorphism-derived-pullback-equivalence: the existing statement concerns Derived pullback along an isomorphism of schemes is an equivalence of ambient derived categories; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs def-coef-tower-derived-evaluation-transition: the existing statement concerns Canonical localized transitions between derived tower evaluations; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs def-sf-open-normalization-data: the existing statement concerns Geometric and operation data for open tensor normalization; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs lem-pc-open-stalk-representative-coherence: the existing statement concerns Exact open stalk comparison on arbitrary representatives; it supplies no closed-support restriction/counit theorem on small-etale modules and no identity for arbitrary derived target arrows.

lem-pur-closed-support-open-counit vs lem-weil-pbc-open-closed-short-exact: states the complementary open/closed sequence for an arbitrary sheaf; the new node establishes its application to a separate closed support inside the open and normalizes the derived counit.

lem-pur-closed-support-open-counit vs lem-weil-pbc-extension-by-zero-adjunction: states the sheaf adjunction; the new node adds the support isomorphism and its actual derived-morphism identity.

lem-pur-closed-support-open-counit vs lem-weil-pbc-geometric-point-cohomology: computes abelian cohomology on Spec of an algebraically closed field; the new node gives a derived A-module isomorphism for a closed pushforward on Y and its section-one compact-source identity.

lem-pur-closed-support-open-counit vs lem-weil-pbc-etale-module-cohomology-forget: compares degreewise module and abelian cohomology; the new node computes the closed-point derived source and its exact unit normalization.

lem-pur-closed-support-open-counit vs lemma-weil-pbc-finite-direct-image-exact: states finite abelian direct-image exactness; the new node adds the closed-point global sections, module coefficients, actual unit, and compact-source normalization.

lem-pur-closed-support-open-counit vs def-weil-pbc-derived-direct-image-composition: defines the conjugate composition isomorphism of abelian derived direct images; it does not compute a compact-source unit at the point.

lem-pur-closed-support-open-counit vs lem-sfb-etale-locally-closed-extension-comparison: gives normalized sheaf-level finite-coefficient locally closed extension comparison; the new node treats arbitrary A and B and the actual exact derived counit on arbitrary shifted targets.

lem-pur-closed-support-open-counit vs lem-sfb-locally-closed-module-extension-coherence: concerns pro-etale module-sheaf extension coherence and explicitly makes no derived assertion; the new node is an ordinary small-etale derived counit statement.

lem-pur-closed-support-open-counit vs lemma-weil-pbc-finite-pushforward-extension-zero: gives the underived abelian finite-open isomorphism in a cartesian square; it does not state the module and actual localized-counit identity on arbitrary derived targets.

lem-pur-closed-support-open-counit vs lem-cbc-open-closed-recollement: gives a bounded-below complementary-pair triangle; the new node handles the closed support lying inside the open with its canonical section formula and all unbounded derived targets.

lem-pur-closed-support-open-counit vs lem-pur-compact-product-proper-support-compatibility: uses fixed A_E,r over the standing field and concerns products and supported-class images; neither the arbitrary-field compact-source beta/lambda normalization nor the all-A all-B exact derived support counit is its statement.

lem-pur-closed-support-open-counit vs lem-weil-stratum-ambient-hom: states a derived internal-Hom identity for a locally closed immersion and exceptional inverse image, not the actual open counit or a normalized compact point source.

lem-pur-closed-support-open-counit vs lem-pur-origin-class-projective-comparison: the parent is a Kummer divisor/positive Chern comparison; the new generic task contains no Kummer or Chern conclusion and is only one independent argument used in its assembly.

lem-pur-compact-point-source-normalization vs lem-pe-left-module-derived-evaluation-forget: the existing statement concerns Derived evaluation of arbitrary left-module sheaves commutes with forgetting scalars; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs lem-pe-ringed-site-derived-evaluation-slice: the existing statement concerns Derived module evaluation is abelian cohomology on the slice; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs def-sbc-etale-complex-cohomology-presentation: the existing statement concerns Abelian complex presentation of a cohomology cocone; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs sbc-lem-higher-image-raw-affine-image-rep: the existing statement concerns Affine raw module-cohomology classes have stage representatives after comparison; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs lem-sbc-raw-module-restricted-abelian-nonnegative: the existing statement concerns Scalar-forgetting comparison (nonnegative); it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs lem-sbc-raw-module-scalar-hom-composite-formula: the existing statement concerns Scalar Hom map after module raw pullback expansion; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs lem-sbc-coefficient-higher-direct-image-zero: the existing statement concerns Restriction of scalars detects vanishing of higher direct images; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs lem-sbc-raw-scalar-hom-evaluation: the existing statement concerns Evaluation of the explicit additive scalar Hom map; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs sbc-lem-higher-image-colimit-comparison-epi: the existing statement concerns Local surjectivity of the canonical higher-image sheaf-colimit comparison; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs lem-sbc-derived-source-comparison-injective: the existing statement concerns Derived source comparison detects classes; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs lem-sbc-restrict-scalars-injective-direct-image-acyclic: the existing statement concerns Restricted injective module sheaves are acyclic for étale direct image; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs lem-sbc-constant-module-higher-direct-image-local-vanishing: the existing statement concerns Vanishing for constant module coefficients from local cyclic cohomology annihilation; it does not compute RΓ(Y,k_*A) as A[0] together with the closed-unit and compact-source section-one identities.

lem-pur-compact-point-source-normalization vs def-weil-exact-derived-adjunction: defines localization of a supplied exact adjunction; it does not assert restriction to a closed support or invertibility of its open counit.

lem-pur-compact-point-source-normalization vs lem-weil-pbc-open-closed-short-exact: states the complementary open/closed sequence for an arbitrary sheaf; the new node establishes its application to a separate closed support inside the open and normalizes the derived counit.

lem-pur-compact-point-source-normalization vs lem-weil-pbc-extension-by-zero-adjunction: states the sheaf adjunction; the new node adds the support isomorphism and its actual derived-morphism identity.

lem-pur-compact-point-source-normalization vs lem-weil-pbc-geometric-point-cohomology: computes abelian cohomology on Spec of an algebraically closed field; the new node gives a derived A-module isomorphism for a closed pushforward on Y and its section-one compact-source identity.

lem-pur-compact-point-source-normalization vs lem-weil-pbc-etale-module-cohomology-forget: compares degreewise module and abelian cohomology; the new node computes the closed-point derived source and its exact unit normalization.

lem-pur-compact-point-source-normalization vs lemma-weil-pbc-finite-direct-image-exact: states finite abelian direct-image exactness; the new node adds the closed-point global sections, module coefficients, actual unit, and compact-source normalization.

lem-pur-compact-point-source-normalization vs def-weil-pbc-derived-direct-image-composition: defines the conjugate composition isomorphism of abelian derived direct images; it does not compute a compact-source unit at the point.

lem-pur-compact-point-source-normalization vs lem-sfb-etale-locally-closed-extension-comparison: gives normalized sheaf-level finite-coefficient locally closed extension comparison; the new node treats arbitrary A and B and the actual exact derived counit on arbitrary shifted targets.

lem-pur-compact-point-source-normalization vs lem-sfb-locally-closed-module-extension-coherence: concerns pro-etale module-sheaf extension coherence and explicitly makes no derived assertion; the new node is an ordinary small-etale derived counit statement.

lem-pur-compact-point-source-normalization vs lemma-weil-pbc-finite-pushforward-extension-zero: gives the underived abelian finite-open isomorphism in a cartesian square; it does not state the module and actual localized-counit identity on arbitrary derived targets.

lem-pur-compact-point-source-normalization vs lem-cbc-open-closed-recollement: gives a bounded-below complementary-pair triangle; the new node handles the closed support lying inside the open with its canonical section formula and all unbounded derived targets.

lem-pur-compact-point-source-normalization vs lem-pur-compact-product-proper-support-compatibility: uses fixed A_E,r over the standing field and concerns products and supported-class images; neither the arbitrary-field compact-source beta/lambda normalization nor the all-A all-B exact derived support counit is its statement.

lem-pur-compact-point-source-normalization vs lem-weil-stratum-ambient-hom: states a derived internal-Hom identity for a locally closed immersion and exceptional inverse image, not the actual open counit or a normalized compact point source.

lem-pur-compact-point-source-normalization vs lem-pur-origin-class-projective-comparison: the parent is a Kummer divisor/positive Chern comparison; the new generic task contains no Kummer or Chern conclusion and is only one independent argument used in its assembly.

lem-pur-closed-support-open-counit vs lem-sc-exact-functor-higher-derived-vanishing: only gives vanishing of positive right derived functors of an exact functor; no support, restriction or actual counit is asserted.

lem-pur-closed-support-open-counit vs lem-pc-ext-exact-functor-square: compares Ext maps in a supplied square of exact functors; it assumes the comparison isomorphism and has no support or adjunction assertion.

lem-pur-closed-support-open-counit vs lem-pc-ext-restriction-map-calculus: gives identities for supplied Ext comparison isomorphisms; it does not construct the supported restriction isomorphism or prove its counit invertible.

lem-pur-closed-support-open-counit vs lem-pc-open-tensor-restriction-representative: identifies a pinned tensor restriction representative; no closed pushforward or support counit is involved.

lem-pur-closed-support-open-counit vs def-weil-pbc-derived-inverse-image: defines termwise derived inverse image and its shifts; it does not establish the open extension counit on a closed pushforward.

lem-pur-closed-support-open-counit vs lem-weil-pbc-completed-realization-derived-cohomology: concerns exact completed pro-etale coefficient realization and its cohomology, not the small-etale open/closed support counit.

lem-pur-closed-support-open-counit vs lem-weil-pbc-exact-functor-bounded-below: proves t-exactness of an already supplied exact functor; it gives no closed-support geometric identification or counit isomorphism.

lem-pur-closed-support-open-counit vs lem-weil-pbc-exact-functor-complex-cohomology: compares termwise exact functors with cohomology of complexes; it supplies no adjunction or supported sheaf comparison.

lem-pur-closed-support-open-counit vs lem-weil-pbc-exact-functor-derived-factorization: constructs localization and shift factorization for one exact functor; it does not identify closed-support sections or prove the actual open counit invertible.

lem-pur-closed-support-open-counit vs lem-weil-pbc-exact-functor-derived-functor: identifies exact-functor localization with its Kan-derived functors; no closed-support identification or open counit is part of its conclusion.

lem-pur-compact-point-source-normalization vs lem-pqf-open-module-cohomology-comparison: compares structure-sheaf module and abelian cohomology on a Zariski open; the new task computes a constant-A small-etale closed-point derived source with its unit normalization.

lem-pur-compact-point-source-normalization vs lem-sc-module-cup-flasque-acyclicity: assumes a flasque underlying sheaf and concludes vanishing; the new task proves a closed-point derived identification and a compact unit equality without flasqueness hypotheses.

lem-pur-compact-point-source-normalization vs lem-sc-picard-external-cup-scalar-comparison: concerns degree-one structure-sheaf external cup products and scalar equivalences; it does not give constant finite-A closed-point compact cohomology.

lem-pur-compact-point-source-normalization vs lem-sc-picard-external-cup-unit-comparison: identifies external cup products with structure-sheaf pullbacks in degree one; no closed-point compact source or derived beta/lambda is present.

lem-pur-compact-point-source-normalization vs lem-sc-scalar-unit-cohomology-pullback-comparison: chooses equivalences for degree-one structure-sheaf scalar pullbacks; the new statement computes a different small-etale complex concentrated in degree zero.

lem-pur-compact-point-source-normalization vs new-picard-derived-fibre-naturality: compares residue fibres of proper flat pushforwards of line bundles with structure-sheaf H1; it does not compute the pushforward of a constant closed-point sheaf.

lem-pur-compact-point-source-normalization vs new-sc-scalar-abelian-ext-factorization: factors a scalar-to-abelian degree-one structure-sheaf Ext map; it does not assert the closed-point derived compact-source identification or its section-one inverse.

lem-pur-compact-point-source-normalization vs new-sc-scalar-unit-comparison-family: proves bijectivity of a degree-one unit-module/structure-sheaf comparison; the new statement concerns the entire small-etale closed-point complex and compact-source unit.

lem-pur-compact-point-source-normalization vs new-sc-scalar-unit-pullback-naturality: proves naturality of structure-sheaf scalar cohomology comparisons; it computes neither the closed-point complex nor the actual compact-source inverse.

lem-pur-compact-point-source-normalization vs def-sc-topological-abelian-cohomology: defines topological/Zariski abelian cohomology; the new statement is a computation and map identity on ordinary small-etale constant-A derived modules.

lem-pur-compact-point-source-normalization vs lem-sc-additive-cohomology-scalar-comparison: compares H1 for sheaves presented by structure-ring sections on a curve; the new statement has constant finite coefficients and a closed rational point on any proper Noetherian scheme.

lem-pur-compact-point-source-normalization vs lem-sc-etale-qcoherent-source-comparison-natural: compares associated quasi-coherent etale cohomology with module cohomology; a constant-A skyscraper is not the specified quasi-coherent source and the compact-source unit identity is absent.

## Preservation of the complete returned argument

The following old steps are retained verbatim for the workers and reviewer. Allocations: old 1 stays parent 1; old 2 and 3 become the counit task; old 4 uses that task in parent 3 while retaining its Cartier pullback/twist work there; old 5 becomes the compact-point task; old 6 is parent 5 using parent 4. These are task guidance in the report, not proof steps of the new unsplit nodes.

### Old step 1

Put $U_0=D(x_0)=X$ and $U_1=D(x_1)=P-D_0$. The ideal of $D_0$ has frames $f_0=t$ on $U_0$ and $f_1=1$ on $U_1$. These generate Cartier ideals: $t$ is a non-zero-divisor in $\Omega[t]$, and $1$ is a non-zero-divisor on $U_1$. For the dual ideal [def-pc-divisor-line-bundle], the dual frames satisfy $g_0=t^{-1}g_1$ on the overlap. The frame identifications $g_a\mapsto e_a^{(1)}$ therefore glue to an isomorphism $\mathcal O_P(D_0)\cong\mathcal O_P(1)$ by the transition rule of [def-pc-projective-space-twist]. The canonical divisor section has coordinates $t$ and $1$ in these frames, respectively; it is thus the section $x_1$ of the positive twist. Restriction to $X$ gives precisely the divisor pair used to define $c_{0,X}$.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md, Step 2, supported origin; unit sk-prop-an Step 5(d), divisor normalization.

### Old step 2

Write $F=\bar i_{0*}A_S$ and $G=i_{0*}A_S$. Open inverse image is restriction, as specified in [lem-weil-pbc-extension-by-zero-adjunction]. Thus on every etale $V\to X$ the two sheaves $j^{-1}F$ and $G$ are both $A_S(V\times_XS)$, by [def-weil-pbc-direct-image]; this gives the canonical identification in the statement. The same direct-image formula shows that $F|_{U_1}=0$, since $U_1\times_PS=\varnothing$. In particular its inverse image at infinity is zero, since infinity lies in $U_1$. Apply the module-sheaf version of [lem-weil-pbc-open-closed-short-exact] to $j:X\hookrightarrow P$ and its closed complement infinity, with coefficient sheaf $F$. Its last term is zero, so its first map $\epsilon_F:j_!j^{-1}F\to F$ is an isomorphism. Under $j^{-1}F=G$ this map is exactly $e$, not an arbitrary support isomorphism.

Source: literature/stacks-project/etale-cohomology.tex, Tags 03S3 definition-extension-zero and 095L lemma-ses-associated-to-open.

### Old step 3

Use [lem-weil-pbc-extension-by-zero-adjunction] for the actual sheaf adjunction $j_!\dashv j^{-1}$. Both functors are additive and exact, by [lem-weil-pbc-extension-by-zero-exact] and [prop-weil-pbc-inverse-image-modules-exact]. Its localization to derived categories is the specified exact derived adjunction of [def-weil-exact-derived-adjunction]. In particular its derived counit is the localized original counit on sheaves and is a natural transformation on the whole ordinary derived category, including morphisms to shifted sheaves. We use this normalization for every $\epsilon_M$ below.

Source: literature/stacks-project/etale-cohomology.tex, Tag 03S3 definition-extension-zero; exact localization as in derived.tex Tag 015F.

### Old step 4

The pullback clause of [lem-asd-ordinary-supported-kummer], applied to $j$ and the Cartier pair of Step 1, identifies $j^{-1}c_{0,P}$ with $c_{0,X}$. The target identification $j^{-1}L_P[2]=L_X[2]$ is the roots- and tensor-normalized comparison of [lem-asd-etale-finite-twist-pullback]; the source is the restriction identification of Step 2. Naturality of the counit of Step 3 at the actual arrow $c_{0,P}:F\to L_P[2]$ reads
$$c_{0,P}\circ\epsilon_F=\epsilon_{L_P[2]}\circ j_!j^{-1}(c_{0,P}).$$
Substituting these identifications gives exactly $c_{0,P}\circ e=\epsilon_{L_P[2]}\circ j_!c_{0,X}$. This uses no equality deduced merely from equality of restrictions of derived morphisms.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/lem-amb-cartier-kummer-map.proof.md, Final paragraphs: Cartier pullback and forgetting support; Stacks Tag 03PL.

### Old step 5

We check the source generator of the compact image. The closed immersion $\bar i_0$ is finite by [lem-weil-pbc-closed-immersion-finite]. On abelian sheaves its direct image is exact by [lemma-weil-pbc-finite-direct-image-exact]; the derived direct-image composition of [def-weil-pbc-derived-direct-image-composition], for $S\xrightarrow{\bar i_0}P\to S$ whose composite is the identity, gives $H^q(P,F)=H^q(S,A_S)$. Here the equality is first for underlying abelian sheaves, then for module cohomology by [lem-weil-pbc-etale-module-cohomology-forget]. By [lem-weil-pbc-geometric-point-cohomology], these groups vanish for $q>0$ and are $A$ in degree zero, with identification given by sections on $S$. There is no negative cohomology for a sheaf in degree zero under right derived sections. Thus $R\Gamma(P,F)=A[0]$, normalized by the section $1$. By the chosen compactification definition [def-amb-etale-compact-support], $R\Gamma_c(X,G)=R\Gamma(P,j_!G)$; $R\Gamma(e)$ gives its canonical identification with $A[0]$. Let $\lambda:A\to R\Gamma(P,j_!G)$ be its inverse and $\eta:A\to R\Gamma(P,A_P)$ the constant-section map. If $u:A_P\to F$ is the closed unit, then
$$R\Gamma(e)\lambda=R\Gamma(u)\eta.$$
Indeed both sides are maps $A[0]\to A[0]$ sending $1$ to $1$: the formula for direct image and its unit sends the constant section $1$ to its restriction on $D_0=S$. An $A$-linear map $A\to A$ is determined by this value.

Source: literature/stacks-project/etale-cohomology.tex, Tags 03QT theorem-equivalence-sheaves-point and 03QU lemma-compare-cohomology-point; sites-cohomology.tex Tag 0D6E lemma-derived-pushforward-composition.

### Old step 6

Apply derived global sections to the equality of Step 4 and precompose with $\lambda$ of Step 5. By [def-amb-etale-compact-support], $R\Gamma(j_!c_{0,X})\lambda=\tau_X^e$ and $R\Gamma(\epsilon_{L_P[2]})=a$. Step 5 therefore gives
$$a\tau_X^e=R\Gamma(c_{0,P})R\Gamma(e)\lambda=R\Gamma(c_{0,P}u)\eta.$$
The forgetting-support clause of [lem-asd-ordinary-supported-kummer] says $c_{0,P}u=c_1(\mathcal O_P(D_0))$. By the explicit line-bundle isomorphism of Step 1 this is $c_1(\mathcal O_P(1))$ with the positive Kummer boundary convention in the statement. Hence the last displayed morphism is the specified $h$. No generator was rescaled: the equality is with this Chern class itself, so its coefficient is $+1$.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md, Step 2, compact image of the origin; unit sk-prop-an Step 5(d), positive projective Chern class.

