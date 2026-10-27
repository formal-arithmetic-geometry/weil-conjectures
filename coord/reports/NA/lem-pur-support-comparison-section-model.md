## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-support-comparison-section-model.json`: repaired split; its statement and all maintainer fields are unchanged. Five assembly steps, 2381 characters in total.
- `dag/nodes/sec-smooth-purity/lem-pur-normalized-comparison-augmented-resolution.json`: new statement, unsplit, no Mathlib match. Computes a normalized composite of right derived functors on a common augmented resolution, with explicit naturality of both computation isomorphisms. This is a general lemma for additive functors between abelian categories, not a replacement statement of the parent.
- `dag/nodes/sec-smooth-purity/lem-pur-open-restriction-comparison-augmentation.json`: new statement, unsplit, no Mathlib match. Gives the localized augmented injective resolutions, equality of their augmentations and derived-unit normalization, and chain-map naturality. It does not identify any of the three derived comparison maps of the parent.
- `citations.json`: a verbatim statement quotation for every node used in every parent step.
- `report.md`: this report. Search evidence is in `searches.jsonl`; returned proof text is retained in `returned-proof.json` for the repair audit. Auxiliary scripts and evidence stay in the sandbox and are not project files.

Attachments: none. The exact blueprint tag and relevant names were searched in the project under `lean/WeilConjectures/`; no complete declaration was found there. The retained local `lean/Sheaf/AlgebraicGeometry/SupportComparisonSectionModel.lean` has `sorry` in both `supportComparisonSectionModel` and `supportComparisonSectionModel_naturality`. The existing helper definitions and partial generic lemmas do not supply an attachment. No Lean was written or compiled.

WANTED: none.

The returned head is present as the current repository node, with the same six proof steps of lengths 711, 668, 1067, 1152, 978, 942. Contrary to the generic retained-sandbox instruction, this sandbox initially contained only dispatcher `.brief*` markers, no node, report, citations or search log. I therefore copied the live item, kept its statement, citations and historical Mathlib searches, and continued its actual six-step proof. No git command was run in the read clone. The delivery tool performs the rebase and commit construction.

Nothing mathematically false was found in this item. No statement was corrected or weakened, and no target or unit statement was changed. The return is a granularity repair: two separate arguments now join the queue, rather than being hidden in the parent. Nothing remains unfinished within this assigned split; the new nodes deliberately await other workers.

## Repair of the return

The return has one requirement with several concrete conditions. All are addressed:

1. Spread the 5518-character proof across at least two new nodes: exactly two are added, both unsplit and statement-only, with empty proof and proof_deps and null proof_origin. Their self-contained statements have 2101 and 2349 characters, and their proof tasks have comparable scope. The first handles the normalization calculation used twice; the second handles localization of the actual augmented data and its unit. Neither carries the entire parent.
2. Preserve the parent statement: it is byte-for-byte the decoded original JSON statement. The existing Lean record and all other maintainer fields are preserved.
3. Parent proof at most 3000 characters: it has 2381. Each step is below 2000. The parent applies the two intermediate results and explicitly supplies their hypotheses; it still carries the elementary section/kernel and chain-map equalities.
4. Preserve every old argument: the detailed mapping below and the verbatim returned proof at the end record precisely where each argument went. The subsequent two proof-task descriptions give the future workers the calculations; these are in the report, not proof sketches embedded in the new node statements.
5. Sources, blueprint provenance and searches: both nodes point through this item and support-comparison-boundary to thm-pur-rank-one-local-calculation, at the final comparison sentence of the current main-20261015 proof. Both have actual logged LeanSearch, LeanFinder/Loogle and grep requests; unavailable LeanSearch is recorded as unavailable. There is no SGA route.

The six old arguments map as follows:

| Returned step | Where the entire argument now resides |
| --- | --- |
| 1, strict direct-image evaluations, differentials and kernel | Parent 1 retains the section, restriction and kernel argument. The open-square identity is also part of the statement and proof task of open-restriction-comparison-augmentation. |
| 2, cancel the inverse of the canonical beta in the unit equation | Open-restriction-comparison-augmentation, ordinary-unit clause; its proof task below spells out that cancellation, with the exact existing canonical unit lemma. Parent 2 applies it. |
| 3, normalize global comparison by the given augmentation | Normalized-comparison-augmented-resolution, with E,H the two global section functors, sigma identity and b full support. Its general formula expands exactly the two-factor computation. Parent 3 supplies K-injectivity and identifies the named composite. |
| 4, restricted resolution, actual augmentation equality, comparison on V | Open-restriction-comparison-augmentation supplies injectivity, derived-unit normalization, beta, and a_V=j^-1 a. Parent 3 applies the same general normalized-comparison lemma to those precise data on V. |
| 5, support functor and the specified b-normalized supported map | Normalized-comparison-augmented-resolution, with E,H the two support kernel functors, computes the very same composite. Parent 4 checks its b is the stipulated kernel-normalized map. No uniqueness from the other two terms is substituted. |
| 6, ordinary naturality, section restrictions, kernels, localization | Parent 5 retains the ordinary augmentation equation and the elementwise kernel/restriction argument. The first new node states naturality of both derived computation isomorphisms. The second states the restricted lift and augmentation equations, using beta naturality. |

## Proof task for normalized-comparison-augmented-resolution

This is extracted from old steps 3 and 5, with their derived naturality from step 6. Use the natural comparison alpha of lem-weil-pbc-right-derived-plus-injective, not an arbitrary isomorphism of cohomology groups. All alpha maps at J and I=UJ are invertible because those complexes are bounded below and termwise injective. The images RU(Qh) and RE(Qa) are invertible because h,a are quasi-isomorphisms and the functors act on the derived categories. Thus all three displayed computation isomorphisms are defined, with their indicated directions.

Insert eta=RU(Qh)^-1 alpha^U_J Qa into c. Naturality of b at Qh says
`RH(Qh) b_N = b_QJ RE(RU(Qh))`.
Postcompose the defining composite c by c^H_h. The two factors involving RU(Qh) cancel, giving
`c^H_h c = (alpha^H_J)^-1 b_QJ RE(alpha^U_J) RE(Qa)`.
Use exactly the hypothesis normalizing b on J to replace the first three factors by
`Q(sigma_J) (alpha^E_I)^-1`.
The result is `c^H_h c = Q(sigma_J) c^E_a`. With sigma identity this is the identity matrix on the common complex, using precisely the two specified augmentations. This calculation applies separately to E=global sections and E=support kernels; the latter must use the normalized b in the statement, not merely agreement with forget-supports maps.

For a map of augmented data, `U(t)a=a'f` and naturality of alpha^E give
`c^E_a' RE(f) = (alpha^E_I')^-1 RE(QU(t)) RE(Qa) = Q(EU(t)) c^E_a`.
Similarly `th=h'g` and naturality of alpha^H give
`c^H_h' RH(g)=Q(H(t)) c^H_h`.
Naturality of sigma gives the remaining square. This retains the canonical isomorphisms, not just the image on cycles; localization of the chain-map equalities justifies each square. It is a task about two successive derived computations and a supplied normalized composite, not just the single-functor naturality lemma from Mathlib.

Sources read: derived.tex, Tags 05TH, label lemma-injective-acyclic (bounded-below injectives compute the derived functor), 05TI, label lemma-enough-injectives-right-derived (existence), and 05SA, label lemma-derived-functor (functoriality); the full statement of the existing derived-plus-injective node supplies the actual natural alpha and its invertibility. The new composite calculation is explicitly agent-formulated; none of these tags is claimed to state it verbatim. Tag 09XP is only the support specialization's kernel construction.

## Proof task for open-restriction-comparison-augmentation

This is old steps 2 and 4, with the open-square evaluation from step 1 and the open part of step 6. Apply lem-pur-comparison-pullback-open-unit to T,j,A,F. Its a_F is beta_F^-1, and its c_G is literally the sectionwise identity on every etale W over V. Its displayed equation is therefore
`nu_V,*(beta_F^-1) j_e^-1(eta_F^0) = eta_FV^0`.
Postcompose by nu_V,*(beta_F) and cancel the inverse. This produces the ordinary-unit equality in the new statement, for the specified canonical beta, not a new comparison choice.

An open immersion is etale (lem-weil-pbc-open-immersion-etale), hence weakly etale; apply lem-weil-pbc-proetale-restriction-injectives. Its exactness preserves h's quasi-isomorphism, injective preservation gives injective terms of J_V, and restriction preserves the lower bound. Composition with the isomorphism beta makes h_V the claimed resolution of nu_V^*F_V. Apply lem-pur-support-comparison-common-injectives to V,F_V,h_V: it says a_V is an injective etale resolution representing the derived unit. On each W over V the two direct-image/restriction functors evaluate to J(W over T) and give the same arrows and differentials. Substitute the just-proved unit identity into nu_V,*(h_V) eta_FV^0. Functoriality of direct image gives the displayed equality a_V=j_e^-1(a), including the source augmentation, not just the unaugmented complex.

For f,t as in the statement, naturality of beta gives
`(j_p^-1 nu_T^*f) beta_F = beta_F' nu_V^*(j_e^-1 f)`.
Restrict th=h'nu_T^*f and compose with beta_F: this gives t_V h_V=h'_V nu_V^*f_V. Naturality of the ordinary unit then gives nu_V,*(t_V)a_V=a'_V f_V. The natural alpha of derived-plus-injective gives the computation-isomorphism squares. These supply exactly the augmented data used when the parent applies the first new lemma on V.

Sources read: sites.tex Tag 03CF, label lemma-localize-morphism, especially its final direct-image/restriction identity; proetale.tex Tag 099V, label lemma-relative-comparison (unit on D^+), and Tag 09B1, label lemma-compare-derived (constant module coefficients); the exact statements of comparison-pullback-open-unit and support-comparison-common-injectives, and the statement of proetale-restriction-injectives. Localization alone does not identify the canonical unit; the existing unit-normalization node supplies that extra input. This is an agent-formulated augmentation refinement of these sources.

## Searches

Before creating either node I searched the whole DAG, by statement/title/concept, and used blueprint_refs.py ancestor plus searches `support comparison`, `injective computation`, `open unit`, `derived functor comparison`, `open restriction injective`, `augmented resolution`, `normalized comparison`, and `restriction augmentation`. These found related nodes but no equivalent statement. The nearest blueprint ancestor is thm-pur-rank-one-local-calculation; both via lists are [this item, support-comparison-boundary]. Existing related nodes were opened and read, in particular comparison-global-resolution-model, comparison-unit-injective-model, sf-normalized-derived-comparison-common-resolution, sf-normalized-derived-comparison-composition, sf-kinjective-derived-map-computation, pe-injective-complex-slice-section-model and weil-pbc-kinjective-exact-square-comparison. None gives both normalization through the supplied non-exact right adjoint U and the two actual augmented computation maps; none identifies the restricted comparison augmentation through beta. The item itself is not a blueprint import and its inherited same_as=[] remains appropriate.

All new-node mathlib_searches are taken from the log generated by msearch.py in this sandbox. The exact tool and query strings are copied, and results retain the actual response record including top names, availability, digest, subdirectory and hit count. Both concepts had two different semantic phrasings. LeanSearch answered `Rate limit exceeded: 60 per 1 minute` and is unavailable, never a claimed negative result. Loogle's first generic `rightDerivedFunctor` query is recorded as the actual unknown-identifier response; the corrected query found rightDerivedNatTrans_app.

I read Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean at rightDerivedNatTrans_app (111), Mathlib/CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean at rightDerivedFunctorComparison_fac_app (80), and Mathlib/CategoryTheory/Abelian/RightDerived.lean at InjectiveResolution.isoRightDerivedObj_hom_naturality (126). They compute a single derived transformation or a single resolution's derived homology; they do not state the new normalized composite of RE and RU with two different augmentations. One must still do the calculation above. Mathlib/AlgebraicGeometry/Modules/Sheaf.lean at restrictAdjunction_unit_app_app (442) concerns modules over a scheme's Zariski structure sheaf, not constant-A small etale/pro-etale sheaves. The proetale grep hits in Sites/Proetale.lean and ElladicCohomology.lean do not state the restricted augmented-resolution assertion. Accordingly both new nodes are unsplit, zero Mathlib leaves.

## Review by NA

I read the current main-20261015 rank-one-local-calculation statement and proof, especially the final comparison sentence, the returned item in full, and the recorded local Lean docstrings and two sorry theorem bodies. The repair remains below that comparison sentence; it does not change the affine-line calculation or the chapter/unit route. I read Tag 09XP, label section-cohomology-support, directly: its support is the kernel of restriction and it derives that functor. It does not assert this site's comparison normalization, which is why the proof remains agent-formulated and cites the actual normalization statement.

For parent step 1 I opened site-comparison-morphism: its explicit formula `(nu_*G)(U)=G(u(U))` is precisely what makes the two complexes and arrows equal. Support-cohomology states the kernel and the action on morphisms. The conclusion is elementary evaluation and restriction to that kernel; no injective-preservation theorem is smuggled into this step.

For step 2 I checked the new open-restriction statement against its proof task above. Its ordinary-unit clause is exactly the displayed clause of the parent, and its augmentation equality supplies a_V=j_e^-1 a, not merely an isomorphism of resolutions. Its assumptions are just a scheme, open immersion, finite commutative coefficients and the given bounded-below injective resolution; these all hold. No finite-type assumption on an arbitrary open of T is required by this lemma.

For step 3 I checked the new abstract normalized-comparison statement's directions: sigma maps E U J to H J; c^E_a maps RE(M) to Q(EI); c^H_h maps RH(N) to Q(HJ). Thus the equality computes exactly the map from the etale sections to the pro-etale sections. The parent supplies I=nu_*J injective, a a resolution, and eQa=eta by its original hypothesis. I opened bounded-below-injectives-kinjective and used only its stated implication. I opened derived-support-comparison-direct-image: its normalization is the identity on the two restriction kernels, and its full-support sentence identifies b with the final-object comparison. The global-cohomology node explicitly says its comparison is the composite with that final-object comparison. These are precisely the three facts this step needs. The same hypotheses on V follow from step 2; the open source is F_V and the pro-etale augmentation uses beta_F, not an unrelated coefficient identification.

For step 4 I checked the support functor's action on morphisms in support-cohomology and the literal kernel equality of step 1. The abstract lemma therefore has E U=H and sigma identity here as well. The supported composite is the displayed definition already in the unchanged parent statement. I read the whole normalization clause of derived-support-comparison-direct-image and used that clause, not an inference from agreement of the other two components. K-injectivity is already established in step 3. Both kernel inclusions and restriction arrows remain those of the same complexes.

For step 5 I checked the ordinary augmentation equation by naturality of the comparison adjunction unit, evaluated the same chain map on T,V, and verified res(t(s))=t(res(s)) sends kernel elements to kernel elements and preserves inclusions. The new abstract lemma explicitly states the two derived naturality equations; the open lemma explicitly states the restricted lift equation using beta. Thus every derived naturality assertion is in a cited statement; nothing is inferred just from a generic fully-faithful Yoneda or a definition node. These applications are why this assembly step is marked non-elementary even though its evaluation/kernel calculation is elementary.

I checked all new statements on the following cases. With U,E,H identity and sigma,b identity, the first assertion reduces to the ratio of the two augmentation computations, and when a=h it is the identity. If h is the identity of an injective complex in degree zero, its equation is exactly b's normalization. With a non-identity scalar automorphism sigma the representative must be that automorphism, not an identity; the statement correctly keeps Q(sigma_J). Zero objects give zero complexes and identity maps of zero objects. For the open lemma j=id gives h_V=h, a_V=a and beta=id; for V empty all evaluated complexes are zero; the unit/lift equations remain valid. For the parent C empty the support kernels are zero; for C=T the open is empty and the support calculation is the global calculation. No nonemptiness, constructibility, freeness, positive characteristic or inverse preservation of injectives is assumed. The injectivity is supplied for precisely I and J, not inferred from exactness alone.

I also audited B–E explicitly: no new node has proof text or proof_deps; each introduces its own objects and cites the defining notions it uses; TeX has single logical backslashes; Stacks sources use verified tags and labels; no leaf is claimed without a declaration; no source tag is used to define an unstated notion. Duplicate and blueprint searches preceded creation. The two new lemmas are supporting arguments with different inputs and neither restates all three conclusions of the parent. Every parent proof use has a checked verbatim quotation in citations.json. No new dependency points to the parent, so there is no new cycle. No unit route was replaced. The only off-unit tool retained in the parent split_report is global-cohomology, which identifies its named composite; this was already a tool use in the returned proof. No top-level tool_uses field was changed.

What I corrected in this review: the final assembly step is marked non-elementary because it invokes the two new naturality assertions, although its own unit and kernel equalities are elementary. The earlier large proof is not just shortened: the common-normalization and open-augmentation tasks are now independently stated queue items, with the original argument retained below for verification. This is my direct-delivery self-review, as requested by the brief; the maintainer supplies the independent reading.

## Not duplicates

lem-pur-normalized-comparison-augmented-resolution vs lem-weil-pbc-right-derived-plus-injective: the existing statement constructs a single RF and its natural injective computation; the new statement computes a normalized RE(RU(-)) to RH composite through two given augmentations and both naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-sc-derived-lower-truncation-unit-bridge: the existing statement is about Bottom derived unit through good lower truncation; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-pbc-u2-sheafH-large-filtered-colimit: the existing statement is about Large filtered-colimit continuity of Ext sheaf cohomology; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-sp-derived-functor-single-identification: the existing statement identifies individual cohomology of RF(X[0]) with classical derived functors; the new assertion is an equality of the specified composite morphism in D^+ through two augmented models.

lem-pur-normalized-comparison-augmented-resolution vs lem-weil-pbc-constant-etale-cohomology-iso-comparison: the existing statement is about Constant derived etale cohomology vanishing agrees with Ext cohomology vanishing on an isomorphic scheme; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-weil-pbc-free-sheaf-derived-sections: the existing statement is about Free sheaf shifted Hom computes derived module global sections; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-weil-pbc-resolution-pullback-augmentation: the existing statement is about Exact pullback and localized resolution augmentations; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-weil-pbc-sheafH-ext-derived-comparison: the existing statement is about Natural comparison of Ext sheaf cohomology with derived global sections; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-pur-derived-functor-morphisms-05sa: the existing statement is about Left derived values are functorial; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-pur-derived-injective-boundary: the existing statement is about Normalized derived connecting maps from sequences exact on injectives; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-pur-derived-representable-transport: the existing statement starts with representing objects and exact L and computes a represented pullback comparison; the new statement has a possibly non-exact U and a supplied normalized RE RU comparison, without representability.

lem-pur-normalized-comparison-augmented-resolution vs lem-pur-left-derived-defined-pointwise-kan-bridge: the existing statement is about A Stacks-defined left derived value is a pointwise Kan-extension value; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-normalized-comparison-augmented-resolution vs lem-pur-module-supported-hom-transport: the existing statement is about Exact transport of module-valued normalized supported Hom; it does not give the new two-functor normalized composite formula through a common augmented resolution and its two computation naturality squares.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-etale-object-sections-base-change: the existing statement is about Compatibility of etale evaluation with a base-change unit; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-pullback-sections-comparison: the existing statement is about Naturality of sections on an etale object under base change; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-pe-comparison-injective-left-modules-acyclic: the existing statement is about Comparison pullbacks of injective left-module sheaves are acyclic for arbitrary rings; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-pe-left-module-comparison-vanishing-criterion: the existing statement is about Objectwise derived evaluation detects comparison direct-image vanishing; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs sk-prop-sf-comparison: the existing statement gives derived comparison equivalence and cohomology/continuity; the new statement identifies the actual augmented injective resolutions after open restriction, a fact not stated by that equivalence.

lem-pur-open-restriction-comparison-augmentation vs def-weil-pbc-derived-morphism-sheaf-comparison: the existing statement is about Canonical comparison and weakly contractible evaluation of derived morphism sheaves; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs def-weil-pbc-normalized-origin-scalar-comparisons: the existing statement is about Canonical quotient scalar-extension unit and associator; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation: the existing statement is about Derived morphism sheaves evaluate on weakly contractible pro-etale affines; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-etale-restriction-pullback-unit: the existing statement concerns the pullback of terminal etale sections along arbitrary scheme base change; the new statement compares etale and pro-etale augmented injective resolutions and their actual units on an open.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-etale-underived-exchange-restriction: the existing statement computes underived exchange for a morphism of schemes on etale sites; the new statement compares two different topologies, injective resolutions and the derived-unit augmentation.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-finite-perfect-adic-tower-extraction: the existing statement is about Compatible algebraic stalk trivialization of a uniform finite perfect quotient diagram; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-fixed-module-bounded-constructible-origin: the existing statement is about Bounded fixed-module complexes with constructible sheaf origins have derived origin; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-fixed-module-derived-hom-bijection: the existing statement is about Derived comparison Hom bijection with bounded below target; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-localize-ringed-site-morphism: the existing statement constructs the localized ringed-site morphism; the new statement identifies canonical augmented injective resolutions under this square and their derived-unit normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-normalized-etale-origin-witnesses: the existing statement is about Compatible etale-origin witnesses for normalized finite-coefficient towers; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-normalized-origin-comparison-coherence: the existing statement is about Comparison reduction respects canonical scalar units and composition; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-over-post-continuous-general: the existing statement is about Continuity of the functor on localized sites; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-slice-commRing-pullback-isIso: the existing statement is about Invertibility of the canonical commutative-ring slice inverse mate; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-slice-set-pullback-isIso: the existing statement is about Invertibility of the canonical set-sheaf slice inverse mate; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-weil-pbc-slice-site-localization: the existing statement identifies the localized site morphism and its restriction functors; the new statement proves injective-resolution and actual augmented-unit equalities for constant module comparison on an open.

lem-pur-open-restriction-comparison-augmentation vs new-lem-weil-pbc-specialization-affine-coordinates: the existing statement is about Affine coordinate transport for specialization restriction; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs stage3-slice-sheaf-inverse-image-equivalence: the existing statement is about Finite limits and restriction comparisons for the localized inverse image; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs def-pur-supported-hom-site-comparison: the existing statement is about Canonical etale to pro-etale comparison on supported signed-twist Hom groups; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-cbc-abelian-comparison-injective-acyclicity: the existing statement is about Comparison inverse images of injective abelian sheaves are direct-image acyclic; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-pur-adic-line-system-base-change: the existing statement is about Adic line-system comparison through cofinal indices and rational coefficient colimits; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-pur-inverse-image-compatible-free-tower: the existing statement is about Inverse image of an inverse tower with compatible local bases; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

lem-pur-open-restriction-comparison-augmentation vs lem-pur-support-comparison-common-injectives: the existing statement gives a common resolution on one scheme and its augmentation; the new statement identifies its restriction with the independently defined canonical augmentation on an open, including beta and restricted lifting maps.

lem-pur-open-restriction-comparison-augmentation vs lem-pur-support-site-comparison: the existing statement gives supported comparison and exterior-product compatibility; the new statement has no support or exterior-product conclusion and identifies the restricted ordinary augmentation instead.

lem-pur-open-restriction-comparison-augmentation vs lem-pur-unit-normalized-slice-inverse-image: the existing statement normalizes localized inverse image of set sheaves; the new statement constructs the restricted module injective resolution, identifies its augmentation, and states chain-map naturality.

lem-pur-open-restriction-comparison-augmentation vs lem-trf-proetale-sheaf-equivalence-zariski-local: the existing statement is about Direct-image equivalence is local on the target; it does not identify the restricted etale/pro-etale injective augmentation with beta and the ordinary unit, together with its derived-unit and lifting-map normalization.

Additional close concept comparisons (not just shared tags):

lem-pur-normalized-comparison-augmented-resolution vs lem-sf-normalized-derived-comparison-common-resolution: the existing lemma assumes the restriction functor r is exact and computes RF rN on successive resolutions; the new lemma has non-exact U, RE RU, and a separate augmented unit M[0] to RU(N[0]). It is not a specialization through r=U.

lem-pur-normalized-comparison-augmented-resolution vs lem-sf-normalized-derived-comparison-composition: the existing lemma composes exact restriction-square comparisons, whereas the new one computes the unit-induced map through non-exact U on the two specified augmented resolutions.

lem-pur-normalized-comparison-augmented-resolution vs lem-sf-kinjective-derived-map-computation: the existing lemma computes one RF applied to a given morphism; the new one identifies a supplied normalized RE RU to RH composite, its chain representative and both augmentation computations. The existing lemma is useful input, not its complete statement.

lem-pur-normalized-comparison-augmented-resolution vs lem-pur-comparison-global-resolution-model: the existing lemma is a section/cocycle model using an etale resolution and a further pro-etale resolution. The new lemma computes a general normalized composite on the common UJ resolution, including support-functor applications; no section or representability hypothesis appears.

lem-pur-open-restriction-comparison-augmentation vs lem-pur-comparison-pullback-open-unit: the existing lemma gives the ordinary unit normalization; the new one identifies the entire restricted augmented injective resolution, its derived-unit computation and its lifting chain maps. Parent step 4's argument did not follow just by restating that unit clause.

lem-pur-open-restriction-comparison-augmentation vs lem-pe-injective-complex-slice-section-model: the existing lemma gives derived evaluations of a single site complex on slices; the new one identifies augmentations across two sites and the canonical coefficient beta, not only derived section objects.

## Verbatim returned argument retained for the next workers

### Returned step 1

For each etale object $W\to T$, the definition of direct image gives $(\nu_{T,*}J^n)(W)=J^n(W)$, and it gives the same map for every arrow of such objects. Thus the maps $u_T,u_V$ are identities of complexes, not just degreewise bijections: the differentials and the arrow $T\leftarrow V$ are the same on both sides. The support functor is the kernel of this arrow, with the induced action on morphisms. Hence its termwise application gives the stated $u_C$, with the same kernel inclusion. Likewise, on any etale $W\to V$, both $j_{\mathrm{et}}^{-1}\nu_{T,*}J^n$ and $\nu_{V,*}j_{\mathrm{pro}}^{-1}J^n$ evaluate to $J^n(W\to T)$; this is the sectionwise restriction/direct-image identification in the question.

Uses: def-weil-pbc-site-comparison-morphism, def-pur-support-cohomology, lem-pur-comparison-pullback-open-unit.

### Returned step 2

Use [lem-pur-comparison-pullback-open-unit] with the given finite ring $A$, scheme $T$, open $j$ and sheaf $F$. In its notation $a_F=\beta_F^{-1}$ and $c_{F_p}$ is precisely the sectionwise identity of step 1. Its unit equation is
$$\nu_{V,*}(\beta_F^{-1})\circ j_{\mathrm{et}}^{-1}(\eta_F^0)=\eta_{j_{\mathrm{et}}^{-1}F}^0.$$
Postcompose by $\nu_{V,*}(\beta_F)$. Since a functor preserves inverse isomorphisms, this gives exactly
$$j_{\mathrm{et}}^{-1}(\eta_F^0)=\nu_{V,*}(\beta_F)\circ\eta_{j_{\mathrm{et}}^{-1}F}^0.$$
In particular the comparison here is the specified canonical pullback comparison, with its specified unit, rather than a new choice of isomorphism.

Uses: lem-pur-comparison-pullback-open-unit.

### Returned step 3

Write $e:QI^\bullet\xrightarrow{\sim}R\nu_{T,*}F_p$ for the injective-computation isomorphism specified in the hypotheses. Those hypotheses say $e\circ Qa=\eta_F$. The canonical injective computation of a right derived functor is natural in chain maps by [lem-weil-pbc-right-derived-plus-injective]. Consequently, when the source $R\Gamma(T_{\mathrm{et}},F)$ is identified with $QI^\bullet(T)$ by the augmentation $a$, the morphism $R\Gamma(T_{\mathrm{et}},\eta_F)$ has identity matrix on $I^\bullet(T)$, with its target identified using $e$. To identify the next factor, $J^\bullet$ is K-injective by [lem-weil-pbc-bounded-below-injectives-kinjective]. The full-support case $C=T$ of [lem-pur-derived-support-comparison-direct-image] says that the final-object comparison is represented by the sectionwise identity $I^\bullet(T)=J^\bullet(T)$. The global comparison is the composite of these two factors by [lem-weil-pbc-comparison-global-cohomology]. Its representative is therefore exactly $u_T$, with the source and target identifications coming from $a$ and $h$.

Uses: lem-weil-pbc-right-derived-plus-injective, lem-weil-pbc-bounded-below-injectives-kinjective, lem-pur-derived-support-comparison-direct-image, lem-weil-pbc-comparison-global-cohomology.

### Returned step 4

Put $F_V=j_{\mathrm{et}}^{-1}F$, $J_V^\bullet=j_{\mathrm{pro}}^{-1}J^\bullet$, and $h_V=(j_{\mathrm{pro}}^{-1}h)\circ\beta_F:\nu_V^*F_V\to J_V^\bullet$. Restriction is exact and preserves injectives by [lem-weil-pbc-proetale-restriction-injectives], so $h_V$ is a bounded-below injective resolution. Apply [lem-pur-support-comparison-common-injectives] on the scheme $V$ to this resolution. It gives the injective etale resolution $a_V=\nu_{V,*}(h_V)\circ\eta_{F_V}^0$, representing the derived unit on $V$. The sectionwise identity of step 1 identifies its target $\nu_{V,*}J_V^\bullet$ with $j_{\mathrm{et}}^{-1}I^\bullet$. Step 2 then gives the actual equality of augmentations
$$a_V=\nu_{V,*}(j_{\mathrm{pro}}^{-1}h)\circ\nu_{V,*}(\beta_F)\circ\eta_{F_V}^0=j_{\mathrm{et}}^{-1}(a).$$
Now repeat the two-factor calculation of step 3 on $V$, using $a_V,h_V$ and the global comparison of [lem-weil-pbc-comparison-global-cohomology]. Its chain representative is the identity $I^\bullet(V)=J^\bullet(V)$, namely $u_V$. The source augmentation is the restriction of the given $a$, and $h_V$ uses exactly the required coefficient identification $\beta_F$.

Uses: lem-weil-pbc-proetale-restriction-injectives, lem-pur-support-comparison-common-injectives, lem-weil-pbc-comparison-global-cohomology.

### Returned step 5

Apply the same calculation to the additive kernel functor $\Gamma_C$ defined in [def-pur-support-cohomology]. Under the injective-computation isomorphisms of [lem-weil-pbc-right-derived-plus-injective], the equality $e\circ Qa=\eta_F$ from step 3 means that $R\Gamma_C(T_{\mathrm{et}},\eta_F)$ is represented by the identity of $\ker(I^\bullet(T)\to I^\bullet(V))$, with its source identified by the given augmentation $a$. The second factor $b_{C,F_p}$ of the explicitly specified $c^C_{T,F}$ is, by the normalization in [lem-pur-derived-support-comparison-direct-image], the identity between that kernel and $\ker(J^\bullet(T)\to J^\bullet(V))$. Its hypothesis of a K-injective representative holds by the bounded-below injective result used in step 3. Thus the composite has representative $u_C$. This uses the normalization of $b$ and the displayed definition of $c^C_{T,F}$ in the statement; compatibility with the two other terms alone would not determine a supported map.

Uses: def-pur-support-cohomology, lem-weil-pbc-right-derived-plus-injective, lem-pur-derived-support-comparison-direct-image, lem-weil-pbc-bounded-below-injectives-kinjective.

### Returned step 6

Let $f:F\to F'$ and $t:J^\bullet\to J'^\bullet$ be a chain map between two such augmented resolutions lifting $\nu_T^*f$, so $t\circ h=h'\circ\nu_T^*f$. Naturality of the ordinary adjunction unit gives
$$\nu_{T,*}(t)\circ a=\nu_{T,*}(t\circ h)\circ\eta_F^0=\nu_{T,*}(h')\circ\eta_{F'}^0\circ f=a'\circ f.$$
On $W=T,V$ the maps $\nu_{T,*}(t)(W)$ and $t(W)$ are literally equal by the direct-image formula. They commute with the restriction arrows because $t$ is a morphism of sheaf complexes. If $s\in J^n(T)$ restricts to zero on $V$, then $\mathrm{res}(t(s))=t(\mathrm{res}(s))=0$; the same equality proves that the induced kernel map commutes with the kernel inclusion. These equalities commute with all three identity representatives. Localization preserves these equalities, and the canonical derived comparisons used above are natural. This proves the claimed naturality and preservation of the two arrows on the specified augmentations.

Uses: def-weil-pbc-site-comparison-morphism, def-pur-support-cohomology, lem-weil-pbc-right-derived-plus-injective.


## Validation repairs

The first dry run refused five quotation entries because they were shorter than its 40-character evidence minimum. I extended them to the verbatim evaluation paragraph, the full composite formula paragraph, and the full bounded-below K-injectivity statement respectively. The cited statements and the mathematics were unchanged.
