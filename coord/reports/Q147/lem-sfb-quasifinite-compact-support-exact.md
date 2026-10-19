## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-quasifinite-compact-support-exact.json: item, split into 11 short steps; statement, stmt_deps, Lean record and existing maintainer fields preserved.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-open-tower-derived-unit.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-etale-geometric-fibre-compact-sections.json: statement, unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation for every node cited by every item step.
- report.md: this report and signed self-review.

Attachments: none. I searched the read-only slopmaster2 WeilConjectures source for the item id and proper-support terminology, and inspected SixFunctors/Etale/UpperLowerStar/FiniteEtale.lean. Its finite-etale direct-image stalk declarations do not state the present quasi-finite proper-support theorem or the two new lemmas. The item's existing stage-2 record is preserved; its declaration is not a completed proof.

WANTED: none.

The defect was the granularity of old steps 6 and 7, not the statement. The retained retry merely subdivided their prose without creating lemmas and had no report. I retained that work and its logged searches, compared it against the current repository's returned eight-step proof, restored original steps 1–5 and 8 verbatim, and extracted the actual internal arguments. New step 7 uses a tower-resolution lemma; new step 10 uses a finite-geometric-fibre compact-sections lemma. Setup, naturality/cancellation, construction of the graph map, conservativity, and nested-summand normalization remain in the item. This follows the same finite-compactification route; it is not a rebase-only push or a relocation of the whole theorem. There is no statement correction or statement dispute.

No mathematical work required for this one-level split is left unfinished. Both new nodes are intentionally statement-only for their own later stage-1 work. Validation results are recorded below.

## Review by Q147

I read the chapter record sec-six-functors-basics and the unit sk-lem-geo-affine-local, including proof (2)'s last Hom equality. The new blueprint references have that unit as their ancestor and the item in their via list. The chapter/unit route is unchanged. I read coord/dag-sync.md, GOAL.md, the human three-level rule in SETUP.md, and delivery-errors B–E in full. The repair addresses the sole return: extracting the non-elementary arguments in original steps 6 (3763 characters) and 7 (2567 characters). All 11 current steps are below 2000 characters; the longest is the unchanged 1659-character step 3.

Sources opened: more-etale.tex Tag 0GKM, lemma-Rf-shriek-for-quasi-finite (finite compactification), Tag 0F4Y, lemma-separated-etale-shriek (graph map into proper supports), Tag 0F5F, lemma-lqf-f-shriek-stalk (stalk/exactness context), Tag 0F7B, lemma-shriek-proper-and-open (the explicit K-injective map), Tag 0F7J, lemma-shriek-composition (the four tower equalities); etale-cohomology.tex Tag 09Z9, lemma-normal-scheme-with-alg-closed-function-field (separated etale schemes split into open immersions); and sites-cohomology.tex Tag 0D6E, lemma-derived-pushforward-composition. These are the same sources and route as the returned proof. The stronger map-level formulations extracted from that proof are agent-explicit calculations, not a claim that 0D6E alone states their chain formulas. No SGA reference is used.

I opened the statements of every cited node. The following records what each step takes from them; citations.json contains the exact statements, including all hypotheses and normalization clauses, so the quotations can be checked without relying on node titles or proofs.

1. Noetherian schemes are qcqs: the finite affine cover gives quasi-compactness and the locally-Noetherian quasi-separatedness lemma supplies the other condition. The Zariski-main node gives a quasi-compact open followed by a finite morphism for a separated finite-type quasi-finite map into a qcqs target. Finite type of that finite map is the elementary module-generator argument in the step; the finite-type-over-Noetherian and finite-proper statements supply the two remaining ambient hypotheses.

Cited statements: lem-weil-pbc-locally-noetherian-quasi-separated, thm-pqf-zmt-factorization, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-finite-proper.

2. The proper-support composition statement explicitly identifies the proper and open cases, naturally and A-linearly. Extension by zero is exact. The finite-direct-image node asserts exactness on abelian sheaves (I use that clause only, not its bounded-below derived conclusion); sectionwise direct image and the exact faithful module forgetful functor transfer exactness to constant-A modules.

Cited statements: lem-cbc-proper-support-sheaf-composition, lem-weil-pbc-extension-by-zero-exact, lemma-weil-pbc-finite-direct-image-exact, def-weil-pbc-direct-image, lem-weil-pbc-module-sheaves-colimits-forgetful.

3. The qcqs permanence statement makes each open quasi-compact once the ambient is quasi-separated; finite type over a Noetherian target gives the ambient Noetherian hypothesis. The support-composition statement gives r_*j_!=h_!^supp. Resolution existence and total-derived construction give its unit on all complexes. Exact-functor factorization plus localization descends it, and exact-functor-derived-functor makes its finite-compactification component invertible on all unbounded inputs. No bounded-below truncation argument is used.

Cited statements: lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-finite-type-over-noetherian, lem-cbc-proper-support-sheaf-composition, prop-weil-pbc-kinjective-resolutions-exist, def-amb-etale-compact-support, lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-localization-universal-property, lem-weil-pbc-exact-functor-derived-functor.

4. The proper/open node gives exactly the map j_2!J=u_*j_1!J to u_*I, not merely an unspecified isomorphism. Exact inverse image and its right adjoint preserving K-injectives make u_*I K-injective. Morphisms into a K-injective are computed up to homotopy, so the lift and commuting triangle have the asserted meaning. The direct-image composition node fixes the path normalization. Localization makes the representative equality a derived equality; the compact-support-comparisons statement identifies the refinement maps. I checked the direction beta_u delta_c2=delta_c1.

Cited statements: prop-weil-pbc-kinjective-resolutions-exist, lem-amb-unbounded-proper-open-interchange, lem-cbc-proper-support-sheaf-composition, prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-hom-derived, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-localization-universal-property, lem-amb-unbounded-compact-support-comparisons.

5. The cofilteredness statement supplies a common proper refinement, and the unbounded-comparisons statement supplies invertible beta maps and their cocycle. Everything after those inputs is multiplication and cancellation of isomorphisms, which is why this step remains elementary. It does not use a common refinement chosen outside the compactification category.

Cited statements: lem-cbc-compactifiable-cofiltered, lem-amb-unbounded-compact-support-comparisons.

6. The compatible-compactification-triangle statement gives the indicated Cartesian square, open arrows and proper arrows for the prescribed compactification of e. The ambient schemes are Noetherian by finite type over Noetherian schemes. The support-composition statement identifies the actual sections in all three composites; it is not being used as a definition-only node. Exactness of the composite proper-support functor follows from step 2 for e and h and this identification.

Cited statements: lem-weil-pbc-compatible-compactification-triangle, lem-amb-unbounded-compact-support-comparisons, lem-weil-pbc-finite-type-over-noetherian, lem-cbc-proper-support-sheaf-composition.

7. The new tower-derived-unit statement gives the missing equality of the two resolution paths and explicitly identifies their unit normalizations. Its hypotheses hold for step 6: all six schemes are Noetherian, i,b,j open, s,p,q proper, pb=iq. The unbounded-comparisons statement specifies alpha as precisely Rs_* of this interchange followed by the two compositors; the support-composition statement specifies sigma by equality of sections. Naturality of delta_e supplies the displayed whiskering rearrangement. Localization supplies equality on the entire derived category. Since delta_e and delta_h are invertible, the equality also makes delta_eh invertible (alpha and D(sigma) are isomorphisms); inversion gives the stated c-equation. This avoids assuming the composite is quasi-finite without a cited permanence result.

Cited statements: lem-sfb-proper-open-tower-derived-unit, lem-amb-unbounded-compact-support-comparisons, lem-cbc-proper-support-sheaf-composition, lem-weil-pbc-localization-universal-property.

8. The compact-support comparison statement explicitly includes compatibility of alpha with refinements. Substitution of delta-prime=eta delta from step 4 and cancellation by eta_eh are elementary natural-transformation algebra. This retains the final paragraph of original step 6, with only its step boundary moved.

Cited statements: lem-amb-unbounded-compact-support-comparisons.

9. The etale definition includes unramifiedness; the unramified quasi-finite-at-points statement and quasi-finite=locally-quasi-finite+qc statement apply because finite type includes quasi-compactness. The sum-extension definition supplies the presheaf generators. Etale base change, separated base change and the section-clopen lemma make each graph clopen. The closed-subset-proper lemma applies to a closed subset of the graph, which is isomorphic to the test object over itself. Addition, restriction and sheafification then construct the map; the map is not inferred merely from an abstract stalk isomorphism.

Cited statements: def-weil-etale-morphism, lem-weil-pbc-unramified-quasi-finite-at-points, pqf-lem-qf-locqf-qc, def-weil-pbc-etale-sum-extension, lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-separated-base-change, lem-weil-pbc-etale-section-clopen-immersion, lem-weil-pbc-closed-subset-proper-over-base-properties.

10. The proper-support-geometric-stalk statement specifies its isomorphism by restriction of a representative section to the fibre. The new geometric-fibre compact-sections statement specifies the same restriction/germ map and its graph-generator formula. The sum-stalk node specifies that exact formula on the source. Thus the map, not only the two abstract modules, is the identity on the direct sum. Geometric-stalk conservativity and the exact faithful forgetful functor then detect an isomorphism of module sheaves. No extra properness of h is assumed.

Cited statements: lem-cbc-proper-support-geometric-stalk, lem-sfb-etale-geometric-fibre-compact-sections, lem-amb-etale-sum-stalks, lemma-weil-pbc-geometric-stalk-conservative, lem-weil-pbc-module-sheaves-colimits-forgetful.

11. The support-composition statement keeps the underlying section, and the sum presheaf definition keeps the lift index. Two successive graph extensions restrict to the original section on the composite graph and to zero on its complementary open; the clopen sheaf gluing axiom proves the asserted equality. This is a few-line generator calculation, with finite sums and sheafification giving the result. Identity lifts give the sheaf identity, and exact-functor-derived-functor allows the identity derived unit. Step 4 transfers it to other compactifications. This is original step 8 verbatim.

Cited statements: lem-cbc-proper-support-sheaf-composition, def-weil-pbc-etale-sum-extension, lem-weil-pbc-exact-functor-derived-functor.

For lem-sfb-proper-open-tower-derived-unit I checked the extracted statement against the actual chain calculation: p_*M and q_*I are K-injective because direct image is right adjoint to exact constant-coefficient inverse image. The bijection Hom_K(-,p_*M)=Hom_D(-,p_*M) gives the unique homotopy class of ell lifting across w. The homotopy remains a homotopy after s_*; naturality of chi gives the displayed equality of the two paths. Exact b_! carries u to a quasi-isomorphism, so v b_!u is a K-injective resolution, and p_*M itself computes the intermediate direct image used for (sp)_*. The statement records this resolution path rather than the item's quasi-finite exactness, compactification independence, or final c-equation. It requires no quasi-finiteness and has no claim that the generally non-exact termwise source already descends to a functor on all derived inputs. I made its naturality claim precise as naturality in maps of K-injective representatives, with independence of I,M,L. The proof route to be used when splitting this lemma is this lifting/naturality calculation from the returned proof.

For lem-sfb-etale-geometric-fibre-compact-sections, 09Z9 applies to Spec Omega, which is integral normal with separably closed function field. The separated etale base change is a disjoint union of copies of that point; quasi-compactness makes the union finite. Its coordinate ring is Omega^n, a finite free Omega-algebra, so the fibre is finite and proper, and every closed support is proper. The sheaf axiom identifies its sections with a finite product, hence finite sum. The geometric-point pullback-stalk and inverse-image-stalk-germ statements give exactly the restriction/germ identification; graph extension has one nonzero component. This is the whole removed geometric-fibre argument, not a restatement of the item's global sum-extension isomorphism. It assumes only separated qc etale h, with no Noetherian assumption needed. I replaced an initially mistyped nonexistent quasi-compact definition id by def-weil-finite-type-morphism, which actually defines quasi-compactness. All notions in both new statements have definition/notation dependencies or are written out inline. Both new nodes have empty proof and proof_deps and null proof_origin; their proposed arguments are in this report only.

Small cases checked: empty source/fibre gives the zero module and empty coproduct; one sheet gives restriction to the original germ; two sheets sends a graph extension to (z,0) or (0,z), so the asserted map cannot be a summation map. The zero coefficient ring and sheaves with infinite module stalks are allowed. A nonproper open immersion still has a fibre either empty or one point, so no properness of h was introduced. For the tower lemma all open/proper arrows equal to identities reduce to identical resolution paths; an empty open gives zero paths. The lifting argument works for unbounded complexes and needs no uniform cohomological dimension. I also rechecked the item's finite non-etale example Spec(k[epsilon]/epsilon^2) to Spec k: exactness uses finite direct image, not an assertion that quasi-finite fibres are reduced etale points.

Searches: retained searches.jsonl was read and reused for the unchanged item. For each new node I ran LeanFinder, LeanSearch, Loogle and source grep with its own statement in mind, then a second semantic phrasing. All queries/results are recorded verbatim in mathlib_searches and in the command's log. Derived.RightDerived.lean's rightDerivedNatTrans_comp (line 125), rightDerivedNatTrans_fac (line 104), and totalRightDerivedUnit (line 201) concern derived transformations of functors on the same source; they do not identify the proper/open interchange with the two K-injective resolution paths. Limits.lean's Scheme.coprodPresheafObjIso (line 480) and isIso_stalkMap_coprodSpec (line 543) concern the Zariski structure sheaf of scheme coproducts, not etale module sheaves, geometric-fibre decomposition, or compact supports. FiniteEtale.lean's project declarations assume a globally finite f for its direct-image comparison and do not state the new lemma. Thus neither new node is an attachment or one-line Mathlib specialization.

I searched the entire DAG for matching source tags and key words, and ran blueprint_refs.py searches for proper/open, compact support, geometric fibre, geometric fibre sections, and derived units, besides the ancestor query. No blueprint statement supplies either extracted calculation. I opened the colliding-tag statements listed below: square coherence, compactification composition and coefficient/site transport are distinct from the derived-unit path equation, while normal-scheme splitting and proper-support composition do not state the finite-fibre compact-sections/generator calculation. No new node is elementary on its own: the first combines K-injective lifting, the proper/open map, and two normalizations; the second combines geometric splitting, finiteness/properness, sheaf gluing, and the actual germ map. These are exactly the hidden arguments the human required as nodes.

## Not duplicates

lem-sfb-proper-open-tower-derived-unit vs lem-sf-unbounded-compact-support-proper-composition: states compact-support composition with a proper first map, not the two unit/resolution paths for arbitrary open j in a tower.

lem-sfb-proper-open-tower-derived-unit vs lem-sf-compact-coefficient-composition: states compatibility of coefficient reduction with composition, whereas the new lemma fixes one coefficient ring and compares resolution units.

lem-sfb-proper-open-tower-derived-unit vs lem-trf-finite-structural-maps-commshift: states shift compatibility of structural transformations on constructible etale-origin inputs, not a unit-path identity on unbounded complexes.

lem-sfb-proper-open-tower-derived-unit vs lem-sfb-quasifinite-compact-support-exact: the item proves exactness and global compactification/sum-extension comparisons; this new node isolates only an internal resolution calculation, or only the compact-sections computation on one geometric fibre.

lem-sfb-proper-open-tower-derived-unit vs sk-lem-geo-affine-local: states classical pro-etale affine/etale exceptional adjunctions; it does not state the ordinary etale resolution-path calculation.

lem-sfb-proper-open-tower-derived-unit vs lem-weil-pbc-ringed-topoi-derived-pushforward-composition: states the direct-image compositor and its resolution normalization, not its compatibility with open extension and successive termwise units.

lem-sfb-proper-open-tower-derived-unit vs lem-weil-pbc-etale-shriek-qcqs-composition: states existence of a bounded-below compact-support composition isomorphism, not the two unbounded unit paths.

lem-sfb-proper-open-tower-derived-unit vs lem-weil-pbc-ring-sheaf-change-adjunction: compares adjunctions under scalar changes on pro-etale sites; the new lemma has a fixed coefficient ring and a proper/open square.

lem-sfb-proper-open-tower-derived-unit vs def-weil-pbc-derived-direct-image-composition: defines the bounded-below direct-image compositor as an adjunction conjugate; it gives no proper/open unit-path calculation.

lem-sfb-proper-open-tower-derived-unit vs lem-weil-pbc-etale-open-proper-interchange: asserts a bounded-below interchange isomorphism for a Cartesian open square, not the unit-path equation in a tower.

lem-sfb-proper-open-tower-derived-unit vs lem-weil-pbc-compatible-compactification-triangle: supplies geometric compactification data; it does not compare derived unit maps on those data.

lem-sfb-proper-open-tower-derived-unit vs def-weil-pbc-adjunction-conjugate: defines conjugate transformations of adjunctions, not a theorem about K-injective resolutions or proper/open maps.

lem-sfb-proper-open-tower-derived-unit vs lem-weil-pbc-frobenius-exchange-restriction: states finite-coefficient Frobenius exchange and restriction compatibility on pro-etale categories, not this ordinary etale unit-path identity.

lem-sfb-proper-open-tower-derived-unit vs lem-amb-unbounded-proper-open-interchange: fixes Gamma and square pasting equations but does not state the additional equality between two successive units through j,I,M,L and the single composite resolution.

lem-sfb-proper-open-tower-derived-unit vs lem-sp-et-proet-coefficient-compatibility: compares scalar/site transports on bounded constructible inputs, while the new calculation uses one fixed etale coefficient category on unbounded complexes.

lem-sfb-proper-open-tower-derived-unit vs lem-sf-proper-open-comparison-site-normalization: normalizes interchange under change of site; the new lemma stays on the etale site and compares unit/resolution paths.

lem-sfb-proper-open-tower-derived-unit vs lem-kun-module-abelian-kinjective-direct-image-acyclic: asserts acyclicity after coefficient forgetting; it does not give the proper/open unit-path equality.

lem-sfb-proper-open-tower-derived-unit vs lem-exc-proetale-cartesian-open-injective-acyclic: asserts proper acyclicity of open-extended injectives on pro-etale sites; the new lemma compares morphisms computed from K-injective resolutions.

lem-sfb-proper-open-tower-derived-unit vs lem-cbc-open-extended-injective-proper-acyclic: asserts higher-direct-image vanishing for open-extended injectives, not equality of unit maps in a tower.

lem-sfb-proper-open-tower-derived-unit vs def-cbc-finite-constant-coefficient-transport: defines scalar/site transport, whereas the new lemma proves a fixed-coefficient resolution-path comparison.

lem-sfb-proper-open-tower-derived-unit vs lem-sf-compact-support-restriction-of-scalars: compares compact support after coefficient restriction; it does not compare the two unit paths in one coefficient category.

lem-sfb-proper-open-tower-derived-unit vs lem-sp-coefficient-tower-shriek-calculus: states operations and coherence on varying coefficient towers, not the displayed ordinary-etale K-injective path identity.

lem-sfb-proper-open-tower-derived-unit vs lem-kun-etale-module-abelian-ringed-presentation: constructs ringed presentations for coefficient forgetting and direct image, not a proper/open tower unit identity.

lem-sfb-proper-open-tower-derived-unit vs lem-amb-unbounded-compact-support-comparisons: states alpha and Gamma normalization and compactification coherence, but not the two resolution-unit paths with arbitrary termwise source; the new lemma computes the units needed to compare alpha with exact proper support.

lem-sfb-proper-open-tower-derived-unit vs lem-exc-proetale-proper-open-sheaf-comparison: compares underived pro-etale sheaf operations, not K-injective derived-unit paths on the etale site.

lem-sfb-proper-open-tower-derived-unit vs lem-sp-proper-open-tower-comparison: states mate/open-adjunction normalization on strict coefficient towers with etale-origin witnesses, not this ordinary etale termwise-source unit calculation.

lem-sfb-proper-open-tower-derived-unit vs def-cbc-strict-tower-open-extension: defines exact open extension on strict towers, not a unit-path comparison for ordinary etale sheaves.

lem-sfb-proper-open-tower-derived-unit vs lem-cbc-strict-tower-proper-open-calculus: states intrinsic clopen-projection mate and coherence laws for strict pro-etale towers, not the displayed equality of two etale resolution-unit paths.

lem-sfb-proper-open-tower-derived-unit vs lem-cbc-compactifiable-compatible-tower: supplies geometric towers and common refinements, not equality of unit maps on resolutions.

lem-sfb-proper-open-tower-derived-unit vs lem-weil-proetale-direct-image-restriction-of-scalars: compares right derived direct image and restriction of finite scalars on pro-etale sites, not proper/open unit paths.

lem-sfb-proper-open-tower-derived-unit vs lem-sp-proetale-open-injective-proper-acyclic: states proper acyclicity on pro-etale sites, not the etale resolution-unit calculation.

lem-sfb-proper-open-tower-derived-unit vs def-cbc-strict-constant-tower-operations: defines strict-tower operations and their adjunctions, not a theorem about these ordinary etale resolution paths.

lem-sfb-proper-open-tower-derived-unit vs def-cbc-strict-tower-proper-open-arrows: defines strict-tower mate arrows, not a theorem identifying the two etale K-injective resolution paths.

lem-sfb-proper-open-tower-derived-unit vs lem-cbc-proper-open-interchange-coherence: gives square coherence and one-resolution Gamma normalization on bounded-below inputs, not the successive-unit versus composite-unit calculation.

lem-sfb-etale-geometric-fibre-compact-sections vs sbc-lem-etale-over-normal: states splitting into open immersions over an integral normal base; it does not assert finiteness, compact-support sections, or the restriction/germ generator formula on one geometric fibre.

lem-sfb-etale-geometric-fibre-compact-sections vs lem-sfb-quasifinite-compact-support-exact: the item proves exactness and global compactification/sum-extension comparisons; this new node isolates only an internal resolution calculation, or only the compact-sections computation on one geometric fibre.

lem-sfb-etale-geometric-fibre-compact-sections vs lem-weil-pbc-spec-domain-stalks-function-field: computes Zariski structure-sheaf local rings and the function field of Spec R, not etale module sections on a geometric fibre.

lem-sfb-etale-geometric-fibre-compact-sections vs lem-weil-pbc-gabber-h1-absolutely-algebraically-closed: states H^1 vanishing for constant finite groups on closed subschemes, not degree-zero sections of arbitrary module sheaves on an etale fibre.

lem-sfb-etale-geometric-fibre-compact-sections vs lem-weil-pbc-gabber-quotient-localizations: states strict henselianity of quotient local rings, not geometric-fibre decomposition or compact sections.

lem-sfb-etale-geometric-fibre-compact-sections vs lem-cbc-proper-support-sheaf-composition: states global proper-support composition, proper/open coincidences and base change; it does not compute the finite etale fibre as copies of Spec Omega or its module sections and graph-germ formula.

lem-sfb-etale-geometric-fibre-compact-sections vs lem-pur-etale-support-map-compatibility: assumes the item comparison to prove exchange/projection compatibility, so cannot be used to prove the item; the new node is the independent finite-fibre compact-sections input.

lem-sfb-proper-open-tower-derived-unit vs lem-pur-completed-coefficient-pushforward-comparison: the existing statement compares scalar restriction with pro-etale direct image for completed coefficient rings and strict reduction towers; the new lemma fixes one finite coefficient ring on ordinary etale sites and identifies the two chain-level derived-unit paths through a proper/open square. Neither the square nor this unit-path identity occurs in the existing statement.

lem-sfb-proper-open-tower-derived-unit vs lem-asd-proper-finite-coefficient-extension: the existing statement compares derived proper direct image after a finite coefficient-ring extension and its ordered projection-formula normalization, whereas the new lemma keeps one coefficient ring fixed and compares successive K-injective unit paths through an open/proper tower; it has no coefficient extension or projection-formula claim.

## Validation

The resumed dry run exited before pushing because a newly present Tag 0D6E collision required a report entry. I opened lem-pur-completed-coefficient-pushforward-comparison and added the statement-level distinction above. The final dry run then exited 0 and printed OK (not pushed), commit 0640ec6634, with server preflight passed (including check_dag.py and review_split.py). The original steps 1–5 and 8 remain verbatim; statement and Lean record compare equal to the current repository. All 55 citation quotes are verbatim with exact step coverage, proof_deps is the union of uses, and every item step is below 2000 characters. Both new nodes are statement-only, and there are no Mathlib leaves. Delivery follows this successful dry run.
