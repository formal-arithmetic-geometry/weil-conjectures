## Worker report

Repair of the 2026-10-22 batch-5 re-split return for lem-sfb-derived-cech-image-totalization, group Q71. The sandbox contained only the launcher brief markers, not the previous delivered JSON/report/search log. I copied the live returned item and retained its complete statement, metadata, citations in the old proof, and previously logged Mathlib search records. There was no retained sandbox split/report on which to run the preliminary repair dry run. An initial delivery attempt before writing report.md supplied no usable content diagnostics; the subsequent server review_split check passed. The required full dry run is run after this report.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-derived-cech-image-totalization.json: same statement verbatim; five assembly steps, 2,475 characters in all.
- dag/nodes/sec-six-functors-basics/lem-sfb-cech-injective-column-model.json: statement, unsplit, no Mathlib match; constructs the one coherent slice/direct-image injective bicomplex and its specified derived-column comparisons, without asserting descent or its coefficient naturality.
- dag/nodes/sec-six-functors-basics/lem-sfb-cech-injective-image-augmentation.json: statement, unsplit, no Mathlib match; proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality.
- dag/nodes/sec-six-functors-basics/lem-sfb-cech-augmentation-normalized-naturality.json: statement, unsplit, no Mathlib match; proves the actual Cech augmentation counit and signed resolution/refinement equations in the derived category, without proving row exactness or coefficient comparison.
- dag/nodes/sec-six-functors-basics/lem-sfb-cech-coefficient-derived-comparison.json: statement, unsplit, no Mathlib match; identifies actual scalar-restriction Cech maps with canonical right-derived column and total comparison maps, without proving the descent isomorphism or assuming those comparisons invertible.

- report.md and citations.json: signed review, complete obligation map and verbatim quotes of every cited statement.

## Attachments

None. Searching WeilConjectures/ for the exact blueprint tag found no attachment. Concept searches found open-cover/global-section Cech results, including CategoryTheory.injective_cech_augmentation_quasiIso and injective_cech_total_sections_nat; their hypotheses and conclusions do not cover arbitrary ringed-topos sheaf-valued direct images with coherent naturality. The live Sheaf.CategoryTheory.DerivedCechImageTotalization module was read: its main theorem and all its comparison/naturality helpers still contain sorry. It supplies the intended Lean interface, not a finished proof.

## WANTED

None. Sources read are present under literature/. No SGA source was used.

## What was wrong and what remains

The return identifies excessive indivisible proof work: eight steps, 8,038 characters. I repaired that exact point by adding four comparably sized independent statement-only obligations (about 2,300-3,100 characters including repeated self-contained hypotheses). The parent assembles them and the elementary finite-biproduct computation. No new node restates the whole parent: construction, exactness, normalized homotopy/refinement, and coefficient comparison have different conclusions and can be assigned separately. Each has proof=[], proof_deps=[], proof_origin=null, status=unsplit. I have not attempted to solve their proofs in this stage-1 repair. No Lean file was written and no compiler or build was run.

There is no statement dispute. The inherited ancestor chain has blueprint.from.node=null; blueprint_refs.py ancestor confirms None. I retained that provenance and extended the via chain through the item, instead of inventing an imported ancestor. The chapter and unit records were read and not changed. The relevant current blueprint place is paragraph (3) of main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md: the covering-nerve argument is the existing tame-boundary expansion of the open-direct-image route. There is no change to that route.

## Return repaired: complete distribution of the original argument

| Original step | Where its work now lives |
| --- | --- |
| 1: enough injectives, resolution, bicomplex, signs, augmentation | lem-sfb-cech-injective-column-model |
| 2: arbitrary slice presentations, K-injective restrictions, specified derived columns | lem-sfb-cech-injective-column-model |
| 3: slice adjunction, injectivity, presheaf nerve acyclicity, epi/local-surjectivity and gluing | lem-sfb-cech-injective-image-augmentation |
| 4: first-quadrant augmentation criterion and transpose sign | lem-sfb-cech-injective-image-augmentation |
| 5: exact inverse image and finite diagonal total | parent assembly step 3, using the existing exact-functor derived-factorization statement |
| 6: unit, restriction, triangle identity, derived counit normalization | lem-sfb-cech-augmentation-normalized-naturality |
| 7: lifts, comparison naturality, signed homotopy, refinement identities/composition | lem-sfb-cech-augmentation-normalized-naturality |
| 8: exact coefficient restriction, map TI to a new injective J, canonical right-derived comparison and independence | lem-sfb-cech-coefficient-derived-comparison |

The original eight arguments and their cited dependencies are reproduced verbatim below, so no work is lost through summarization. They are future proof tasks, not hidden proof steps of the new unsplit nodes.

## Review by Q71

I read the item, all eight returned steps, its live Lean interface, the chapter and inherited unit, and the current direct-images blueprint proof. I also read the original dependency statements, in particular the distinction between arbitrary-sheaf slice presentation and restriction to a site object, between injective modules and injective abelian sheaves, and between a canonical derived comparison and an arbitrary isomorphism.

For the column-model task I read Stacks sites-cohomology.tex, lemma-injective-module-trivial-cech (03FC), lemma-restrict-K-injective-to-open (08FI), sites.tex lemma-localize-topos (04GZ), and sites-modules.tex lemma-localize-ringed-topos (04IE) and lemma-relocalize-ringed-topos (04J4). The task fixes actual localization units and a single resolution, so the column computations are compatible instead of a collection of unrelated triangulated representatives. The existing def-sfb-coherent-cech-image-model defines supplied data only; it does not assert the existence now required of the canonical model. The enough-injectives and K-injective computations from old steps 1-2 remain explicit obligations of this construction task, with their complete old arguments in the appendix.

For the row/augmentation task I read 03FC and its proof through injective presheaves and the zeroth Cech kernel, together with homology.tex lemma-double-complex-gives-resolution (0133), including its second-variable version. The statement requires injectivity in the module category, not injectivity of its underlying abelian sheaf. On a target-site object W the slice is at f^{-1}(h_W^#), which need not have been representable in the original site; the preserved proof uses the existing small presenting-site lemma before applying localized restriction. The exact left adjoint to restriction is the reason injectivity survives, and locally surjective V_A to A supplies degree-zero gluing. Exactness is asserted sectionwise, hence as sheaves, before the total criterion. This is more than the existing positive site-cover Cech-vanishing statement, and is the work that criterion assumes. The transpose sign (-1)^{nq} fixes the (0,q) augmentation summands.

For normalized naturality I read derived.tex lemma-derived-adjoint-functors (09T5) and lemma-K-injective (070I), and the existing lem-trf-bounded-below-derived-adjunction statement, which explicitly pins both derived unit and counit to their termwise comparisons. The new task states the actual equation Q(Tot B(t)) alpha_K = alpha_L Rf_*(u), not just equality after cohomology. The (-1)^n sign on a vertical degree -1 homotopy cancels the horizontal cross terms; a degree-zero localization unit has no extra sign. Refinement means an actual map V' to V over 1, so it acts contravariantly and satisfies rho alpha_V = alpha_V'. These checks keep the direction of all maps and the counit normalization correct. Resolution changes lift the identity and give homotopy equivalences on totals.

For coefficient comparison I read derived.tex lemma-right-derived-exact-functor (015F), lemma-K-injective (070I), the actual rightDerivedNatTrans definition/factorization in Mathlib/CategoryTheory/Functor/Derived/RightDerived.lean, and def-pc-sheaf-restrict-scalars. Exactness makes TX I a resolution, but TX need not preserve injectives. The target J is K-injective, so a comparison t exists and is unique up to homotopy. The new task fixes its class by Q(t)Q(TX a)=Q(c), states the resulting total square, and identifies its column maps with the right-derived units at the scalar-restricted complexes. The commuting underived identifications are the canonical ones of actual scalar restriction; their unit/counit compatibilities follow by leaving underlying additive sections unchanged and restricting the scalar action. They do not add a geometric hypothesis to the parent. I corrected the draft to introduce v'_n explicitly for the new coefficients and to cite the existing scalar-restriction definition. No comparison is asserted invertible.

The assembly citations were checked as follows. Step 1 cites exactly the new column-model statement, which gives the chosen I, coherent B, b and canonical derived-column comparisons under the same hypotheses. Step 2 cites exactly the new row/augmentation statement, whose Q(b) is an isomorphism for this nonnegative injective I. Step 3 uses lem-weil-pbc-exact-functor-derived-factorization for termwise h^* preserving quasi-isomorphisms; def-sp-double-complex-total supplies the finite diagonal and stipulated sign. The remaining biproduct calculation is elementary: an additive functor preserves finite sums and their injections/projections, hence carries each differential and its sign to the corresponding component. Step 4 cites the new normalized-naturality statement for the counit and all resolution/refinement squares, and applies h^* to equalities already established there. Step 5 cites the coefficient-comparison statement for the canonical augmentation square and all column maps, then uses the underived h^* commutation in the parent's hypothesis and the same finite-sum calculation. Every citation is backed in citations.json by the full verbatim cited statement; no step uses a dependency's proof as though it were its statement. No off-unit nonclosed statement is newly cited by the parent.

I checked B-E against the actual files. New statements repeat their ringed topoi, coefficient rings, cover, indices, resolutions and maps; the unsplit statements contain no proof sketch. Statement dependencies are existing definitions, including sheafification for h_W^# and scalar restriction for the last task. Blueprint searches were run for Cech, Čech, injective resolution, coefficient restriction and Cech augmentation; whole-DAG concept/declaration/tag searches and live Lean searches found no exact or more general existing statement that replaces one of these tasks in one specialization. The source-sharing pairs are distinguished below. Mathlib searches were run only through msearch.py; every task has its own two natural-language phrasings, Loogle pattern and source grep, recorded with actual output and verdict. The closest hits are ordinary injective resolution lift/homotopy, degreewise right-derived cohomology naturality and abstract derived natural transformations. They omit the actual coherent Cech and normalization assertions, so these four tasks remain unsplit, with no Mathlib leaves.

Edge cases: K=0 and I=0 give zero bicomplexes and all asserted squares. V=1 gives the constant nerve and its usual alternating 0/identity differentials; the augmented rows are exact, and the (0,q) unit is the identity. A split nontrivial cover has the insertion contraction compatible with the stated signs. The degenerate topos, in which an empty object can cover 1, has zero module categories and causes no excluded case. h=id reduces to the pre-pullback augmentation; total degree r<0 is zero and degree 0 has exactly one summand, while degree r>=0 has r+1. Taking identity coefficient restriction and J=I recovers the identity comparison. For a nontrivial ring restriction there is no injectivity-preservation premise: its absence is precisely why the independent comparison task uses TI to J. All isomorphisms of complexes/derived objects are stated at the derived-object level; no per-degree assertion substitutes for them. I changed no hypotheses or clauses of the parent.

## Not duplicates

lem-sfb-cech-injective-column-model vs lem-sfb-derived-cech-image-totalization: The parent assembles normalized derived descent after h^*; this new task only constructs the one coherent slice/direct-image injective bicomplex and its specified derived-column comparisons, without asserting descent or its coefficient naturality. The remaining independent tasks and finite-total calculation are essential.

lem-sfb-cech-injective-column-model vs lem-sbc-injective-module-forget-evaluation-acyclic: The existing result is positive derived-evaluation vanishing after forgetting constant-ring scheme-etale modules; it is not a coherent arbitrary-ringed-topos Cech construction.

lem-sfb-cech-injective-column-model vs def-sfb-coherent-cech-image-model: This existing node defines supplied coherent data but proves neither existence of the canonical model nor the injective and derived-comparison assertions.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-injective-module-abelian-acyclic: The existing result is abelian evaluation acyclicity of an injective constant-ring module sheaf on a scheme etale site, without Cech totals.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-module-abelian-derived-direct-image-comparison: The existing comparison forgets scheme-etale module structures to abelian sheaves; it does not construct or normalize a Cech nerve model.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-ringed-site-cech-refinement-square-rest: The existing assertion is a per-cohomology finite site-cover edge comparison; it does not assert coherent derived-object comparisons for arbitrary topos-object covers.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-injective-module-annihilator-acyclic: The existing result concerns abelian cohomology of an integer-annihilator submodule on one etale site; it has no Cech bicomplex or augmentation.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-ringed-site-cech-refinement-square: The existing result concerns finite representable covers and individual Cech-to-cohomology edge maps, with a site-functor presentation; the new task has arbitrary topos-object covers and actual derived sheaf objects.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-injective-etale-module-cech-h1: The existing theorem only kills the first Cech homology of an injective constant-ring etale module sheaf; it gives neither arbitrary ringed-topos derived columns nor a sheaf-valued total comparison.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-ringed-site-injective-module-cech-acyclic: The existing theorem kills positive Cech cohomology for a covering of a site with specified universe/precoverage hypotheses; it omits arbitrary topos-object slices, degree-zero gluing, and the specified direct-image total augmentation.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift: The existing theorem gives positive cocycle primitives for module presheaves on representable families; it does not give a coherent derived direct-image model, degree-zero descent or its total comparison.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift-max: The existing theorem is the larger-universe positive presheaf cocycle-lifting result on representable families; arbitrary sheaf-object slices, derived columns and sheaf-valued total augmentations are additional work.

lem-sfb-cech-injective-image-augmentation vs lem-sfb-derived-cech-image-totalization: The parent assembles normalized derived descent after h^*; this new task only proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality. The remaining independent tasks and finite-total calculation are essential.

lem-sfb-cech-injective-image-augmentation vs lem-sc-finite-strip-cone-graded-map-epi: The existing result is a generic finite-horizontal-strip cone/filtration statement requiring its own support and augmentation inputs; it gives no injective-sheaf exactness on arbitrary topos-object slices. The new task proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality.

lem-sfb-cech-injective-image-augmentation vs lem-sc-finite-strip-cone-graded-map-isIso: The existing result is a generic finite-horizontal-strip cone/filtration statement requiring its own support and augmentation inputs; it gives no injective-sheaf exactness on arbitrary topos-object slices. The new task proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality.

lem-sfb-cech-injective-image-augmentation vs lem-sc-first-quadrant-total-column-comparison: The existing generic total comparison assumes column quasi-isomorphisms; it supplies none of the injective-sheaf row exactness on arbitrary slices required by this new task.

lem-sfb-cech-injective-image-augmentation vs lem-sc-finite-strip-cone-filtration-graded-point: The existing result is a generic finite-horizontal-strip cone/filtration statement requiring its own support and augmentation inputs; it gives no injective-sheaf exactness on arbitrary topos-object slices. The new task proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality.

lem-sfb-cech-injective-image-augmentation vs lem-sc-finite-strip-row-augmentation: The existing result is a generic finite-horizontal-strip cone/filtration statement requiring its own support and augmentation inputs; it gives no injective-sheaf exactness on arbitrary topos-object slices. The new task proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality.

lem-sfb-cech-injective-image-augmentation vs lem-sc-finite-strip-cone-filtration-steps: The existing result is a generic finite-horizontal-strip cone/filtration statement requiring its own support and augmentation inputs; it gives no injective-sheaf exactness on arbitrary topos-object slices. The new task proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality.

lem-sfb-cech-injective-image-augmentation vs lem-sc-first-quadrant-column-augmentation: The existing generic augmentation criterion assumes row quasi-isomorphisms; the new task proves the necessary sectionwise sheaf-theoretic row assertion and identifies the actual unit augmentation.

lem-sfb-cech-injective-image-augmentation vs lem-pc-abelian-cech-alpha-quasi-iso: The existing result is a global-sections total for abelian sheaves and open covers of a scheme; the new task is a sheaf-valued direct-image augmentation on arbitrary ringed topoi.

lem-sfb-cech-injective-image-augmentation vs lem-sc-finite-strip-cone-graded-map-differential: The existing result is a generic finite-horizontal-strip cone/filtration statement requiring its own support and augmentation inputs; it gives no injective-sheaf exactness on arbitrary topos-object slices. The new task proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality.

lem-sfb-cech-injective-image-augmentation vs lem-sc-finite-strip-cone-filtration: The existing result is a generic finite-horizontal-strip cone/filtration statement requiring its own support and augmentation inputs; it gives no injective-sheaf exactness on arbitrary topos-object slices. The new task proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality.

lem-sfb-cech-injective-image-augmentation vs lem-sc-finite-strip-cone-graded-map-mono: The existing result is a generic finite-horizontal-strip cone/filtration statement requiring its own support and augmentation inputs; it gives no injective-sheaf exactness on arbitrary topos-object slices. The new task proves sectionwise injective-row exactness for arbitrary topos-object covers and the specified sheaf-valued total augmentation, without constructing the derived columns or proving naturality.

lem-sfb-cech-augmentation-normalized-naturality vs lem-sbc-unbounded-exact-adjunction-square: The existing statement normalizes constant-tower/evaluation derived adjunctions and their square mates; it contains no Cech total or signed resolution/refinement comparison.

lem-sfb-cech-augmentation-normalized-naturality vs lem-sbc-ambient-operations-scalar-linearity: The existing statement is scalar linearity of operations, without a Cech resolution or an augmentation comparison.

lem-sfb-cech-augmentation-normalized-naturality vs lem-trf-proetale-unit-leray-chain-formula: The existing formula concerns global sections and the Leray unit for a scheme morphism with finite coefficients; it has no covering-nerve total or its refinement maps.

lem-sfb-cech-augmentation-normalized-naturality vs lem-sc-p1-rhom-injective-cocycle-bijective: The existing result concerns Hom(M,-) cocycle/roof or shift formulas in D^+, without Cech fibre powers, their refinements, or a signed-total augmentation. The new task proves the actual Cech augmentation counit and signed resolution/refinement equations in the derived category, without proving row exactness or coefficient comparison.

lem-sfb-cech-augmentation-normalized-naturality vs lem-sc-p1-rhom-hom-derived-roof-shift-injective-cocycle: The existing result concerns Hom(M,-) cocycle/roof or shift formulas in D^+, without Cech fibre powers, their refinements, or a signed-total augmentation. The new task proves the actual Cech augmentation counit and signed resolution/refinement equations in the derived category, without proving row exactness or coefficient comparison.

lem-sfb-cech-augmentation-normalized-naturality vs lem-sc-p1-rhom-hom-derived-roof: The existing result concerns Hom(M,-) cocycle/roof or shift formulas in D^+, without Cech fibre powers, their refinements, or a signed-total augmentation. The new task proves the actual Cech augmentation counit and signed resolution/refinement equations in the derived category, without proving row exactness or coefficient comparison.

lem-sfb-cech-augmentation-normalized-naturality vs lem-sc-p1-rhom-natural-cocycle-map: The existing result concerns Hom(M,-) cocycle/roof or shift formulas in D^+, without Cech fibre powers, their refinements, or a signed-total augmentation. The new task proves the actual Cech augmentation counit and signed resolution/refinement equations in the derived category, without proving row exactness or coefficient comparison.

lem-sfb-cech-augmentation-normalized-naturality vs lem-sc-p1-rhom-hom-derived-roof-shift: The existing result concerns Hom(M,-) cocycle/roof or shift formulas in D^+, without Cech fibre powers, their refinements, or a signed-total augmentation. The new task proves the actual Cech augmentation counit and signed resolution/refinement equations in the derived category, without proving row exactness or coefficient comparison.

lem-sfb-cech-augmentation-normalized-naturality vs lem-sfb-kinjective-hom-scalar-telescope: The existing result compares two scalar towers of internal Hom complexes and their colimits; it has no Cech augmentation or coefficient-comparison square.

lem-sfb-cech-augmentation-normalized-naturality vs lem-weil-pbc-flat-restriction-derived-mate: The existing result assumes normalized flat diagram comparisons and proves a derived mate invertible; it does not construct the scalar-restriction Cech map or its canonical noninvertible comparisons.

lem-sfb-cech-augmentation-normalized-naturality vs lem-weil-pbc-derived-exchange-module-termwise: The existing result represents the etale geometric base-change mate on K-injectives; it gives no covering refinement or Cech signed-total homotopy.

lem-sfb-cech-augmentation-normalized-naturality vs lem-weil-pbc-sequential-tower-evaluation-full: The existing statement is existence of derived lifts for compatible sequential tower maps, not a canonical coefficient comparison on a Cech bicomplex.

lem-sfb-cech-coefficient-derived-comparison vs def-pe-finite-discrete-presentation-encoding: The existing node defines supplied finite-discrete coefficient presentation equivalences; it asserts no Cech coefficient-comparison theorem.

lem-sfb-cech-coefficient-derived-comparison vs lem-sbc-higher-image-raw-pullback-composition: The existing result proves a raw geometric higher-image pullback identity/composition formula on etale evaluations; it contains no scalar-restriction Cech bicomplex or total augmentation.

lem-sfb-cech-coefficient-derived-comparison vs src-sbc-exact-functor-plus-unit: The existing theorem only says the derived unit of an exact functor is invertible; the new task compares scalar restriction with nonexact direct images on all Cech columns and the total.

lem-sfb-cech-coefficient-derived-comparison vs lem-sbc-higher-image-raw-pullback-identity: The existing result proves a raw geometric higher-image pullback identity/composition formula on etale evaluations; it contains no scalar-restriction Cech bicomplex or total augmentation.

lem-sfb-cech-coefficient-derived-comparison vs def-sbc-tower-derived-evaluation-interchange: The existing node defines exact derived evaluation interchange for strict towers; it neither constructs nor proves a Cech coefficient comparison.

lem-sfb-cech-coefficient-derived-comparison vs def-weil-exact-derived-adjunction: The existing definition treats an adjunction with both functors exact; it contains no nonexact direct-image or Cech total comparison.

lem-sfb-cech-coefficient-derived-comparison vs def-coef-system-derived-transition: The existing definition localizes transitions in strict inverse coefficient systems; it has no Cech resolution or right-derived coefficient square.

lem-sfb-cech-coefficient-derived-comparison vs def-sf-scalar-reduction-categories-restriction: The existing definition specifies integral coefficient reduction categories and scalar restriction, without a Cech or right-derived comparison assertion.

lem-sfb-cech-coefficient-derived-comparison vs lem-weil-isomorphism-derived-pullback-equivalence: The existing result is a derived equivalence for a scheme isomorphism with finite torsion coefficients; it has no arbitrary coefficient-comparison Cech map.

lem-sfb-cech-coefficient-derived-comparison vs def-coef-tower-derived-evaluation-transition: The existing node defines exact tower evaluation transitions; it has no injective replacement of a scalar-restricted Cech resolution.

lem-sfb-cech-coefficient-derived-comparison vs def-sf-open-normalization-data: The existing node defines supplied normalization data for Cartesian open-immersion squares and tensor models; it proves no coefficient-comparison Cech assertion.

lem-sfb-cech-coefficient-derived-comparison vs lem-pc-open-stalk-representative-coherence: The existing equation concerns derived stalk representatives at an open immersion; it has no coherent Cech coefficient-comparison square.

lem-sfb-cech-injective-column-model vs lem-sc-injective-module-abelian-acyclic-zariski: The existing theorem is abelian cohomology acyclicity after forgetting injective modules on a Zariski or scheme-etale site, not a compatible arbitrary-ringed-topos Cech derived-column model.

lem-sfb-cech-injective-column-model vs lem-sc-injective-presheaf-module-nerve-acyclic: The existing presheaf free-nerve/exactness/Hom result concerns positive cohomology or the algebraic nerve-Hom identification; it constructs no coherent sheaf-slice direct-image injective model and no specified derived-column comparisons.

lem-sfb-cech-injective-column-model vs lem-sc-presheaf-free-nerve-comparison: The existing presheaf free-nerve/exactness/Hom result concerns positive cohomology or the algebraic nerve-Hom identification; it constructs no coherent sheaf-slice direct-image injective model and no specified derived-column comparisons.

lem-sfb-cech-injective-column-model vs lem-sc-presheaf-free-nerve-exact: The existing presheaf free-nerve/exactness/Hom result concerns positive cohomology or the algebraic nerve-Hom identification; it constructs no coherent sheaf-slice direct-image injective model and no specified derived-column comparisons.

lem-sfb-cech-injective-column-model vs lem-weil-pbc-etale-module-injective-forget-acyclic: The existing theorem is abelian cohomology acyclicity after forgetting injective modules on a Zariski or scheme-etale site, not a compatible arbitrary-ringed-topos Cech derived-column model.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-augmentation-quasi-iso: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-filtration-data-steps: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-filtration-data: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-filtration-properties: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-filtration: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-graded-augmentation-representative: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-graded-hom-ext: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-graded-normalized-differential: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-graded-normalized-iso: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-graded-resolution-representative: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-injective-image-augmentation vs lem-sp-cartan-eilenberg-cone-graded-short-complex-iso: The existing abstract Cartan-Eilenberg result assumes a bicomplex augmentation and specified filtration/column data; even its augmentation theorem assumes the row quasi-isomorphisms. The new task proves sectionwise injective Cech exactness on arbitrary topos-object slices and identifies the actual unit augmentation, which those results take as inputs.

lem-sfb-cech-augmentation-normalized-naturality vs lem-weil-pbc-kinjective-pullback-abutment: The existing formula identifies one geometric inverse-image unit/global-section Leray map, on abelian etale sheaves, without Cech totals, signed homotopies or covering refinements.

lem-sfb-cech-augmentation-normalized-naturality vs lem-weil-pbc-kinjective-unit-leray: The existing formula identifies one geometric inverse-image unit/global-section Leray map, on abelian etale sheaves, without Cech totals, signed homotopies or covering refinements.

lem-sfb-cech-augmentation-normalized-naturality vs lem-weil-pbc-derived-exchange-bounded-comparison: The existing statement transports a geometric base-change exchange comparison between bounded and arbitrary K-injective representatives; it has no Cech covering refinement or signed total homotopy.

lem-sfb-cech-augmentation-normalized-naturality vs lem-weil-pbc-derived-exchange-unbounded-transport: The existing statement transports a geometric base-change exchange comparison between bounded and arbitrary K-injective representatives; it has no Cech covering refinement or signed total homotopy.

lem-sfb-cech-augmentation-normalized-naturality vs lem-weil-pbc-free-sheaf-derived-sections: The existing theorem identifies derived Hom from a free rank-one sheaf with cohomology of derived global sections; it contains no Cech augmentation or counit/refinement equations.

lem-sfb-cech-coefficient-derived-comparison vs lem-sc-exact-functor-higher-derived-vanishing: The existing result concerns exact functors themselves (cohomology, boundedness, derived factorization or higher vanishing). Exactness is only an input to the new task, whose nonexact direct images require a new injective replacement and the canonical coherent Cech comparison square.

lem-sfb-cech-coefficient-derived-comparison vs lem-pc-ext-exact-functor-square: The existing theorem gives identities on Ext groups for exact functors and supplied comparison isomorphisms; the new task constructs actual coefficient comparisons through nonexact direct images on all Cech columns and the total derived object.

lem-sfb-cech-coefficient-derived-comparison vs lem-pc-ext-restriction-map-calculus: The existing theorem gives identities on Ext groups for exact functors and supplied comparison isomorphisms; the new task constructs actual coefficient comparisons through nonexact direct images on all Cech columns and the total derived object.

lem-sfb-cech-coefficient-derived-comparison vs lem-pc-open-tensor-restriction-representative: The existing formula pins one open tensor restriction representative; it contains no coefficient-restriction injective replacement, Cech columns or augmentation square.

lem-sfb-cech-coefficient-derived-comparison vs def-weil-pbc-derived-inverse-image: The existing definition is termwise exact inverse image on scheme-etale derived categories; it does not prove a canonical coefficient comparison through nonexact Cech direct images.

lem-sfb-cech-coefficient-derived-comparison vs lem-weil-pbc-completed-realization-derived-cohomology: The existing theorem is exact completed realization and its cohomology/shift comparison; it has no Cech direct-image or scalar-restriction augmentation square.

lem-sfb-cech-coefficient-derived-comparison vs lem-weil-pbc-exact-functor-bounded-below: The existing result concerns exact functors themselves (cohomology, boundedness, derived factorization or higher vanishing). Exactness is only an input to the new task, whose nonexact direct images require a new injective replacement and the canonical coherent Cech comparison square.

lem-sfb-cech-coefficient-derived-comparison vs lem-weil-pbc-exact-functor-complex-cohomology: The existing result concerns exact functors themselves (cohomology, boundedness, derived factorization or higher vanishing). Exactness is only an input to the new task, whose nonexact direct images require a new injective replacement and the canonical coherent Cech comparison square.

lem-sfb-cech-coefficient-derived-comparison vs lem-weil-pbc-exact-functor-derived-factorization: The existing result concerns exact functors themselves (cohomology, boundedness, derived factorization or higher vanishing). Exactness is only an input to the new task, whose nonexact direct images require a new injective replacement and the canonical coherent Cech comparison square.

lem-sfb-cech-coefficient-derived-comparison vs lem-weil-pbc-exact-functor-derived-functor: The existing result concerns exact functors themselves (cohomology, boundedness, derived factorization or higher vanishing). Exactness is only an input to the new task, whose nonexact direct images require a new injective replacement and the canonical coherent Cech comparison square.

## Dry-run repairs

The first complete dry run found additional source-tag-sharing candidates in the server snapshot. I opened their statements and added the individual distinctions above. They are generic Cartan-Eilenberg filtration tools, exact-functor facts, geometric exchange/section formulas, or positive presheaf-nerve results, rather than any of the four new assertions. No duplicate was retained and no mathematical statement needed changing.

## Original argument retained verbatim for the four new tasks

### Original step 1

The module category on each of the small ringed sites is Grothendieck abelian by [prop-pur-kinjective-resolutions-exist], hence has enough injectives by [lem-sp-grothendieck-enough-injectives]. Choose an ordinary injective resolution $a:K[0]\to I^\bullet$ with $I^q=0$ for $q<0$, in the sense of [def-sp-injective-resolutions]. It is K-injective by [lem-weil-pbc-bounded-below-injectives-kinjective]. The exact module inverse images are left adjoint to the corresponding direct images. Define $B^{n,q}=(fv_n)_*v_n^*I^q$ for $n,q\geq0$. A face deleting a factor induces the restriction map on these sheaves; the alternating sum defines $d_{\mathrm{Cech}}$. Naturality of restriction gives $d_{\mathrm{Cech}}d_I=d_Id_{\mathrm{Cech}}$, and the simplicial identities give $d_{\mathrm{Cech}}^2=0$. Thus $B$ has the total complex of [def-sp-double-complex-total], with the stipulated sign. The units of slice restriction define a chain augmentation $b:f_*I\to\operatorname{Tot}B$, landing in Cech degree zero.

Dependencies: prop-pur-kinjective-resolutions-exist, lem-sp-grothendieck-enough-injectives, def-sp-injective-resolutions, lem-weil-pbc-bounded-below-injectives-kinjective, def-sp-double-complex-total

### Original step 2

For a localization at an arbitrary topos object $A$, use [lem-trf-topos-localization-site-presentation] to present $A$ by an object of a small site. Under this presentation [lem-pur-kinjective-restrict-localized-universes] says that restriction carries $I$ to a K-injective complex. Restriction is exact, so $v_n^*a$ resolves $K_n$. Hence [lem-weil-pbc-kinjective-total-derived] identifies $Q((fv_n)_*v_n^*I)$ with $R(fv_n)_*(K_n[0])$, and $Q(f_*I)$ with $Rf_*(K[0])$. Here $Q$ denotes localization at quasi-isomorphisms. These comparisons use the right-derived comparison at the specified resolution; they are not arbitrary isomorphisms. All faces and degeneracies are induced on this one complex $I$, so they supply a compatible cosimplicial resolution, rather than independently chosen column representatives.

Dependencies: lem-trf-topos-localization-site-presentation, lem-pur-kinjective-restrict-localized-universes, lem-weil-pbc-kinjective-total-derived

### Original step 3

Fix $q$ and a site object $W$ of $\mathcal Y$. Put $A=f^{-1}h_W^\#$ and work in $\mathcal X/A$. The direct-image adjunction identifies $B^{n,q}(W)$ with sections of $I^q|_A$ over the $(n+1)$-fold fibre product of $V_A=V\times A\to A$. Present this slice and its object $V_A$ by [lem-trf-topos-localization-site-presentation]. The restriction of $I^q$ is injective: [lem-pur-kinjective-restrict-localized-adjunction-universes] gives an exact left adjoint $G$ to restriction, and a map $M\to I^q|_A$ extends across a mono $M\hookrightarrow N$ by adjoining it to $GM\to I^q$, extending across the mono $GM\hookrightarrow GN$, and transposing back. By [lem-weil-pbc-ringed-site-injective-module-injective-presheaf], its underlying module presheaf is injective. Apply [lem-sc-injective-presheaf-module-nerve-acyclic] to the map of set presheaves $V_A\to1$ to obtain exactness in positive Cech degrees. Since $v$ is epic, $V_A\to1$ is locally surjective by [lem-weil-pbc-site-sheaf-sets-epi-locally-surjective]: lift the terminal section locally, using the epi characterization before base change. The sheaf gluing axiom therefore identifies degree-zero cycles with sections over $A$, uniquely. Consequently $f_*I^q(W)[0]\to B^{\bullet,q}(W)$ is a quasi-isomorphism. This holds for every $W$, so the augmented row is exact as a complex of module sheaves.

Dependencies: lem-trf-topos-localization-site-presentation, lem-pur-kinjective-restrict-localized-adjunction-universes, lem-weil-pbc-ringed-site-injective-module-injective-presheaf, lem-sc-injective-presheaf-module-nerve-acyclic, lem-weil-pbc-site-sheaf-sets-epi-locally-surjective

### Original step 4

Apply [lem-sc-first-quadrant-column-augmentation] to $B$ with the internal and external indices chosen so that its tested complexes are the Cech rows $B^{\bullet,q}$ and its complex $A$ is $f_*I^\bullet$. The row quasi-isomorphisms are precisely step 3. The condition that the augmentation is killed by the first Cech differential is equality of the two restrictions to $V\times V$; its component in total degree $q$ is the $(0,q)$ inclusion. These are exactly the two augmentation hypotheses of that node. It follows that the specified map $b$ is a quasi-isomorphism. If one uses the transposed total convention, the comparison on bidegree $(n,q)$ is multiplication by $(-1)^{nq}$: it interchanges the two total differential conventions and is the identity at $n=0$, so it preserves this augmentation. This proves the derived descent assertion before applying $h^*$.

Dependencies: lem-sc-first-quadrant-column-augmentation

### Original step 5

Apply $h^*$ termwise to $b$. By [lem-weil-pbc-exact-functor-derived-factorization] this represents the derived exact inverse image and remains a quasi-isomorphism. In degree $r$ the identity of finite biproducts gives $h^*(\bigoplus_{n+q=r}B^{n,q})\cong\bigoplus_{n+q=r}h^*B^{n,q}$. Additivity makes this identification commute with the two differentials and their signs, hence it is a chain isomorphism $h^*\operatorname{Tot}B\cong\operatorname{Tot}(h^*B)$. Compose with the column comparisons of step 2. This gives the displayed isomorphism, represented by $h^*b$ and these finite-sum identifications. There are exactly $r+1$ possible summands for $r\geq0$, and none for $r<0$.

Dependencies: lem-weil-pbc-exact-functor-derived-factorization, def-sp-double-complex-total

### Original step 6

The component $f_*I^q\to(fv_0)_*v_0^*I^q$ is the direct image of the ordinary localization unit. On sections it sends a section to its restriction to $V$; no sign is present in Cech degree zero. For any module $M$, the composite $v^*M\xrightarrow{v^*\eta_M}v^*v_*v^*M\xrightarrow{\varepsilon_{v^*M}}v^*M$ is the identity by the adjunction triangle identity. Thus evaluating the restriction map on $V$ and then evaluating sections is the direct-image counit, with exactly this normalization. The derived version has the same representative: [lem-trf-bounded-below-derived-adjunction] identifies the derived unit and counit with the localized termwise ones through the derived comparison on the bounded-below injective model. Exact restriction makes its left-derived comparison the termwise restriction. Applying $f_*$ and $h^*$ preserves these identities, which identifies the requested augmentation and its normalization.

Dependencies: lem-trf-bounded-below-derived-adjunction

### Original step 7

For $u:K\to L$, take injective resolutions $a:K\to I$ and $c:L\to J$. By [lem-weil-pbc-injective-resolution-lift-exists] choose $t:I\to J$ lifting $u$. Restrict $t$ in each Cech degree and apply the direct images: the resulting double-complex map commutes with the units defining $b$. [lem-sp-derived-injective-resolution-naturality] identifies the source and column maps with the prescribed derived maps. Independence of choices follows from [lem-weil-pbc-kinjective-hom-derived]: two lifts have the same homotopy class. A homotopy $s$ of vertical degree $-1$ induces on the total a homotopy whose $(n,q)$ component is $(-1)^n s$; the horizontal cross terms cancel and the vertical terms give the difference of total maps. For a covering refinement $V'\to V$, the maps of fibre powers induce restrictions of sections, commute with every deletion and repetition of a factor, and commute with $b$ because their composites to $1$ agree. Therefore the same augmentation square proves refinement naturality, with composition and identities inherited from the actual restrictions.

Dependencies: lem-weil-pbc-injective-resolution-lift-exists, lem-sp-derived-injective-resolution-naturality, lem-weil-pbc-kinjective-hom-derived

### Original step 8

Let $T$ be an exact coefficient-restriction functor as in the statement, with its natural commutation identifications. It commutes with finite totals by the degreewise biproduct calculation in step 5. The resolution $TK\to TI$ is a quasi-isomorphism by [lem-weil-pbc-exact-functor-derived-factorization]. Choose an injective resolution $TK\to J$ for the new coefficients. By [lem-weil-pbc-kinjective-hom-derived] the derived map $Q(TI)\to QJ$ specified by these augmentations is represented by a chain map $t:TI\to J$, unique up to homotopy. In each slice, restrict $t$ and apply the displayed direct images. Commutation with those underived functors gives maps from $T B(I)$ to $B(J)$; they respect both differentials and the augmentation because the underived adjunction units are natural for restriction of scalars. These maps represent the canonical right-derived coefficient comparison, obtained by applying the right-derived unit to $TI$ and then the resolution comparison. Their augmentation square commutes in the derived category; the signed homotopy calculation of step 7 removes the choice of $t$. Exactness of $T$ also preserves the quasi-isomorphism $b$. This is the asserted naturality under coefficient restriction. It uses no claim that $TI$ is injective, or that a right-derived coefficient comparison is invertible.

Dependencies: lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-kinjective-hom-derived
