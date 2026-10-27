## Worker report

Group Q33, item lem-sf-native-weil-pullback-star-preservation, 2026-10-22. Stage 1 only; no Lean files written and no compiler, Lake or build command run. All writes are in the assigned sandbox.

## Files written

- dag/nodes/sec-six-functors/lem-sf-native-weil-pullback-star-preservation.json: statement, split; nine proof steps, fifteen existing dependencies; not in Mathlib.
- citations.json: twenty-one step/node entries, each with a verbatim excerpt or whole statement of the cited node.
- report.md: this report and signed self-review.
- write_split.py: sandbox-only editing and citation-validation helper, not a delivery file.

## New nodes

None. The existing geometric stability and coefficient comparison nodes suffice. In particular no second affine finiteness theorem or single-sheaf native preservation theorem was introduced.

## Attachments

None for the whole item. I searched live WeilConjectures/ for the blueprint tag, objectProperty_rightDerivedLowerStar, the native upperStar definitions and constructibility terminology, and read Category.lean:447-480 and LowerStar.lean:116-179. The ordinary pushforward theorem has a body without a local sorry, but its underlying finiteness proof reaches SixFunctors/ProEtale/Adic/LowerStar.lean:411-415, finiteLowerStar_singleFunctor_of_isAffine, whose body is sorry. The existing adjunction candidate does not assert preservation. The native pullback definition supplies only the pullback clause. Consequently there is no finished attachment covering the item. No transitive axiom-closure claim is made.

## WANTED

None. The relevant blueprint, Bhatt–Scholze and Stacks sources are present.

## Corrections and reuse

The statement and its statement dependencies are unchanged. There is no statement dispute. The imported item had no proof; its exact ambient operations, finite-type hypotheses, boundedness requirement and requested restrictions have all been retained.

The coefficient model is not identified with the discrete constant field. Step 2 proves that the native locally finite function ring is the finite-subextension-valued pulled-back condensed coefficient ring, using the already stated continuous-function realization and coefficient colimit. Steps 3-4 identify the module encodings and their actual ordinary derived operations. We do not claim an equivalence between the derived category of fixed pairs and fixed pairs in an underlying derived category.

The source route is clauses (1),(3) of det-thm-sf-ctf-stability-direct-images and its proof, used for the geometric underlying coefficients after these identifications. It supplies the preservation needed for f^*L and Rf_* in Step 1 of sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md, the route explicitly named by this seed's breadcrumb. The seed has no imported ancestor: blueprint_refs.py ancestor returns None. Its unit is not the unit's key-node delivery, so no unit realization fields were edited.

Whole-blueprint searches for 'native Weil' and 'Frobenius equivariant' returned no match. The underlying geometric stability node is not the same statement as native equivariant preservation, so same_as remains empty. DAG searches also found and reused the existing fixed-pair derived-forget comparison and ringed/internal derived comparison. No new-node duplicate comparisons are required.

The off-unit theorem citations are declared individually in split_report.tool_uses: geometric base-change/Noetherian/qcqs facts, continuous coefficient realization and colimit, Cartesian coefficients, module encoding comparison, the field coefficient-heart and Tor comparison, ringed-site Grothendieck property, fixed-pair derived forgetting, and the existing geometric stability theorem. They supply the stated generic tools and the source preservation input; none changes a biduality proof or the chapter route. The maintainer is asked to assess these declared tool uses at review, not to approve an alternate route.

## Mathlib searches

The five new searches are exactly those in searches.jsonl and have been appended to the item's prior search history without deleting its inherited records. They use LeanFinder twice with distinct phrasings, Loogle, the prescribed Mathlib grep command and LeanSearch. All services answered. Loogle and grep returned zero hits. LeanFinder returned perfectoid period rings, local cohomology, generic derived-category factorization and generic condensed constructions. LeanSearch returned generic sheaf pullback and module adjunctions. None states native Frobenius-equivariant bounded constructible preservation. The displayed signatures of the generic hits do not supply the missing finiteness assertion. No search was fabricated or marked unavailable when it answered.

## Review by Q33

I read the live native framework node and its source declarations: Category.lean's fixed-pair category, objectProperty, WeilComplex and upperStar; Adic/ConstantSheaf.lean's locallyFiniteFunctions; Adic/Module.lean's action and functor formulas; Adic/Constructible.lean's lisse, stratified and local constructibility definitions; LowerStar.lean's comparison and full-subcategory restriction. I read the current direct-image stability statement and its blueprint proof, the field coefficient-heart statement and source, and Bhatt–Scholze Lemma 4.2.12 and §6.8, especially Definitions 6.8.3, 6.8.6 and 6.8.8. There are no new nodes to review against separate sources.

1. The geometric hypothesis step cites lem-pod-separated-finite-type-base-change, which explicitly covers the base-changed morphism and structure maps, not merely schemes. I checked Stacks schemes.tex lemma-separated-permanence (01KU), morphisms.tex lemma-base-change-finite-type (01T4), and lemma-finite-type-noetherian (01T6). The Noetherian and qcqs statements are exactly those in the two other cited nodes. Finite type, rather than only local finite type, retains quasi-compactness of the target. The base is the algebraic closure of the finite field and has the same positive characteristic.

2. The two continuous-coefficient citations were opened. The realization node states the sheaf C(|U|,E), its pullback-from-point realization and compatibility with continuous coefficient maps and finite products. The colimit node states the ring-sheaf colimit over finite E. The elementary basis/compositum argument written in this step proves that this colimit has precisely the native local finite-dimensional-span condition. The pointwise ring formulas check multiplication, restriction and the precomposition coefficient maps. This removes the otherwise unjustified coefficient identification.

3. This elementary encoding step gives mutually inverse action constructions, with the underlying sheaf and all linear maps unchanged. The native definition provides the module object over B; the module-sheaf definition provides its ordinary sectionwise action. Restriction along the constant scalars recovers exactly the original Omega-vector-space action. Kernel and sheafified cokernel formulas make the equivalence exact; the inverse degreewise constructions also preserve quasi-isomorphisms. Nothing is chosen from a sorried existence theorem.

4. I opened lem-pd-module-ringed-topos-derived-comparison and checked its actual statements about additive exact encodings, ordinary total derived pushpull, and the section formula for pullback. It applies to separated finite-type schemes over a positive-characteristic field, as established in Step 1. The Cartesian coefficient node explicitly states the invertible coefficient map and exact module pullback. The separate K-injective sentence is justified by transporting the acyclic-test Hom complexes through the explicitly inverse exact encodings, rather than assuming that arbitrary exact functors preserve K-injectives.

5. I checked the coefficient-heart node's initial equivalence of constructibility with stratified pro-etale local finite freeness, and det-def-localizing-closure-ctf-equals-bc(2)'s qcqs bound and Dctf=Dbc assertion. Neither was used for a stronger all-coefficient claim. The finite partition refinement is written explicitly; on the Noetherian geometric schemes its locally closed pieces are constructible. The finite scalar models are ordinary finite-dimensional Omega-vector spaces, so choosing bases gives exactly the native ranks, including zero and varying ranks on cover members.

6. The ring-sheaves node states the Grothendieck property for arbitrary small ringed sites, with the common coefficient universe specified. I checked Stacks injectives.tex remark-existence-D (079Q), final sentence, and definition-grothendieck-conditions (079B). The fixed-pair comparison states exactness and conservativity of forgetting and preservation of K-injectives for additive autoequivalences. The native Frobenius is an automorphism. The cohomology equality follows by the kernel/cokernel computation written here; conservativity then detects zero in every degree. This verifies both directions of the boundedness criterion.

7. I read RightDerivedFunctor/IsoAlgebra.lean:62-97, especially the actual rightDerivedFunctorMapOfNatIsoCompForgetIso, and the native lowerStar transport formula. Its comparison is for total ordinary right derivation on the fixed-pair abelian category. The cited fixed-pair node states precisely this comparison, not just an underived identity. Pullback equality after forgetting is termwise the native formula. Both comparisons use the same operations retained in Step 4.

8. The stability citation is the existing node's clauses (1),(3), not a declaration proving only an adjunction. Its enumerated coefficients include the particular finite-subextension-valued Omega from sk-def-sfb-qlbar-condensed. Step 5 supplies finite Tor amplitude of the inputs and Step 1 supplies all geometric assumptions. Boundedness of the outputs follows from Dctf membership and is reflected by forgetting, so no uniform native cohomological bound or finite-stalk theorem was silently assumed.

9. The final elementary step cites the native framework's explicit restriction definitions. I compared them with Category.lean:472-480 and LowerStar.lean:171-179: the objects and morphisms are the ambient ones, with membership proofs only. Thus the named restrictions are the actual functors requested in the item.

Small cases checked: empty source or target where a morphism exists; zero sheaves and complexes; rank zero; inputs in a single arbitrary degree; the identity morphism; open and proper morphisms; and cover members having different finite ranks. An empty scheme has only zero module sheaves, so the empty finite covering and partition cause no exception. For an identity the comparisons identify the same underlying functor. A sheaf with a finite cohomological interval is sent into a finite interval, including arbitrary shifts; no bounded-below-only inference is used. The non-quasi-compact disjoint union of projective spaces in increasing dimension is outside the finite-type target hypothesis and is not implicitly admitted.

I checked B–E of delivery-errors.md against the node and its citations. No new statement-only nodes, Mathlib leaves, duplicate lemmas or restatements of clauses were introduced. The existing-node dependency closure was inspected for cycles back to this item and none was found. proof_deps is exactly the union of uses. Every cited statement was opened; citations.json preserves verbatim supporting statements. All nine steps are under 2000 characters; the coefficient and encoding arguments are explicitly written and the non-elementary derived comparison and finiteness are separately cited. No forbidden source route is used. The substantive correction during this reading was to avoid duplicating the affine finiteness/finite-cover reduction when the existing coefficient stability theorem already supplies it after the explicit native-model comparison.

## Validation

The preliminary server review_split check passed with zero new nodes; its note that sk-prop-sf-biduality-general has no realization recorded concerns the existing unit, which this non-key item does not edit. The required complete delivery dry run will be run after this report is written, with every failure repaired before pushing.
