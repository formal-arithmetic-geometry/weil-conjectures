# Stage-1 repair: sk-prop-sfb-cartesian-coefficients

## Files written

- dag/nodes/sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients.json: existing item, statement and statement dependencies unchanged; eight assembly steps, 2742 characters in all.
- dag/nodes/sec-proetale-coefficients/lem-sfb-internal-abelian-finite-limit-creation.json: one new statement-only node, status unsplit, 1684-character self-contained categorical statement; no exact Mathlib match, zero new Mathlib leaves.
- citations.json: full verbatim statements for every node used by every parent step.
- report.md: this report and signed review. The genuine search-command log is searches.jsonl. Baseline item and the ND and Q30 reports are preserved as sandbox-only comparison material.

## Attachments

None for the whole item. I searched lean/WeilConjectures for the blueprint tag, cartesianCoefficients, and condensedPullbackHom. The closed coefficient-ring comparison is only part of the conjunction. The project module lean/Sheaf/Paper/CartesianCoefficients.lean still has sorry at the final theorem (lines 432–435) and the normalized twist-family existence theorem (356–360). The source therefore does not furnish an attachment for every clause. No Lean was written or compiled.

## WANTED

None. The blueprint and Stacks sources are present locally. No prohibited source is used.

## Return repaired and current baseline

The sandbox initially contained only four dispatcher markers: no item node, report, or search log. The current shared repository already includes Q30's accepted repair of the same 5449-character six-step proof. That repair has eight steps totaling 2545 characters and two Mathlib leaves, lem-sfb-products-zero-additive and lem-sfb-finite-exactness-nat-iso. I read that live version and both older reports, and reconstructed the sandbox from the live version, preserving the statement, imported fields, previous sources, searches, citations and review/Lean metadata. The delivery tool overlays only split-owned fields against the current server baseline; no git command was run by me in the repository.

The present delivery is a substantive further split: it adds an unsplit proof obligation for finite-limit creation by internal abelian groups, with its own arbitrary-category hypotheses, canonical operations and universal-factorization conclusion. Step 6 now applies this statement before the existing additivity criterion. The new node states no scheme-theoretic coefficient, twist, finite-free or exact-module-pullback clause of the parent. It has no proof steps, proof dependencies, or proof origin. Its proof is reserved for another worker; the complete intended construction is recorded below, so that it has not disappeared into a shorter parent text.

The old arguments are accounted for as follows. The coefficient comparison, twists and basis-induced integral/rational isomorphisms remain steps 1–3 with their existing nodes. The old category-hypothesis argument remains step 4, using the already-existing small-site abelianness statement instead of reconstructing abelian sheaves through constant-integer modules. I investigated that old reconstruction separately: lem-cbc-constant-ring-module-sheaves already gives extension of constant-ring actions to the sheafified ring; ordinary integer-module/abelian-group equivalence is also already present, and lem-kun-integer-module-abelian-equivalence states its etale instance. I therefore created no redundant integer-action lemma. The old scalar-extension/restriction argument is step 5 with the existing extension-along-iso and forgetful-functor statements. The old final step is distributed over the new finite-limit creation input, the already-landed product/zero additivity leaf, the existing exact-lift theorem, and the already-landed natural-isomorphism invariance leaf. All these arguments are either explicit assembly steps or separately named nodes; the report below supplies the new independent universal-property construction. The maximum assembly step is 545 characters and the total is below the human's 3000-character bound.

## Proof construction reserved for the new worker

For a finite diagram D of internal abelian groups, let (L,p_j) be a chosen limiting cone of its underlying diagram. The morphisms m_j composed with (p_j times p_j) form a cone with source L times L, because each transition of D is a group morphism. Its unique factorization defines m_L. The same universal property applied to the unit legs e_j and to i_j composed with p_j defines e_L and i_L. Postcomposition with every p_j reduces associativity, commutativity, both unit identities and both inverse identities to the corresponding identities in D(j); uniqueness of factorization proves them. It also proves that any alternative operations with the required projection equations equal these operations. The empty diagram is handled by uniqueness of every morphism into the terminal object, rather than assuming a nonempty family of projections.

For any cone of group objects, its unique underlying map to L respects multiplication, unit and inverse: postcompose each of the two proposed sides with every p_j and use the cone's group-linearity; limiting uniqueness then equates the sides. This proves the lifted universal property and reflection of limits. Conversely a group-object limiting cone is uniquely isomorphic to this constructed one. Forgetting that group isomorphism makes its underlying cone isomorphic to a limiting cone, proving preservation and the stated equivalence of limiting properties. This is needed in addition to creation; it is not assumed merely from the word creates.

For finite-limit-preserving F, the product and terminal comparison maps are isomorphisms. Applying F to the group identities defines the indicated operation transport and the same process on morphisms is functorial. A group-limit cone has a limiting underlying cone by the previous paragraph; F sends it to a limiting cone. The transported projections are group morphisms by their defining operation equations. Reflection of finite limits by the target forgetful functor therefore proves finite-limit preservation of F^ab. These arguments work without an adjoint for F, without a concrete set-valued category, and without abelianness of the ambient category. This is why existing site inverse-image theorems and existing adjunction-lifting nodes are not the proposed statement.

## Mathlib and duplicate searches

Every Mathlib search on the new node is an exact tool/query pair in searches.jsonl, executed with the prescribed msearch.py command. Both semantic phrasings, LeanSearch, Loogle and source grep were read. The first semantic search supplies map/additivity and left-exact-functor ingredients. The second supplies AddCommGrpCat.leftExactFunctorForgetEquivalence and concrete AddCommGrpCat/CommGrpCat forgetful limit-preservation results. I read LeftExactFunctor.lean:40–68: it assumes a preadditive source with finite biproducts and target Type; it is not the theorem about arbitrary finite-limit ambient categories and their internal group objects. I read Grp/Limits.lean:232–280: it creates concrete commutative-group limits, not internal group-object limits for arbitrary ambient categories. I read Monoidal/CommGrp_.lean, especially mapCommGrp at 199–206: it constructs operation transport but gives no finite-limit creation or preservation theorem. Loogle's CommGrp/Preserves hits refer to concrete CommGrpCat; the CommGrp/map query likewise produced concrete category formulas. The grep finds those ingredients and no generic internal-group finite-limit theorem. Hence the new node is unsplit, not a Mathlib leaf; no unavailable search is misrecorded as absence.

Before writing the node I searched the whole DAG for internal/commutative/abelian group objects together with finite limits, creation and additivity, and for the proposed id. I ran blueprint_refs.py ancestor on the item, and whole-blueprint searches for abelian group objects, internal groups, group objects limits, creates finite limits, finite-limit creation, and tensor unit normalization while considering possible extractions. None states the proposed limit-creation result. The closest existing statements were opened: the three adjunction/group-transport nodes, the group-object/sheaf reconstruction node, the general site abelian inverse-image exactness node, and the constant-ring equivalence nodes. Their distinctions are recorded below. No new definition or clone of an existing proof obligation is introduced.

## Review by Q03

I read GOAL.md, the worker and stage-1 instructions, the three levels and tool-lemma rule in SETUP.md, and delivery-errors B–E. I read the chapter record sec-proetale-coefficients and unit sk-prop-sfb-cartesian-coefficients, its source section and all three proof paragraphs in the current main-20261015 blueprint. They prescribe point-pullback comparison, twists, and integral-basis/condensed finite-free comparison; this route is retained. The item statement is byte-identical to the live baseline. I retained the earlier explicit twist domain: ell is invertible only for the twisted assertions, finite A being twisted is ell-power torsion, E and F are finite subextensions of the fixed algebraic closure, and Qbar is the finite-subextension-valued condensed ring.

For the new node I read Stacks sites.tex Tag 00YV, proposition-functoriality-algebraic-structures-topoi, part (2), and the preceding quadruple discussion (D1–D4, A1–A3). The source applies finite-limit set inverse image to those operations. The new node explicitly identifies its arbitrary-category finite-limit statement as an agent extraction: Stacks does not verbatim state this generalization. I checked the complete construction in the preceding section, including universal maps, uniqueness of operations, reflection, and preservation; no adjoint or underlying-points hypothesis has been imported from the source. I also read the cited definition nodes for products and finite limits. All objects, the finite indexing category and both ambient categories are introduced in the statement itself. The new node is a genuine universal-property argument; the parent previously moved between set-level and abelian-level products without exposing this general lifting argument as an independent task.

Step 1: sk-def-sfb-coefficient-morphisms states that alpha underlies an isomorphism of ring objects, and lem-sfb-alpha-iso states its invertibility for every condensed ring and scheme morphism. I checked both statements, not merely their proofs. This supplies the ring-object clause for arbitrary f, with no invertibility of ell used.

Step 2: det-prop-sfb-cartesian-coefficients-twists explicitly states the comparison for every integer d, including finite A, with alpha and module compatibility. I read its current statement and the domain of sk-def-sp-tate-twist. All source hypotheses are present: both schemes invert ell and a finite ring being twisted is ell-power torsion. The step invokes no unrestricted inverse-limit interchange.

Step 3: lem-sfb-local-field-integral-basis gives an actual O_E-basis of O_F of length [F:E]. det-prop-sfb-cartesian-coefficients-finite-free is conditional on precisely such a basis and supplies both induced sheaf isomorphisms, integral and rational. I opened both statements and the detailed finite-free source's basis paragraph. Thus this step does not take basis existence from a statement assuming it. E=F gives rank one; ramified and unramified finite extensions are both allowed.

Step 4: def-weil-pbc-proetale-site supplies compatible small skeletons in a larger universe. The abelian-category clause of lem-weil-pbc-site-sheaves-enough-injectives then applies; no injectivity conclusion is needed. sk-def-sfb-sheaf-tensor supplies the closed symmetric tensor structure, det-def-sfb-sheaf-tensor-closed expressly supplies additive tensor and preservation of all colimits, and sk-def-sfb-pulled-back-coefficients supplies the commutative ring objects. These verify all hypotheses of lem-sfb-modobj-abelian, including finite-colimit preservation by tensoring with the coefficient ring. Abelianness gives equalizers and coequalizers for step 5.

Step 5: I read def-sfb-module-upper-star, def-sfb-modobj-extension-along-iso and its inherited setting def-sfb-modobj-restriction-equivalence, sk-def-sfb-transport, and def-sfb-modobj-restriction. The hypotheses include braiding, closedness, equalizers/coequalizers, colimit-preserving tensor, and a commutative source ring; these are supplied by step 4 and alpha's ring isomorphism. The comparison has the correct direction Ext_alpha to Res_alpha-inverse. The action is precomposition by alpha inverse tensored with identity. The transport statement explicitly says mapMod commutes with forgetful functors, while restriction leaves objects and maps unchanged. Therefore U_X G = f^{-1} U_Y holds for both objects and morphisms. Only the lift G has this literal equality; module pullback has the specified natural isomorphism to G.

Step 6: I opened lem-weil-pbc-sheaf-algebraic-structures-objects: its statement identifies abelian sheaves with internal group objects, preserving underlying sheaves of sets and all operations. Clauses 3–4 of det-pe-topos-functoriality-inverse-image give finite-limit set inverse image and compute abelian inverse image on those underlying sets. The source Tag 00YV describes precisely its transported operations. The new node now supplies the universal-property assertion that this operation transport preserves finite limits. The terminal abelian group object is zero, and zero arrows factor through it, so terminal preservation gives zero-arrow preservation. The already-landed lem-sfb-products-zero-additive has exactly the remaining hypotheses, namely binary-product preservation in preadditive categories and preservation of zero arrows. Its conclusion is additivity. The new helper is explicitly cited in this step, not left unused.

Step 7: det-pe-topos-functoriality-inverse-image states exactness of abelian inverse image. I checked the entire statement of det-prop-sfb-module-pullback-exact-lifted: it requires abelian ambient categories, additive tensor, right-exact tensor on the two rings, additive exact F, and U_X G = F U_Y. Steps 4–6 supply each one. Its conclusion includes preservation of finite limits and finite colimits, exactly what is taken here.

Step 8: lem-sfb-finite-exactness-nat-iso states both finite-limit and finite-colimit preservation transfer for naturally isomorphic functors. It is applied from G to f^* along the inverse of step 5's comparison; this orientation was checked. This establishes exactness of the actual ringed-topos module pullback and retains its specified action comparison. The already-landed Mathlib leaves are retained without restatement or new searches claimed on their behalf.

For B1–B10 I checked standalone hypotheses and definitions, singly escaped TeX, the exact source tag and label, genuine searches and blueprint ancestry. The new node has status unsplit with empty proof/proof_deps and null proof_origin/mathlib_match. For C1/C4, the preceding step audit verifies each input against the cited statement; citations.json copies the complete statements, so no quote is bent to cover a missing assertion. The dependency list is exactly the union of uses. For D1/D2, the new node neither mentions coefficients nor restates any clause of the item: it isolates the general finite-limit universal-property argument. For E I checked empty I (terminal/trivial group), a singleton diagram (the same group), products, equalizers and the terminal ambient category. The uniqueness of operations uses joint monicity of all cone legs, with the empty case handled by terminal uniqueness. There is no claim that the ambient category is preadditive or has points. For F the finite-limit hypothesis is essential to the final consequence; a merely product-preserving F is not claimed to preserve equalizers. The identity and zero inverse-image edge cases and the empty scheme remain valid in the parent. The twist claim is not used in characteristic ell; untwisted exactness imposes no such restriction.

This repairs the return's request to spread work: one new nontrivial independent statement is left for parallel proof, with its full construction retained in this report, and the parent remains a 2742-character assembly. The existing Q30 repair and its two leaves are preserved. No agent was started; no repository, launcher, Lean, compiler, Lake or build tool was modified or run. Generic off-unit citations are declared only in split_report.tool_uses for maintainer review.

## Not duplicates

lem-sfb-internal-abelian-finite-limit-creation vs lem-sfb-products-zero-additive: the latter assumes an existing functor between preadditive categories already preserves products and zero; the new statement constructs finite-limit group structures in an arbitrary ambient category and supplies the missing preservation input.

lem-sfb-internal-abelian-finite-limit-creation vs det-pe-topos-functoriality-inverse-image: the latter is a theorem about scheme-induced pro-etale inverse images; the new statement is the universal-property construction of finite limits of internal group objects in an arbitrary finite-limit category, with no schemes, sites or adjoints.

lem-sfb-internal-abelian-finite-limit-creation vs lem-cbc-constant-ring-module-sheaves: the latter extends scalar actions from a fixed ring to its constant ring sheaf; it has no general internal-group finite-limit creation assertion.

lem-sfb-internal-abelian-finite-limit-creation vs lem-kun-integer-module-abelian-equivalence: the latter compares integer-module-valued and abelian etale sheaves; the new statement is neither an integer action comparison nor an etale specialization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sfb-site-inverse-image-multimap-universal: the existing statement is Universality of inverse-image units for natural maps with finitely many inputs; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-pe-constructible-comparison-module-exact: the existing statement is Exact faithful comparison on coefficient-sized intrinsic modules; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs def-pe-comparison-torsor: the existing node defines Torsors under the comparison inverse image of a group sheaf; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-pe-constant-left-module-transport: the existing statement is Exact normalized transport of constant left modules; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-pe-constant-left-module-inverse-image-coherence: the existing statement is Existence of normalized constant left-module comparisons; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-pe-constant-left-module-inverse-image: the existing statement is Exact geometric inverse image with arbitrary constant left-module coefficients; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-exc-intrinsic-resolution-tensor-homology: the existing statement is Tensor cohomology in the intrinsic coefficient presentation; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sf-finite-comparisons-existence: the existing statement is Section preserving finite comparisons exist; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sf-finite-compatibility-transport: the existing statement is Pinned finite comparisons preserve canonical open arrows; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-exc-intrinsic-tor-amplitude-transport: the existing statement is Transport of intrinsic Tor intervals; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs def-sf-finite-coefficient-site-hom-arrow: the existing node defines Canonical finite coefficient site internal-Hom arrow; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sf-finite-operation-comparisons: the existing statement is Prescribed finite realizations admit pinned operation comparisons; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs def-sf-finite-coefficient-site-scalar-arrow: the existing node defines Canonical finite coefficient site scalar comparison; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs def-sf-finite-coefficient-site-chain-tensor: the existing node defines Canonical finite coefficient site comparison on total tensor complexes; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs def-trf-local-oriented-projection-arrows: the existing node defines Canonical closed-point counit and normalized module projection arrows; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs def-trf-abelian-inverse-image-presentation: the existing node defines Normalized presentations of abelian inverse image; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-trf-oriented-closed-base-localization: the existing statement is Closed complementary subtopoi: factorization and supported module sheaves; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sfb-proetale-intrinsic-tensor-comparison: the existing statement is Right-tensor comparison for intrinsic constant-ring realization; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs def-sfb-ringed-site-point: the existing node defines Normalized ring and module inverse images at a topos point; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sfb-constant-scalar-geometric-adjunctions: the existing statement transports operations or an adjunction with specified unit/adjunct formulas; it does not assert unique group structures on arbitrary finite-limit cones, reflection and preservation of those cones without an adjoint.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sfb-coefficient-finite-local-systems-pullback: the existing statement is Inverse image of finitely generated module local systems on small sites; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sfb-geometric-inverse-image-constant-module: the existing statement is Geometric inverse image preserves constant module sheaves; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs def-sfb-internal-slice-derived-hom-comparison: the existing node defines Local internal module-object derived Hom and restriction comparison; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs def-weil-pbc-algebraic-inverse-image: the existing node defines Algebraic inverse image of ring and module sheaves; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-adjunction-lifts-group-ring-objects: the existing statement transports operations or an adjunction with specified unit/adjunct formulas; it does not assert unique group structures on arbitrary finite-limit cones, reflection and preservation of those cones without an adjoint.

lem-sfb-internal-abelian-finite-limit-creation vs def-weil-pbc-sheaf-pullback-unit-presentation: the existing node defines An inverse-image presentation with specified unit; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-c2-proetale-section-module-algebraic-inverse-image: the existing statement is Algebraic presentation of pro-etale internal module inverse image; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-lifted-comm-group-branch: the existing statement transports operations or an adjunction with specified unit/adjunct formulas; it does not assert unique group structures on arbitrary finite-limit cones, reflection and preservation of those cones without an adjoint.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-geometric-ring-transport: the existing statement is Ring operations transported through a geometric inverse image; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-abelian-objects-bijective-surjective: the existing statement concerns Sectionwise reconstruction is surjective on objects; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-abelian-direct-image-internal: the existing statement is The internal commutative-group identification commutes with abelian etale direct image; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-ring-inverse-image-unit: the existing statement is EtaleRingInverseImageUnit; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-abelian-objects-bijective: the existing statement concerns Sectionwise abelian-object functors are bijective on objects; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-algebraic-structures-ring-component: the existing statement is SheavesAlgebraicStructuresRing intermediate component; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-finite-coefficient-intrinsic-constructibility: the existing statement is Intrinsic finite constructibility in the fixed coefficient presentation; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-pullback-unit-presentation: the existing statement is Maps, products and equality testing for inverse-image unit presentations; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs def-weil-pbc-internal-abelian-sheaf-module-equivalence: the existing node defines Internal abelian module sheaves as sectionwise module sheaves; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs def-weil-pbc-sites-and-cohomology: the existing node defines Sites, morphisms of sites and cohomology on an object of a site; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-ring-adjunct-preserves-operations: the existing statement is The forward adjunct preserves internal ring operations; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-ring-objects-injective: the existing statement concerns Injective component of sectionwise ring-object reconstruction; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-finite-product-ring-functor: the existing statement concerns A finite-product-preserving functor transports commutative ring objects; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-inverse-image-abelian-lift-ops: the existing statement is lem-weil-pbc-etale-inverse-image-abelian-lift-ops; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-ring-hom-equiv-core: the existing statement concerns The natural hom-bijection restricts to transported ring objects; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-algebraic-structures-objects: the existing statement concerns Sheaves of abelian groups and of commutative rings are group and ring objects in sheaves of sets; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-ring-direct-image-comparison: the existing statement concerns The transported right ring-object functor is sectionwise etale direct image; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-inverse-image-comparison-addition: the existing statement is Addition transport for supplied compatible comparisons; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-inverse-image-ring-adjunction: the existing statement transports operations or an adjunction with specified unit/adjunct formulas; it does not assert unique group structures on arbitrary finite-limit cones, reflection and preservation of those cones without an adjoint.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-abelian-local-unit-representatives: the existing statement is Local unit representatives for a supplied abelian etale inverse image; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-module-pullback-section-comparison: the existing statement is Underlying sets of module pullback section comparisons; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-abelian-forward: the existing statement is The full sectionwise abelian-object functor; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-algebraic-structures-ring-morphism: the existing statement is Ring sheaf morphism criterion; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-algebraic-structures-ring-core: the existing statement is Ring sectionwise construction and operation compatibility; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-algebraic-structures-abelian-component: the existing statement is SheavesAlgebraicStructuresAbelian intermediate component; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-ring-direct-image-operations: the existing statement is Sectionwise ring-operation preservation of the etale direct-image comparison; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-slice-commRing-pullback-isIso: the existing statement is Invertibility of the canonical commutative-ring slice inverse mate; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-pullback-forget-comparison: the existing statement is Canonical forgetful comparison for sheaf inverse image, respecting units; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-ring-coadjunct-preserves-operations: the existing statement is The inverse adjunct preserves internal ring operations; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-lifted-comm-ring-branch: the existing statement transports operations or an adjunction with specified unit/adjunct formulas; it does not assert unique group structures on arbitrary finite-limit cones, reflection and preservation of those cones without an adjoint.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-ring-objects-bijective: the existing statement concerns Sectionwise ring-object functors are bijective on objects; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-inverse-image-algebraic-structures: the existing statement is Inverse image of etale sheaves of sets, abelian groups and rings; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-ringed-topos-equivalence-ring-transport: the existing statement is Transport of a single commutative ring sheaf across an equivalence; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-ring-inverse-image-counit: the existing statement is EtaleRingInverseImageCounit; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-ring-object-sectionwise-reconstruction: the existing statement concerns Sectionwise reconstruction on the identical underlying sheaf; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs new-r2-etale-abelian-kan-comparison-locally-surjective: the existing statement is Local surjectivity of the concrete underlying-set Kan comparison; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-adjunction-lifts-abelian-group-objects: the existing statement transports operations or an adjunction with specified unit/adjunct formulas; it does not assert unique group structures on arbitrary finite-limit cones, reflection and preservation of those cones without an adjoint.

lem-sfb-internal-abelian-finite-limit-creation vs def-weil-pbc-continuous-coefficient-module-encoding: the existing node defines Explicit continuous coefficient module encodings; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-abelian-objects-bijective-injective: the existing statement concerns Sectionwise reconstruction is injective on objects; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-abelian-pullback-global-sections-comparison: the existing statement is Abelian inverse-image global sections and set section comparisons; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-proetale-finite-tower-limit: the existing statement is Inverse image preserves finite constant ring tower limits; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-sheaf-ring-objects-surjective: the existing statement concerns Surjective component of sectionwise ring-object reconstruction; reconstruction of algebraic sheaves or transport of their operations is different from creating finite-limit cones of internal abelian groups in an arbitrary ambient category.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-site-pullback-abelian-underlying: the existing statement is Underlying sets commute with abelian sheaf inverse image; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-inverse-image-abelian-lift: the existing statement is Étale inverse image: abelian lift and hom-set comparison; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-constant-ring-inverse-image-comparison: the existing statement is Compatible constant-ring inverse-image comparison; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-inverse-image-abelian-lift-hom: the existing statement is lem-weil-pbc-etale-inverse-image-abelian-lift-hom; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-weil-pbc-etale-inverse-image-ring-lift: the existing statement is Étale inverse image: ring lift and hom-set comparison; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-pur-coefficient-level-ordinary-images: the existing statement is Ordinary geometric images at the constant quotient levels; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs new-lem-pur-intrinsic-lisse-fixed: the existing statement is Finite lisse condition in intrinsic and fixed-module coordinates; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sp-proetale-algebraic-inverse-image: the existing statement is Algebraic presentation of the specified pro-etale module inverse image; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs def-pur-proetale-constant-module-unit: the existing node defines Canonical rank-one comparison for intrinsic pro-etale constant modules; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sp-constant-pullback-scalar: the existing statement is Module pullback transports scalar multiplication; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs new-lem-pur-a1-pullback-lift: the existing statement transports operations or an adjunction with specified unit/adjunct formulas; it does not assert unique group structures on arbitrary finite-limit cones, reflection and preservation of those cones without an adjoint.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sp-constant-inverse-image-section: the existing statement is Transported global sections and constant quotient kernels; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs lem-pur-coefficient-pullback-exact: the existing statement is Exact constant-coefficient pro-etale pullback in independent universes; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs new-lem-pur-etale-a1-pullback-full: the existing statement is Fullness of ordinary etale affine-line pullback; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs def-sp-et-proet-coefficient-transport: the existing node defines Fixed presentation transport of the recorded intrinsic reduction comparison; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs def-sp-reduction-direct-image-comparison: the existing node defines Canonical compact-support coefficient comparison and normalized open coordinates; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs def-pd-section-derived-realization: the existing node defines Canonical derived section-module realization; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-pd-module-ringed-topos-derived-comparison: the existing statement is Module-object and ringed-topos derived tensor comparison; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

lem-sfb-internal-abelian-finite-limit-creation vs def-pd-proetale-section-module-functors: the existing node defines Normalized tensor structures on existing pro-etale section-module functors; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs def-pd-section-module-operations-data: the existing node defines Existing section-module operations and pure-tensor data; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs def-pd-section-derived-tensor-data: the existing node defines Canonical derived section-module tensor data; it does not state the generic finite-limit creation and reflection theorem for internal abelian groups.

lem-sfb-internal-abelian-finite-limit-creation vs lem-sc-etale-inverse-image-joint-representatives: the existing statement is Simultaneous local unit representatives of etale inverse-image sections; its scheme/site/module or specified-comparison setting does not give the proposed theorem for arbitrary finite-limit ambient categories, unique lifted cone operations and their universal factorization.

## Unfinished work and validation

The new finite-limit creation theorem is intentionally unsplit and unproved. All stage-1 work requested here is complete pending the required server dry run and delivery. Validation results will be appended after the tool exits.

## Server validation

The required dry run exited successfully: OK (not pushed) deliver/Q03/sk-prop-sfb-cartesian-coefficients at a150dd54996: preflight passed. This includes the server DAG/split preflight. It reported no failure requiring a repair. The new node remains deliberately unsplit. The direct-delivery brief authorizes the push without a second worker; no new reader was started. The following push reruns the delivery checks against the then-current server baseline.
