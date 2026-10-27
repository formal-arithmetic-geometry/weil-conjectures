# Q27 stage-1 direct delivery

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-algebra-directed-colimit-finite.json`: retained statement; five-step proof re-split from the existing nine-step argument. The parent proof has 2259 characters.
- `lem-weil-pbc-kernel-ideal-directed-pairs.json`: new statement, unsplit; no Mathlib match.
- `lem-weil-pbc-generated-ideal-quotient-colimit.json`: new statement, unsplit; no Mathlib match.
- `lem-weil-pbc-directed-pairs-colimit-transitivity.json`: new statement, unsplit; no Mathlib match.
- `lem-weil-pbc-finite-quotient-eventual-finiteness.json`: new statement, unsplit; no Mathlib match.

All five JSON files are under `dag/nodes/sec-proper-base-change/` in this sandbox. Four new nodes, zero new Mathlib leaves. `citations.json` contains one verbatim statement quotation for every parent step/node pair. `searches.jsonl` is the search command's unmodified log. Sandbox-only editing scripts, `prior-proof.json` and `report-initial.md` retain this attempt's earlier work; they are not library files.

## Attachments

None. Exact blueprint-tag and declaration searches, followed by searches for integral/colimit and quotient/fiber concepts in `lean/WeilConjectures/`, found no exact finished declaration. The existing parent theorem `AlgebraicGeometry.integral_algebra_directed_colimit_finite` is at `lean/Sheaf/AlgebraicGeometry/IntegralAlgebraDirectedColimitFinite.lean:96` and ends in `sorry`. Its signature states both clauses with the qcqs hypotheses. It cannot be an attachment. No Lean was written or compiled.

## WANTED

None. All sources used are local. No SGA source is used.

## What was wrong and corrected

This sandbox initially had no item or report; the repository item already contained a 12821-character nine-step split and a stage-2 statement. I copied and reviewed that work. The first dry run rejected a lightly clarified version because the server enforces the human's 2026-10-21 re-split requirement: at most 3000 proof characters, carrying the argument into at least four new statement-only nodes. I therefore extracted four independent technical arguments rather than deleting the work. The old proof is retained in sandbox `prior-proof.json` and its arguments are assigned to the new nodes below.

The original directed-pairs step wrote a symmetric-algebra transition immediately before a map into its kernel. The map actually used is its restriction to that kernel. The new directed-pairs statement explicitly assumes this kernel-preservation, and the parent derives it from compatibility to A. Its index relation is a preorder, not necessarily an antisymmetric order. All index collections are sets, so every colimit is small.

No statement correction or STATEMENT-DISPUTED claim is needed. The blueprint ancestor and via chain are retained, its place now cites paragraph 3 of the current main-20261015 proof of `lemma-weil-pbc-h1-constructible-representation` (the finite-pushforward lemma), and `same_as` is now `[]` after whole-blueprint searches. No unit or chapter route changes.

## Searches and Mathlib verdicts

Before making any new node I searched the whole DAG by tags 0817/086N/05JS and kernel, quotient, eventual-finiteness, fiber-colimit and iterated-colimit concepts, including a parsed search of node statements to avoid treating incidental proof references as matches. Whole-blueprint searches via `tools/blueprint_refs.py` covered `integral algebra`, `0817`, `finite subalgebras`, `iterated colimit`, `quotient colimit`, `eventual finite`, `fibre colimit`, `kernel quotient`, `086N`, and `directed pairs`. None states a proposed node. The generic product-index Fubini node was read: it assumes a product category, whereas our pair relation has varying fibers and no transition functors on them.

Every node has its own actual msearch queries: Lean Finder twice, Loogle, grep, and LeanSearch. The new-node LeanSearch calls were rate limited and are recorded as `unavailable`, never as no match. The initial parent LeanSearch answered normally. The first quotient Loogle pattern used an unknown identifier, which is recorded honestly; I also ran the valid `Ideal.quotientMap` pattern and read its source. The exact logged query strings and actual hits are in each node.

For the first node, filtered-preorder instances and directed systems of finitely generated modules do not supply the pair diagram or its lifting property. For the second, `SheafOfModules.Presentation.isColimit` gives a module presentation cocone, not a directed algebra-quotient colimit; ring quotient maps likewise do not give the sheaf result. For the third, I read `CategoryTheory/Limits/Shapes/Grothendieck.lean`, especially `fiberwiseColimit` at line 55 and `isColimitCoconeOfFiberwiseCocone` at line 175. They require a specified Cat-valued functor and transition functors between fibers. Our arbitrary pair relation provides only eventual lifts and need not have least lifts or any chosen functorial action on K_i; constructing a Grothendieck model and its final comparison is additional work, not a one-line specialization. For the fourth, ring integral-plus-finite-type criteria and finite-cardinality quotient facts do not state eventual module finiteness over a finite affine cover. The relevant ring source at `RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean` and the integral-adjoin theorem at `IsIntegral/Basic.lean:226` were read.

## Review by Q27

I read the item source in `literature/stacks-project/properties.tex`: Tag 0817, `lemma-integral-algebra-directed-colimit-finite`, both clauses and the complete proof. I read its cited constructions 05JS and 086N and the preceding finite-type-subalgebra theorem 05JT; I checked the labels in `tags/tags`. I also read module approximation 01PK in properties.tex and the complete hypothesis list of Modules 01BS in modules.tex. The main-20261015 blueprint ancestor and its proof were read. All cited node statements, including definitions, were opened rather than inferred from titles. The quotations in citations.json are the statements actually read.

The five parent steps were checked as follows.

1. The finite-type-subalgebra theorem supplies the nonempty directed collection and the colimit in all algebra sheaves. The integral-generators leaf supplies exactly finite algebra generators integral over the base implies module finite. Subalgebras inherit monic equations, and module generators generate as an algebra. This gives the entire first clause without moving it to a child node.
2. The module approximation node applies because X is qcqs. The affine module node states that finite-presentation modules are quasi-coherent and that their affine sections are finitely presented. The symmetric-algebra node supplies the universal property and functoriality, hence compatible transitions and maps to A. The kernel/image/ideal node supplies quasi-coherent kernels and images and their affine formulas. The ring symmetric-algebra node supplies finite generation by the module generators. Thus each image B_i is finite type, and step 1 makes it finite. On affines S_i/J_i identifies with its image by the ordinary first isomorphism: send a residue class to its image, well-defined by the kernel, injective by the kernel identity and surjective by the image definition. These maps respect restrictions and therefore give the sheaf identification.
3. Apply the same module approximation to the quasi-coherent kernel J_i. The first new node has precisely these hypotheses, and states directedness, lifting to any later first coordinate, and the compatible quotient diagram. It assumes neither symmetric algebras nor integrality. For finite presentation of Q_ik, the affine module node gives F_i(U) finitely presented and E_ik(U) finitely generated; the symmetric-algebra node identifies S_i(U), and the ring symmetric-algebra quotient theorem explicitly states that quotient by the resulting finitely generated ideal is finitely presented. No new lemma is created for this short specialization.
4. The second new node states the row colimit with its actual quotient legs, so its identification is compatible with the quotient arrows of the first. The existing affine-module-colimit node represents every section of A by some F_i(U); its image lies in B_i(U). All B_i are subalgebras of A and the transitions are their inclusions, so equality of two representatives is witnessed at a common upper bound. The algebra-colimit node gives existence and affine-section computation, the elementwise and ring-zero leaves justify representative/equality tests, and the affine-basis isomorphism leaf gives the sheaf comparison. The third new node then applies with D(i,k)=Q_ik and B_i as constructed. Its lifting hypothesis comes exactly from the first new node, its row-colimit hypothesis from the second, and its compatible legs from the quotient identities. It states the global colimit conclusion used here.
5. The fourth new node applies to fixed S_i (finite type), J_i (quasi-coherent), finite quotient B_i, and the directed module approximation of J_i. It gives an actual bound k_0(i), not merely some finite quotient. Increasing k at fixed i gives cofinality; taking an upper bound of two pairs and then increasing k gives directedness. The cofinal-full-subcategory leaf applies to the opposite thin categories, with every object receiving a map from the restricted subcategory. Its statement gives exactly the canonical colimit isomorphism. The quotient maps to A are the inherited compatible legs. This completes the second clause.

The four new-node statements were checked against their sources and against small cases. They contain statements only, with no proof steps or proof dependencies.

- **Directed pairs:** the source is 0817's factorization square, using 01BS, and the ideal-containment ordering spelled out in 05JS. A complete proof will restrict sigma to J, factor each map from a finitely presented E into the later kernel colimit, take common upper bounds in K_j, and use the quotient universal property. The source of the Hom-factorization is finitely presented and X is qcqs; no finite-generation-only factorization is asserted. Identity and composition follow from uniqueness of quotient maps. Antisymmetry is unnecessary. Singleton I or K_i works; zero kernels and noninjective E maps are allowed.
- **Fixed quotient row:** the source is 086N's quotient-colimit equality, used again in 0817. On an affine open, a quotient element lifts to S(U). If its image in S(U)/J(U) vanishes, its lift belongs to J(U), hence comes from an E_k(U); at a common later index it belongs to the generated ideal and dies. Surjectivity is immediate from quotient representatives; the existing algebra-colimit and affine-basis nodes turn this into the sheaf colimit. This is a sheaf-level identification with the specified legs, not an existence theorem for colimits. No qcqs hypothesis is needed here because affine sections of directed quasi-coherent module colimits already have the stated property. E_k need not embed in J. Taking J=0 or J=S gives the expected S or zero colimit.
- **Colimit transitivity:** the source is the first final equality of 0817, with the categorical argument implicit there reconstructed explicitly in this report. Given a D-cocone to T, restrict to K_i and obtain unique maps B_i -> T. To prove their compatibility for i<=j, test on each D(i,k), lift (i,k) to some (j,l) using (c), and use the D-cocone identity and the assumed compatibility of b. Uniqueness on the row colimit proves compatibility on B_i, hence there is a unique map L -> T. Testing first on each row and then on L proves its universal property. No choice of least lifts, no cartesian product shape, no preservation of colimits by a functor is assumed. Singleton fibers reduce to an ordinary cocone; extra arrows within one fiber cause no difficulty because the b maps are required compatible with every P arrow.
- **Eventual finiteness:** the source is the final paragraph of 086N, used by 0817. Choose a finite affine cover and finitely many algebra generators of S on each member. Their images in the finite quotient satisfy monic polynomials. Each corresponding polynomial in S belongs to J(U), hence is represented in some E_k(U). Directedness puts all finitely many such relations at one index. At every later index all generator images in S/I_k satisfy those equations, so the integral-generators leaf gives module finiteness on the cover; the affine module criterion gives it on every affine open. This does not assume finite presentation of S or E, nor finite generation of J. Empty X gives an empty set of relations and any index works; S/J=0 gives eventual killing of the unit. Nonnoetherian quotient examples are included.

I checked B-E of delivery-errors individually. In particular the new statements introduce every object, specify module versus algebra colimits, define generated ideal and quotient sheaves, and cite their notions. Each non-elementary comparison used by the parent is a cited statement; the construction steps still carry the short arguments. None of the new statements is a clause of the parent: they fix arbitrary kernel systems or one fixed finite-type algebra, or are purely categorical. No new node assumes the parent or one of its consumers. The parent has no step over 2000 characters and its total proof is below 3000. The formerly long non-elementary arguments are in the four unsplit nodes, with the retained arguments above available for the next workers.

## Not duplicates

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-finite-presentation-hom-directed-colimit: the existing node factors one Hom into a directed module colimit; the new node constructs a single directed preorder and algebra quotient diagram out of many such factorizations.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-module-directed-colimit-underlying-sets: the existing node compares underlying sheaf colimits of modules; it supplies no ideal-containment pair preorder or quotient diagram.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings: the existing node supplies finite coverings with quasi-compact intersections; it supplies no algebra ideal approximations or transition diagram.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-symmetric-algebra-finite-presentation: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the existing node is a ring-level symmetric-algebra presentation theorem.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-quasi-coherent-symmetric-algebra-affine: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the existing node identifies symmetric-algebra sections on affine opens.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-symmetric-algebra-sheaf-construction: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the existing node constructs the symmetric algebra sheaf.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-integral-morphism-limit-of-finite: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the existing node constructs finite approximating schemes for an integral morphism and is a consumer of this parent.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-quasi-coherent-symmetric-algebra: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the existing node gives a symmetric-algebra universal property and affine sections.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-algebra-directed-colimit-finite-type: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the existing node ranges over all finite-type subalgebras of a given algebra, not these kernel-ideal pair or row systems.

lem-weil-pbc-kernel-ideal-directed-pairs vs def-weil-pbc-quasi-coherent-algebra: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the existing node defines the algebra category and its properties and proves none of these comparison or eventual-finiteness assertions.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-integral-algebra-directed-colimit-finite: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the parent has an integral algebra and produces finite approximations; this is a proper technical subargument independent of integrality of that algebra.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-quasi-coherent-symmetric-algebra-core: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the existing node gives the symmetric-algebra sheaf core construction.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal: the new node constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the existing node gives quasi-coherence and affine formulas for individual kernels, images, ideals and quotients, not directedness, a colimit identification or eventual finiteness.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-symmetric-algebra-finite-presentation: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the existing node is a ring-level symmetric-algebra presentation theorem.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-quasi-coherent-symmetric-algebra-affine: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the existing node identifies symmetric-algebra sections on affine opens.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-symmetric-algebra-sheaf-construction: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the existing node constructs the symmetric algebra sheaf.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-integral-morphism-limit-of-finite: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the existing node constructs finite approximating schemes for an integral morphism and is a consumer of this parent.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-quasi-coherent-symmetric-algebra: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the existing node gives a symmetric-algebra universal property and affine sections.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-algebra-directed-colimit-finite-type: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the existing node ranges over all finite-type subalgebras of a given algebra, not these kernel-ideal pair or row systems.

lem-weil-pbc-generated-ideal-quotient-colimit vs def-weil-pbc-quasi-coherent-algebra: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the existing node defines the algebra category and its properties and proves none of these comparison or eventual-finiteness assertions.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-integral-algebra-directed-colimit-finite: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the parent has an integral algebra and produces finite approximations; this is a proper technical subargument independent of integrality of that algebra.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-quasi-coherent-symmetric-algebra-core: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the existing node gives the symmetric-algebra sheaf core construction.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal: the new node identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the existing node gives quasi-coherence and affine formulas for individual kernels, images, ideals and quotients, not directedness, a colimit identification or eventual finiteness.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-symmetric-algebra-finite-presentation: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the existing node is a ring-level symmetric-algebra presentation theorem.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-quasi-coherent-symmetric-algebra-affine: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the existing node identifies symmetric-algebra sections on affine opens.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-symmetric-algebra-sheaf-construction: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the existing node constructs the symmetric algebra sheaf.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-integral-morphism-limit-of-finite: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the existing node constructs finite approximating schemes for an integral morphism and is a consumer of this parent.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-quasi-coherent-symmetric-algebra: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the existing node gives a symmetric-algebra universal property and affine sections.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-algebra-directed-colimit-finite-type: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the existing node ranges over all finite-type subalgebras of a given algebra, not these kernel-ideal pair or row systems.

lem-weil-pbc-directed-pairs-colimit-transitivity vs def-weil-pbc-quasi-coherent-algebra: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the existing node defines the algebra category and its properties and proves none of these comparison or eventual-finiteness assertions.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-integral-algebra-directed-colimit-finite: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the parent has an integral algebra and produces finite approximations; this is a proper technical subargument independent of integrality of that algebra.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-quasi-coherent-symmetric-algebra-core: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the existing node gives the symmetric-algebra sheaf core construction.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal: the new node is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the existing node gives quasi-coherence and affine formulas for individual kernels, images, ideals and quotients, not directedness, a colimit identification or eventual finiteness.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-symmetric-algebra-finite-presentation: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the existing node is a ring-level symmetric-algebra presentation theorem.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-quasi-coherent-symmetric-algebra-affine: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the existing node identifies symmetric-algebra sections on affine opens.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-symmetric-algebra-sheaf-construction: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the existing node constructs the symmetric algebra sheaf.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-integral-morphism-limit-of-finite: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the existing node constructs finite approximating schemes for an integral morphism and is a consumer of this parent.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-quasi-coherent-symmetric-algebra: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the existing node gives a symmetric-algebra universal property and affine sections.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-algebra-directed-colimit-finite-type: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the existing node ranges over all finite-type subalgebras of a given algebra, not these kernel-ideal pair or row systems.

lem-weil-pbc-finite-quotient-eventual-finiteness vs def-weil-pbc-quasi-coherent-algebra: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the existing node defines the algebra category and its properties and proves none of these comparison or eventual-finiteness assertions.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-integral-algebra-directed-colimit-finite: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the parent has an integral algebra and produces finite approximations; this is a proper technical subargument independent of integrality of that algebra.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-quasi-coherent-symmetric-algebra-core: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the existing node gives the symmetric-algebra sheaf core construction.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal: the new node gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation; the existing node gives quasi-coherence and affine formulas for individual kernels, images, ideals and quotients, not directedness, a colimit identification or eventual finiteness.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-generated-ideal-quotient-colimit: the former constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the latter identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-directed-pairs-colimit-transitivity: the former constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the latter is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis.

lem-weil-pbc-kernel-ideal-directed-pairs vs lem-weil-pbc-finite-quotient-eventual-finiteness: the former constructs the directed pair preorder and compatible quotient arrows, without any colimit or finiteness conclusion; the latter gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-directed-pairs-colimit-transitivity: the former identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the latter is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis.

lem-weil-pbc-generated-ideal-quotient-colimit vs lem-weil-pbc-finite-quotient-eventual-finiteness: the former identifies the fixed-algebra quotient colimit, without finite presentation, integrality or eventual finiteness; the latter gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-weil-pbc-finite-quotient-eventual-finiteness: the former is a category-theoretic comparison for varying directed fibers, without any algebra hypothesis; the latter gives eventual finiteness for quotients of one fixed finite-type algebra, without constructing the parent approximation.

lem-weil-pbc-directed-pairs-colimit-transitivity vs lem-pc-colimit-fubini: the new node handles a varying family K_i with an arbitrary lifting preorder, whereas the existing statement assumes a product J times K.

lem-weil-pbc-finite-quotient-eventual-finiteness vs lem-weil-pbc-eventually-finite: that node assumes an inverse system of schemes with finite transitions and an integral limit; it does not state the algebra-sheaf quotient assertion or supply its monic-relation bound. Passing through relative Spec and its limit comparison would require further theorems, not a one-line specialization; the present lemma follows the local monic-relations argument of 086N directly.

## What remains unfinished

The parent is split. The four new statement-only nodes remain unsplit for subsequent workers; their proofs are not falsely marked completed. No stage-2 or stage-3 work is authorized here. The prescribed dry run and push are the final validation and delivery steps.
