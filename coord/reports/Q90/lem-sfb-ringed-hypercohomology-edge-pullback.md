# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-hypercohomology-edge-pullback.json: item, four-step split, unchanged statement and statement dependencies; Mathlib no match.
- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-hypercohomology-shifted-unit.json: one new statement-only node, unsplit; Mathlib no match, zero Mathlib leaves.
- citations.json: eight entries quoting the statements used by the four steps.
- searches.jsonl: actual msearch receipts; auxiliary scripts and duplicate_statements.json are sandbox research only.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by hypercohomology, edge/pullback, shifted unit and cocycle. The existing HypercohomologyLeftEdgeCanonical and HypercohomologyEdgeCocycle files concern natural-indexed complexes and a general left exact functor, not this unbounded ringed-topos pullback identity. Scheme DerivedTensorHomSectionsUnit and DerivedStructureSheafHomHypercohomology also do not give the arbitrary ringed-site statement with edge evaluation. No declaration was treated as finished merely because it lacks a literal sorry in the displayed fragment.

## WANTED

None. All mathematical sources used are present in literature/stacks-project. No SGA source is used.

## Findings and changes

The item had an empty proof, not a completed earlier attempt. Its full statement was retained. In particular I did not replace nonflat tensor pullback by exact inverse image or require an isomorphism for r. The discarded informal route would have needed unjustified global lifts of a cocycle through a K-flat resolution. The actual proof uses a morphism from the shifted unit instead, so no such lift is assumed.

The new prerequisite does not restate the item: it concerns one ringed site, no g, no t, no pullback-edge square, and computes a class as a derived morphism and its cohomology-sheaf evaluation. Its proof obligation is the representative-normalized Hom/hypercohomology identification, including compatibility with the *canonical* global-sections adjunction. Moving the adjunction computation or nonflat r identity into that node would have repeated the item; both remain explicit steps of the item.

I read the latest blueprint via literature/blueprint/latest (main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8), especially sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (3). Its composition of direct images is consistent with the normalized composition used here. This supporting lemma is far below the inherited alteration/Picard/affine-relative-cup chain. The ancestor command reports null, as it already does for the item; I preserve that result and extend via by the item for the new node. No chapter or unit record is changed. Blueprint searches for hypercohomology, shifted unit, global Hom, 08JA, cohomology sheaf, and tensor cohomology found no equivalent imported blueprint node.

## Unfinished work

Nothing required of this one-level split remains in the worker's scope. The new shifted-unit prerequisite is intentionally unsplit and carries no proof or proof dependencies, as required for a new node.

## Review by Q90

I read sites-cohomology.tex Tag 0BKV, label lemma-sheafification-cohomology, including its actual quotient-of-cycles proof; Tag 0D6H, lemma-Leray-unbounded, whose proof passes through the punctual ringed topos and derived pushforward composition; Tag 07A6, lemma-adjoint, and its reference to the general derived adjunction; and Tag 08JA, lemma-section-RHom-over-U, especially its global assertion and K-flat/K-injective proof. For the tensor normalization I read Tag 07A4, lemma-pullback-tensor-product. The nonflat edge identity is an agent proof assembled from these constructions, not a theorem attributed verbatim to 0BKV or 0D6H. The new node's source is 08JA together with 0BKV; its adjunction is the existing 07A6 dependency. I also read derived.tex lemma-K-injective: maps into a K-injective in the derived category are precisely homotopy classes of cochain maps.

For the new node, choose a K-injective I for K. Cochain maps O in degree n to I are exactly global cycles z in degree n, by evaluation at the compatible unit section. Cochain homotopies are exactly global boundaries, since the homotopy component is a map O to I in degree n-1. Localization into I is fully faithful on homotopy classes (the K-injective lemma). This gives the asserted bijection. Taking cohomology of the cochain map sends 1 to the sheaf class of z, proving the edge evaluation and its independence/naturality. For the external A normalization, A in one degree is projective and K-flat, and its ordinary pullback is O in that degree. The ordinary sections adjunction identifies the same cochain map with A_n to Gamma(I) by evaluation at 1. The canonical derived adjunction uses these resolution comparisons, so its map is this same bijection, rather than an unspecified automorphism. These arguments justify all clauses of the statement with no assumption that O is A-flat. The statement contains none of this proof text; it remains a statement-only obligation.

Step 1 uses the *statement* of shifted-unit, specifically gamma and e(x)=H^n(gamma(x))(1). The source and target sites meet its smallness and commutative-ring hypotheses. A acts on target sections through the structural map, and Rg_* already retains that action, so the argument need only forget scalars at the end. There is no change of hypercohomology group. I checked that the canonical morphism to (Set,A) exists without a final object of the chosen site: its ordinary right adjoint is compatible families of sections, and its left adjoint is sheafified extension of scalars from constant A-modules.

Step 2 uses shifted-unit's explicit *adjunction normalization*, projection-mate-exact's canonical adjunction and shifted tensor-unit comparison, and ringed-derived-monoidal-comparisons' statement that c and kappa identify the composite adjunction. I opened all three statements: the last one says this compatibility, not just existence of some composition iso. I expanded the unit naturality, counit naturality and triangle identity, obtaining epsilon_D L(R(v) eta)=v. Thus the prescribed P, with the prescribed Leray comparison, really corresponds to t L(u); I did not use a bare existence-of-an-adjunction theorem to infer this normalization. The two existing foundational lemmas are reported as tool uses; neither imports geometry from another unit.

Step 3 uses the cup definition's explicit flat-term K-flat prescription [z] tensor [w] to [z tensor w], and its canonical resolution identifications. Applying a cochain map on the second tensor factor before or after tensoring agrees termwise; passing to cohomology and sheafification preserves equality. That proves the naturality needed for r, rather than silently invoking a separate base-change theorem. Inverse image is exact by the item's hypotheses. Only the source U_n has to be flat, and it has one free rank-one term over O. For this source r sends b tensor a to ba, so its value on the pulled-back unit is exactly 1. There is no shift sign: the scalar factor has degree zero and the signed total tensor is used without swapping factors. Projection-mate-exact supplies exactly the shift and unit comparisons used for this normalization.

Step 4 reuses shifted-unit's edge evaluation and composes the equalities already established, then writes the naturality equation for r and explains postcomposition in t. It invokes no new vanishing, spectral sequence, flatness, or gluing result. All cited statements are quoted verbatim in citations.json, and proof_deps is their union. Steps 3 and 4 are elementary computations from these statements/definitions, not concealed lemmas. No step exceeds 2000 characters (480, 848, 919, 735), so none hides a long subsidiary comparison.

Small cases: if g is the identity, the unit comparison makes r the identity and the formula reduces to edge naturality for t. For K=O_n, r is b tensor a to ba and gamma is evaluation on 1, including n=0. For the punctual site with Z to F_2 and K=[Z --2--> Z] in degrees -1,0, H^0(K)=F_2 and H^0(F_2 tensor^L K)=F_2; r^0 and the P formula are the quotient map on classes. Shifting this complex so its two terms lie in 0,1 also tests degree 1 and the extra Tor class in degree 0: no step identifies all cohomology with ordinary tensor of cohomology. With K=(F_2)[0] under Z to F_2, the derived pullback has nonzero H^{-1} as well as H^0, so the proof explicitly permits the nonflat behavior and asserts no isomorphism in all degrees. Zero coefficient rings, zero modules, and a degenerate/empty topos give zero classes and the unique unit section, so the equality still holds. Arbitrarily unbounded K is allowed because maps into a K-injective and maps out of the single shifted unit are computed in fixed degree without truncating K. No enough-projectives assumption on sheaves enters; projectivity is used only for A over itself on the punctual module category.

I checked delivery-errors B1-B10: the new statement introduces C,O,A,s,K,n,I, uses the existing definitions, has single-escaped TeX and named tag labels, no proof/proof_deps, no fabricated Mathlib match, and real logged searches. C1-C8: each non-elementary comparison is a cited statement; no proof-body interface or missing-hypothesis specialization is used; the graph has no backward citation to the item from the new node. D1-D5: the item contains its adjunction and cocycle naturality calculations; the new node neither repeats its pullback square nor takes over a clause. E1-E7: exact inverse image is kept distinct from nonexact tensor pullback, all comparisons have the correct source/target, the unit shift uses degree n, and the nonflat cases above were checked. I corrected the initial plan to avoid global K-flat cocycle lifts, and chose a common external A on both sides to make scalar restriction explicit. No statement dispute or source error was found.

## Mathlib searches

The item was searched with leansearch, leanfinder, loogle and grep and a second semantic phrasing. The new shifted-unit statement was separately searched with the corresponding plain-language statement, leanfinder in two phrasings, loogle DerivedCategory/SheafOfModules, and grep of both sheaf modules and all Mathlib. Every query in the new node is present in searches.jsonl, with the actual returned hit digest. All services answered in this session. I read SmallShiftedHom.lean (toSmallShiftedHom and its cocycle formula) and Sites/SheafCohomology/Basic.lean (H is Ext from constant Z to a single abelian sheaf). Neither states the unbounded ringed-site bijection together with adjunction/edge normalization. PullbackFree.lean pushforwardSections_unitHomEquiv (72-78) and pullbackObjUnitToUnit (86-98) are ordinary module-sheaf adjunction facts, not the unbounded hypercohomology identification; Sites/GlobalSections.lean GammaHomEquiv naturality is underived as well. Therefore neither item nor new node is a Mathlib leaf.

## Not duplicates

I searched the whole DAG by 08JA, 0BKV, 07A6 and by the statement's key words, and opened the statements of the candidates below. Same-source overlap does not supply the new node's simultaneous shifted-unit representation, canonical adjunction normalization, and edge evaluation. In particular the general internal-Hom theorems supply part of the route to its proof, not its full normalized conclusion.
lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sbc-abelian-higher-image-sheafification-functor-iso: Existing node sheafifies a represented-object derived Hom presheaf for a scheme morphism and one abelian sheaf; the new node treats arbitrary unbounded module complexes on any ringed site and evaluates its edge on the shifted structure unit.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sbc-raw-restricted-resolution-evaluation: Existing node compares a specific bounded-below etale abelian resolution evaluation with restricted sections; it does not identify arbitrary ringed-site hypercohomology with shifted-unit maps.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sbc-raw-restricted-homotopy-sections-iso: Existing node is a homotopy-category formula for the pulled-back free abelian represented sheaf on an etale scheme object; the new node is derived module hypercohomology with structural-ring unit and normalized edge.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sbc-raw-restricted-cohomology-comparison-naturality: Existing node proves naturality of a particular restricted etale cohomology comparison; it does not give the generic shifted-unit representation or its edge value.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sbc-raw-restricted-cohomology-comparison-evaluation-is-iso: Existing node asserts invertibility of an already defined restricted abelian evaluation; it is not the arbitrary ringed-site structural-unit theorem.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sbc-raw-restricted-cohomology-comparison-is-iso: Existing node concerns the c_{h,p,F,U} comparison for etale schemes and a single abelian sheaf, without the generic module-derived edge evaluation.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sbc-raw-restricted-cohomology-natural-iso: Existing node gives natural isomorphisms for raw scheme-etale abelian cohomology; the new node includes arbitrary structural rings, unbounded complexes and canonical shifted-unit/edge normalization.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sbc-abelian-higher-image-evaluation-functor-iso: Existing node evaluates a free represented abelian sheaf on an etale scheme fibre product; this is not O in degree n on an arbitrary ringed site.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-sbc-raw-restricted-cohomology-comparison-map: Existing node defines a restricted etale comparison from a free-generator class; the new node asserts and normalizes the generic module-derived bijection.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sbc-raw-restricted-sections-unit-zero: Existing node normalizes a restricted etale abelian derived-section unit in degree zero; it neither represents arbitrary unbounded module hypercohomology nor evaluates its cohomology-sheaf edge.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-coef-scalar-hom-zero-compatibility: Existing node concerns the scalar internal-Hom comparison for R to S; the new node needs neither a scalar-change pair nor internal Hom and instead evaluates classes from the shifted structural unit.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-weil-boundary-evaluation-currying: Existing node concerns exceptional adjunctions, duality and a pairing identity for a closed immersion; it does not assert the generic shifted structural-unit bijection.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-coef-hom-zero-cycle-class: Existing definition fixes a global derived-Hom zero-cycle normalization; it asserts no existence of the new structural-unit bijection or its cohomology-sheaf edge formula.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-coef-etale-hom-transpose-exact: Existing node gives exactness and signed shifts of a specified internal-Hom scalar transpose; the new node is a global hypercohomology representation and edge evaluation.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pc-derived-tensor-hom-sections-unit: Existing node is restricted to schemes and degree-zero hypercohomology with a supplied tensor-Hom bijection, and gives no normalization by the sections adjunction or cohomology-sheaf edge.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pc-derived-pullback-evaluation-sections: Existing node concerns pointwise internal-Hom pullback on schemes with supplied monoidal/tensor-Hom data; it does not give the arbitrary-site shifted structural-unit edge evaluation.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-derived-internal-hom-shift-right: Existing node shifts the right argument of internal derived Hom; the new node computes a global hypercohomology class as a map and its sheaf edge, not merely a shift iso.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sc-global-hom-shifted-hypercohomology: Existing node compares two shifted global internal-Hom cohomology groups on a scheme; it gives no shifted structural-unit map, sections-adjunction normalization or edge evaluation.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sc-restricted-global-hom-shifted-equiv: Existing node identifies scheme global internal-Hom cohomology with shifted Hom groups; it lacks arbitrary ringed sites and the required structural-unit edge normalization.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-derived-internal-hom-shift-left: Existing node shifts the left argument of internal Hom; it does not normalize global hypercohomology by maps from the shifted structure sheaf.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-hom-complex-resolution-shift-comparison: Existing node compares shifts of a fixed K-injective replacement inside Hom complexes; it is not a structural-unit hypercohomology/edge theorem.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-derived-internal-hom-shift-comparison: Existing node is a derived internal-Hom shift isomorphism before global sections; the new node is the representative-normalized shifted-unit global bijection and edge.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sfb-derived-internal-hom-sections-model: Existing node gives global sections of a right adjoint to tensor as a Hom complex and identifies its cohomology with shifted Hom. It does not identify ordinary hypercohomology of K with maps from O_n normalized simultaneously by the canonical sections adjunction and the sheaf quotient edge.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-sfb-ringed-site-global-hom-identification: Existing definition specifies a normalization predicate for internal-Hom cohomology and explicitly asserts no existence; the new node is an existence and evaluation theorem for the shifted structure unit.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sfb-ringed-global-hom-cup-comparison: Existing node describes the cup/evaluation comparison on global internal Hom and its action on derived maps; it does not supply the cocycle-to-cohomology-sheaf edge formula or its shifted-unit normalization.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sfb-ringed-hypercohomology-edge-tensor: Existing node proves multiplicativity of an edge for two hypercohomology classes. It supplies no shifted-unit representation normalized by the sections adjunction; the new node has no cup-product compatibility assertion.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-sfb-space-affine-hom-comparison: Existing definition fixes algebraic-space affine global Hom pullback and its comparators, not a generic-site shifted-unit hypercohomology/edge theorem.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-sfb-space-affine-global-hom-cohomology: Existing definition fixes all-degree internal-Hom cohomology on algebraic spaces over an affine base. It neither covers arbitrary ringed sites nor asserts the sheaf-edge evaluation of ordinary hypercohomology.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sfb-module-object-ringed-site-derived-comparison: Existing node compares module-object and ringed-site encodings for a scheme with pulled-back condensed coefficients; the new node fixes one ordinary module-sheaf category and represents hypercohomology on any ringed site.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sfb-component-slice-hom-comparison-test: Existing node concerns component-topos slice pullback and its action on internal Hom for w-contractible affine schemes, not arbitrary ringed-site structural-unit edge evaluation.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sfb-ringed-hypercohomology-edge-pullback: The item concerns an arbitrary morphism g and t and the nonflat pullback-edge identity. The new node concerns a single site and no g,t,r or pullback square; steps 2-4 of the item still prove the entire pullback comparison.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-sfb-space-affine-global-sections: Existing definition constructs scalar sections, tensor comparison and cup for algebraic spaces over an affine scheme; it does not assert the generic shifted-unit bijection and edge formula.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-sfb-ringed-site-nonpositive-derived-hom: Existing node truncates a nonpositive source against a degree-zero target; the new node permits arbitrary unbounded targets and all integer degrees and identifies hypercohomology, not this truncation Hom set.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-sfb-space-affine-sections-compositors: Existing definition fixes affine-space section compositors and an affine structure-sheaf insertion; it has no generic-site shifted-unit/edge statement.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-per-ordinary-kummer-first-chern: Existing definition constructs a Kummer Chern class on scheme etale sites; it does not assert the arbitrary-site representation and edge theorem.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-weil-pbc-adic-global-derived-hom: Existing definition constructs adic global derived Hom on a scheme pro-etale site; the new node is an all-ringed-site theorem about ordinary hypercohomology and its edge.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-weil-pbc-proetale-internal-hom-lower-bound: Existing node proves a t-structure lower bound for internal Hom on scheme pro-etale sites; it does not compute global hypercohomology as shifted-unit maps.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-weil-pbc-derived-hom-sheaf-comparison-lisse: Existing node is an etale/pro-etale local-Hom comparison for bounded lisse source and bounded-below target, not the arbitrary ringed-site structural-unit normalization.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-external-rhom-signed-cones: Existing node transports coefficient-cone triangles for a supplied signed external-Hom interface; it is unrelated to a single-site structural-unit edge evaluation.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-pur-external-rhom-pairing-interface: Existing definition specifies an external RHom pairing interface over schemes and constant coefficients, not an existence theorem for arbitrary structural-ring shifted-unit hypercohomology.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-external-rhom-derived-braiding: Existing node proves compatibility of derived braiding and K-flat models, not the shifted-unit representation or global-to-sheaf edge.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-derived-local-class-edge-comparison: Existing node gives edge naturality and exact inverse-image comparison for bounded-below constant finite coefficients on scheme etale/pro-etale sites; the new node is an arbitrary-ringed-site shifted-unit representation with normalized sections adjunction and no topology-comparison assertion.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-global-hom-evaluation-model: Existing node gives a tensor-Hom evaluation model on schemes for bounded flat source complexes; it lacks arbitrary structural-ring sites and the cohomology-sheaf edge formula for ordinary hypercohomology.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-pur-ringed-site-zeroth-hypercohomology: Existing definition defines zeroth hypercohomology on a K-injective. It does not prove its representation by the shifted unit or the canonical adjunction/edge normalization.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-hom-kflat-into-kinjective: Existing node states K-injectivity of a sheaf Hom complex from a K-flat source; it does not identify hypercohomology classes with maps or evaluate their edges.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-hom-complex-global-homotopy: Existing node identifies ordinary H^0 of a global Hom complex with homotopy maps for arbitrary complexes; it does not pass to derived hypercohomology with canonical sections-adjunction and edge normalization.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-rhom-global-sections: Existing node is the H^0 global internal-Hom/derived-Hom identification. It lacks the normalized sections adjunction and cocycle-to-sheaf edge statement, which cannot be read out of its statement by merely specializing L.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-pur-hom-complex-hypercohomology: Existing node identifies derived sections of an explicit Hom complex into a K-injective with homotopy maps; it does not normalize ordinary hypercohomology by the global-sections adjunction or compute the structural-unit edge.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-weil-pbc-strict-local-neighbourhood-geometry: Existing node constructs strict-local-neighbourhood geometry for qcqs schemes; it makes no hypercohomology representation assertion.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-weil-pbc-strict-local-cohomology-source-colimit: Existing node proves a strict-local cohomology colimit for bounded-below abelian sheaves; the new node has no limit or strict-local hypothesis and computes module hypercohomology by shifted O.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-weil-pbc-strict-local-mate-projection-data: Existing definition packages strict-local mate projection comparisons, not a generic ringed-site shifted-unit theorem.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-weil-pbc-strict-local-neighbourhood-geometry: Existing definition constructs the scheme strict-local limiting cone; it has no derived hypercohomology content.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-weil-pbc-strict-local-mate-projection-formulas: Existing node provides strict-local neighbourhood mate projection formulas for bounded-below abelian sheaves; it does not assert the arbitrary structural-ring shifted-unit/edge normalization.

lem-sfb-ringed-hypercohomology-shifted-unit vs lem-weil-pbc-derived-cohomology-germ-isomorphism: Existing node proves that a bounded-below etale abelian derived-Hom germ map is an isomorphism on geometric stalks; it does not provide the arbitrary ringed-site structural-unit bijection.

lem-sfb-ringed-hypercohomology-shifted-unit vs def-weil-pbc-canonical-derived-cohomology-germs: Existing definition fixes a scheme-etale abelian represented-object cohomology germ map; it gives neither the generic module structural-unit bijection nor its sections-adjunction normalization.

