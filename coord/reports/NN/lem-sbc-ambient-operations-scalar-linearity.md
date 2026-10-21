# Stage-1 delivery: lem-sbc-ambient-operations-scalar-linearity

## Files written

- dag/nodes/sec-smooth-base-change/lem-sbc-ambient-operations-scalar-linearity.json: unchanged statement; three-step assembly.
- dag/nodes/sec-smooth-base-change/lem-sbc-underived-ringed-operations-linear.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-smooth-base-change/lem-sbc-linear-right-adjoint.json: statement, unsplit; project scalar clause and Mathlib additive clause already available.
- citations.json: verbatim statement excerpts for every dependency of every assembly step.

## Attachments

CategoryTheory.Adjunction.right_adjoint_linear belongs to lem-sbc-linear-right-adjoint (lean/WeilConjectures/Mathlib/CategoryTheory/Linear/LinearFunctor.lean:34).
CategoryTheory.Adjunction.right_adjoint_additive belongs to lem-sbc-linear-right-adjoint (Mathlib/CategoryTheory/Adjunction/Additive.lean:38).
The scalar lemma assumes only Semiring A, so it specializes to the commutative ring in the new statement without additional hypotheses. The additive lemma assumes only preadditive categories. These two declarations jointly cover the new node, and the metadata records the binding for the normal attachment audit. No proof was invented to replace them. The live item is already proved by AlgebraicGeometry.Scheme.proEtaleRingDerivedOperations_scalarLinearity (lean/Sheaf/AlgebraicGeometry/ProEtaleAmbientOperationsScalarLinearity.lean:77). I read its complete body: it has no sorry and states the exact arbitrary identified-ring-sheaf theorem, including the sectionwise scalar-structure conjuncts. The current node records the J3 stage-3 landing with sorry_after []. I preserve that reviewed_proof record. The explicit human instruction of 2026-10-21 at the end of the repair brief overrides the usual finished-node attachment rule for this deliberate re-split. Thus the delivery extracts named natural-language interfaces without changing or invalidating the existing Lean proof. The underived argument is an unnamed have block there, not an independently named declaration matching the new node; I do not falsely record it as a separate attachment.

## WANTED

None. Sources are present locally.

## What changed and why

This is the deliberate 2026-10-21 re-split, not a stale assignment. The previous reviewed statement is byte-for-byte unchanged. The old four arguments have been redistributed: old steps 1-2 belong to the new underived lemma; old step 3 uses the already existing exact-linear-derived Mathlib leaf; old step 4 is the generic right-adjoint theorem, already proved by the project extension and Mathlib. Both new nodes carry only statements, no proof, no proof dependencies and null proof_origin. One names the underived argument currently local to the completed theorem; the other records reusable completed arguments. Neither is evidence that the completed theorem has an open proof. The assembly has 1252 characters. No new statement restates a derived-operations clause of the item.

The exact originals below preserve every argument rather than abbreviating or blurring them. Their placement in the report, rather than new nodes' proof fields, keeps the new nodes statement-only as instructed.

## Original arguments and their destinations

### Former step 1

Write $P=u^*$ and $G=u_*$ for the underived module functors of [def-weil-pbc-proetale-operations]. For an object $W$ of the site of $V$, put $W_U=U\times_V W$. The scalar $a\in A$ acts on $(GM)(W)=M(W_U)$ through the image of $a$ under $A\to R_V(W)\to R_U(W_U)$. The $A$-compatibility of $c$ identifies this image with the restriction to $W_U$ of the specified global section of $R_U$. Thus, for parallel module-sheaf maps $h,k:M\to N$, the equalities $G(h+k)_W=h_{W_U}+k_{W_U}$ and $G(ah)_W=a h_{W_U}$ hold sectionwise. They commute with restrictions, giving equalities of sheaf maps. In each module-sheaf category the sum and scalar action on Hom are sectionwise; the module laws and bilinearity of composition are checked on sections. These are the $A$-linear category structures of [def-weil-linear-category]. Consequently $G$ is additive and $A$-linear.

Destination: lem-sbc-underived-ringed-operations-linear.

### Former step 2

Use the underived module adjunction $P\dashv G$ of [def-weil-pbc-proetale-operations], with unit $\eta$. For fixed module sheaves $M,N$ on $V$, its bijection $\Phi:\operatorname{Hom}(PM,PN)\to\operatorname{Hom}(M,GPN)$ is $h\mapsto G(h)\circ\eta_M$. Step 1 and bilinearity of composition [def-weil-linear-category] show directly that $\Phi(h+k)=\Phi(h)+\Phi(k)$ and $\Phi(ah)=a\Phi(h)$. Naturality of $\eta$ gives $\Phi(Ps)=\eta_N\circ s$ for each $s:M\to N$. Therefore $\Phi(P(s+t))=\eta_N\circ(s+t)=\Phi(Ps+Pt)$ and $\Phi(P(as))=\eta_N\circ(as)=\Phi(aPs)$. Injectivity of $\Phi$ proves that $P$ is additive and $A$-linear. This uses only the given ordinary adjunction, without presupposing that its Hom bijection is linear.

Destination: lem-sbc-underived-ringed-operations-linear.

### Former step 3

The identified-coefficient construction [def-weil-pbc-proetale-operations] makes $P$ exact and defines $L_u=Lu^*$ by applying $P$ termwise and passing to the ordinary unbounded derived categories. In particular $P$ is additive and preserves finite limits and finite colimits; the coefficient isomorphism, rather than any flatness hypothesis on $u$ as a scheme morphism, is what supplies exactness here. The source and target have precisely the induced $A$-linear derived structures of [lem-weil-linear-abelian-derived-category]. Apply [lem-cbc-exact-linear-derived-functor] with $R=A$, $\mathcal A=\operatorname{Mod}(R_V)$, $\mathcal B=\operatorname{Mod}(R_U)$ and $F=P$, using step 2 for linearity. It gives $L_u(s+t)=L_u(s)+L_u(t)$ and $L_u(as)=aL_u(s)$ on all derived morphisms.

Destination: lem-cbc-exact-linear-derived-functor (existing Mathlib leaf).

### Former step 4

Finally use the ordinary unbounded derived adjunction $L_u\dashv D_u$ stated in [def-weil-pbc-proetale-operations], and let $\epsilon:L_uD_u\to\mathrm{id}$ be its counit. For fixed $X,Y\in D(R_U)$ its bijection $\Psi:\operatorname{Hom}(D_uX,D_uY)\to\operatorname{Hom}(L_uD_uX,Y)$ sends $h$ to $\epsilon_Y\circ L_u(h)$. By step 3 and bilinear composition [def-weil-linear-category], $\Psi$ preserves addition and $A$-scalars. Counit naturality gives $\Psi(D_u(s))=s\circ\epsilon_X$ for $s:X\to Y$. Consequently $\Psi(D_u(s+t))=(s+t)\circ\epsilon_X=\Psi(D_u(s)+D_u(t))$ and $\Psi(D_u(as))=(as)\circ\epsilon_X=\Psi(aD_u(s))$. Injectivity proves both required identities for $D_u$. Together with step 3 these are exactly additive $A$-linearity [def-weil-linear-functor]. Every Hom and adjunction used is in the ordinary unbounded categories; no boundedness, completeness or constructibility has been introduced.

Destination: lem-sbc-linear-right-adjoint.

## Review by NN

I read the small-sites chapter and sk-rem-rest unit records, SETUP's three levels, GOAL.md, the stage-1 worker contract, and delivery-errors B-E in both recorded versions. The current blueprint ancestor is in main-20261015/sec-smooth-base-change/sk-thm-sbc-coefficients: I read its statement and its separate proof, specifically the central-localization sentence. This split provides its scalar-linearity prerequisite and does not alter the chapter or unit route.

For the item and underived node I read sites-modules.tex lemma-adjoint-push-pull-modules (Tag 03D3), including the unit formula and the restriction of the ordinary adjunction to module maps; definition-pushforward (Tag 03D6), clause (1); and section-internal-hom (Tag 04TT), the definition of multiplying a morphism by a ring section. I checked the tags against tags/tags. The global Hom action is already stated by def-pur-sheaf-modules-hom-module, so I cite it rather than create another Hom-module node. Restrict that action along a_T to obtain exactly (a h)_W(x)=a_T(a)|_W h_W(x); its bilinearity is inherited. The compatibility of rho with the A-actions is essential and explicit, including all site objects, so this uses no constancy assumption. Old step 1's section computation then gives G linear. Old step 2's unit bijection is linear because G already is; naturality and injectivity imply P linear. The new underived statement includes these conclusions and all their hypotheses, and is strictly below the derived theorem. It is not a definition-only proof of the item.

For the generic right-adjoint node I read dga.tex definition-functor-linear-categories (Tag 09MK), the complete project file WeilConjectures/Mathlib/CategoryTheory/Linear/LinearFunctor.lean (in particular lines 27-36), and Mathlib CategoryTheory/Adjunction/Additive.lean lines 29-43. The generic project lemma right_adjoint_linear and Mathlib's right_adjoint_additive have exactly the required ordinary adjunction and preadditive/linear hypotheses; neither assumes enriched Hom bijections, abelian categories, exactness or boundedness. I read their complete short proof bodies. Their proofs use adjunction injectivity and counit naturality, as in former step 4. The dual project left_adjoint_linear at line 39 also confirms the underived unit argument; it does not supply the scalar-compatible sheaf structures required by the underived node, so it is not an attachment for that node. No compiler or Lake was run.

Assembly step 1 cites the new underived statement, which says both functors preserve addition and A-scalars and supplies the exact sectionwise structures. Its rho compatibility follows from the item's A-compatible c, with rho the adjunct already specified in def-weil-pbc-proetale-operations. Assembly step 2 uses that definition's explicit exactness and termwise definition of Lu*, the statement of lem-weil-linear-abelian-derived-category for the induced derived structures, and the statement of lem-cbc-exact-linear-derived-functor for both identities on all derived morphisms. I opened all three nodes and read their statements in full. I read Mathlib Algebra/Homology/DerivedCategory/ExactFunctor.lean at lines 27-43 and 120-125: it requires additive P preserving finite limits and finite colimits, which the exact P supplies, and existing unbounded derived categories, which are precisely those in the definition node. Assembly step 3 uses only the explicit ordinary unbounded adjunction in def-weil-pbc-proetale-operations, the generic right-adjoint statement, and def-weil-linear-functor's two defining equations. There is no unproved linear choice of K-injective resolutions. All uses have literal excerpts in citations.json. No step exceeds 2000 characters.

I tested u=id, the zero coefficient ring and zero sheaves, a=0 and a=1, and non-injective A-to-global-section maps: all formulas continue to hold and no faithful scalar action is needed. At u=id with nontrivial coefficient isomorphism the compatibility hypothesis identifies the transported scalar actions, so the ordinary pair remains linear. The generic theorem works also for zero categories and needs no finite biproduct assumption: bilinear composition and the ordinary counit suffice. All objects remain in ordinary unbounded categories, with no constructibility or completeness condition added. No statement dispute was found.

Mathlib searches used only msearch.py and were read as returned; the exact queries are recorded from searches.jsonl. Both natural-language phrasings, Loogle patterns and grep searches were tried. Mathlib's additive-adjoint and Hom-additive equivalence hits do not prove general scalar linearity; the project extension supplies that missing clause. Module pushforward/restriction and pullback-adjunction hits do not construct this arbitrary A-action on both module categories. This is why neither new node is labeled a Mathlib leaf. I searched the whole DAG by tag, keywords and declaration names, and blueprint_refs by linear adjoint, scalar linearity, module direct image, 03D3 and related phrases before creation. In particular, the older module-linearity-criterion nodes concern lifting an abelian adjunction to module maps, not linearity over external global scalars. No SGA source is used.

## Not duplicates

lem-sbc-underived-ringed-operations-linear vs def-weil-pbc-ring-restriction-pullback-comparison: the existing definition specifies restriction-of-scalars functors and their ordinary/derived pullback comparison maps for a square of ring-sheaf maps; it does not assert linearity over an external ring mapping to global sections, or establish the sectionwise Hom linear structures. The new statement is the external-scalar linearity theorem for the underived adjoint pair, and uses the existing operations rather than redefining those comparison maps.

lem-sbc-underived-ringed-operations-linear vs def-coefficient-twists-detailed: the existing node is “Coefficient Tate twists”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-pur-cochain-coefficient-arrows: the existing node is “Canonical scalar-association and transition arrows on cochain sheaves”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-pur-sheaf-hom: the existing node is “Sheaf Hom of sheaves of modules on a site”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-pur-sheaf-modules-hom-module: the existing node gives the global-section Hom action on one category, not linearity of the module pullback/direct-image pair; that action is reused explicitly.

lem-sbc-underived-ringed-operations-linear vs def-sbc-raw-module-abelian-hom-map: the existing node is “The explicit scalar-forgetting map of raw derived Hom”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-sbc-raw-module-scalar-pullback-comparison: the existing node is “Canonical scalar forgetting and inverse-image comparison”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-sp-et-proet-coefficient-transport: the existing node is “Fixed presentation transport of the recorded intrinsic reduction comparison”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-sp-reduction-direct-image-comparison: the existing node is “Canonical compact-support coefficient comparison and normalized open coordinates”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-sp-scalar-tensor-comparison-data: the existing node is “Normalized tensor and scalar-extension comparison data”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-weil-pbc-flat-ringed-diagram-adjuncts: the existing node is “Normalized coefficient comparison with adjunct compatibility”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-weil-pbc-flat-ringed-diagram-comparisons: the existing node is “Comparison functors and localization factors for flat coefficient restriction”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-weil-pbc-flat-ringed-diagram-input: the existing node is “Compatible flat coefficient input and its module diagram functors”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-weil-pbc-module-inverse-image-action: the existing node is “Scalar actions on the constructed abelian inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-weil-pbc-proetale-operations: the existing node is “Derived operations on ringed pro-etale topoi”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-weil-pbc-scalar-localization-coefficient-actions: the existing node is “Canonical coefficient actions on scalar-localized derived module sheaves”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs def-weil-pbc-strict-local-module-sections-set-equiv: the existing node is “Canonical module/set equivalence of strict-local terminal sections”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs det-sf-open-closed-pullback-limits: the existing node is “Closed inverse image preserves limits”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs det-sf-open-closed-sequence-ring-sheaf: the existing node is “The open–closed sequence for module sheaves over a sheaf of rings”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-exc-proetale-finite-module-underlying: the existing node is “Unit-normalized abelian comparison for finite-ring module inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-exc-proetale-finite-scalar-unit-comparison: the existing node is “Finite scalar restriction and pro-etale adjunction units”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-exc-proetale-supported-kernel-complex: the existing node is “Finite-ring supported units and kernel complexes”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-fin-normal-clopen-constructible-module: the existing node is “Componentwise finite constant sheaves on a finite clopen union are constructible”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pc-module-inverse-image-adjunction: the existing node is “Inverse image of module sheaves is left adjoint to direct image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pd-ringed-direct-image-pairing-lax: the existing node is “Normalized lax tensor pairing for ringed direct image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pe-finite-scalar-restriction-constructible: the existing node is “Finite scalar restriction preserves constructible complexes and bounds”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-per-potential-coinduction: the existing node is “Internal coinduction along a prime-power coefficient quotient”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pod-finite-projective-tensor-hom: the existing node is “Internal Hom with a finite projective module”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pod-finite-system-pullback-coherence: the existing node is “Coherent composition of finite-coefficient pullback on strict systems”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pur-frobenius-trivialization-pullback: the existing node is “Pullback naturality of the canonical absolute-Frobenius trivialization”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pur-independent-module-adjunction: the existing node is “Module adjunction for an independently sized algebraic inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pur-inverse-image-hom-comparison: the existing node is “The unit-normalized internal-Hom comparison for an isomorphic base change”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pur-isomorphism-inverse-image-tensor-hom: the existing node is “Inverse image along an isomorphism of schemes commutes with tensor products and sheaf Hom”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pur-kummer-additivity: the existing node is “Kummer additivity”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pur-proetale-open-unit-evaluation: the existing node is “Canonical open pro-etale pullback evaluation and its unit”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-pur-sheaf-hom-is-sheaf: the existing node is “The sheaf Hom of sheaves of modules is a sheaf of modules”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sbc-ambient-operations-scalar-linearity: the existing item concerns unbounded derived operations; this node concerns the underived module pair and its sectionwise A-structures.

lem-sbc-underived-ringed-operations-linear vs lem-sbc-raw-module-abelian-hom-comparison: the existing node is “Scalar forgetting for raw derived Hom before restricted cohomology”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sbc-raw-module-free-source-hom-bijective: the existing node is “Explicit underived free-source comparison”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sc-etale-module-set-pullback-comparison: the existing node is “Canonical module-to-set etale inverse-image comparison”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sc-internal-hom-over-naturality: the existing node is “Naturality of internal Hom restriction under pre- and post-composition”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sf-ambient-proper-open-pasting: the existing node is “Normalized proper/open pasting on ambient pro-etale and semilinear-system categories”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sf-cbc-completed-pullback-unit-tower: the existing node is “Completed pullback completion unit is invertible in the strict reduction tower”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sf-ext-sheaf-constructible: the existing node is “Constructible internal Hom with a site-perfect first variable”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sf-hom-finite-projective: the existing node is “Internal Hom with a finite projective module”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sf-proetale-open-closed-sequence: the existing node is “Open-closed short exact sequence on the pro-etale site”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sf-proetale-tensor-composition-unit: the existing node is “The explicit pro-etale tensor pullback comparison preserves composite adjunction units”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sf-semilinear-scalar-ordinary-comparison: the existing node is “Ordinary scalar restriction with section-normalized comparisons”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sfb-internal-hom-dual-tor-amplitude: the existing node is “Finite Tor amplitude of locally constant perfect duals”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sfb-proetale-object-inverse-image-restriction: the existing node is “Pro-étale inverse image along a site object is slice restriction”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sfb-proetale-open-restriction-counit: the existing node is “Open restriction of pro-etale direct image with counit normalization”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sfb-surjective-closed-module-invariance: the existing node is “Surjective closed immersions: module equivalence and finite local models”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sp-invertible-tensor-scalar-extension: the existing node is “Tensor powers and duals of an invertible module after scalar extension”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sp-level-pullback-exact: the existing node is “Exactness of finite-level inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sp-scalar-extension-binary-coherence: the existing node is “Normalized binary scalar-extension comparisons”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sp-scalar-extension-dual-evaluation: the existing node is “Explicit scalar-extension evaluation on internal duals”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sp-scalar-extension-dual-local-iso: the existing node is “Local rank-one scalar extension and dual invertibility”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-sp-scalar-extension-dual-tower-core: the existing node is “Dual comparisons and binary scalar-extension tower squares”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-trf-finite-scheme-derived-germs: the existing node is “Derived germs and pullback units on a finite geometric scheme”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-trf-frobenius-coefficient-dual-restriction: the existing node is “Residue coefficient restriction and the ambient dualizing object”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-trf-geometric-inverse-image-free-module: the existing node is “Inverse image comparison for free module sheaves”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-tw-dual-stalk-frobenius: the existing node is “Dual stalks and contragredient local Frobenius”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-integral-twist-derived-scalar: the existing node is “Twisting commutes with completed derived scalar extension”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-affine-local-acyclic-open-restriction: the existing node is “Affine-local acyclicity is inherited by open restriction”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-comparison-stratified-essential-image: the existing node is “Gluing classicality through a finite stratification”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-derived-module-underlying-comparison: the existing node is “Derived coefficient-forgetting comparisons respect restriction”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-etale-mayer-vietoris-module-exact-segment: the existing node is “Exact Mayer--Vietoris segment for module-sheaf pullbacks”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-etale-mayer-vietoris-module-vanishing: the existing node is “Two-open Mayer--Vietoris vanishing for inverse images of module sheaves”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-etale-module-h0-finite-connected-criterion: the existing node is “Finite-cover connectedness criterion for etale module sections”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-etale-module-inverse-image-transport: the existing node is “Transport of the module lift along a constant-ring comparison”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-etale-module-pullback-forget-naturality: the existing node is “Naturality of etale module pullback under forgetting coefficients”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-etale-module-ring-iso-adjunction: the existing node is “Transport a linearity criterion across a ring-sheaf isomorphism”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-flat-restriction-derived-mate: the existing node is “FlatRestrictionDerivedMate”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-flat-restriction-ordinary-comparisons: the existing node is “FlatRestrictionOrdinaryComparisons”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-flat-ringed-diagram-restriction: the existing node is “Flat coefficient restriction and normalized derived operations on module diagrams”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-geometric-module-transport: the existing node is “Restriction of the underlying adjunction to linear maps”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-inverse-image-module-adjunction: the existing node is “Inverse image of modules is left adjoint to direct image (etale sites)”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-inverse-image-module-counit-linear-lift: the existing node is “The transported abelian counit lifts to a module map”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-inverse-image-module-linear-criterion: the existing node is “Linearity is preserved and reflected by the etale abelian adjunction”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-inverse-image-module-unit-linear-lift: the existing node is “The transported abelian unit lifts to a module map”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-localization-inverse-image-coherence: the existing node is “Coherent localization comparison for exact inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-module-abelian-inverse-image-comparison: the existing node is “Canonical module-to-abelian inverse-image comparison is invertible”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-module-abelian-underived-exchange: the existing node is “Coefficient forgetting respects underived exchange”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-module-inverse-image-action-adjunction: the existing node is “Underlying inverse image for modules from a normalized ring presentation”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-module-inverse-image-action-of-presentations: the existing node is “Constructing an inverse-image module action from two unit presentations”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-module-inverse-image-unit-comparison: the existing node is “Underlying module inverse-image comparison compatible with the unit”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-module-pullback-section-comparison: the existing node is “Underlying sets of module pullback section comparisons”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-noetherian-stratum-detection: the existing node is “Finite stratified restrictions detect pro-etale sheaves”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-proetale-constant-module-pullback-encoding: the existing node is “Restriction to constant scalars commutes with canonical pullback”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-proetale-immersion-limit-preservation: the existing node is “Inverse images along immersions preserve pro-etale limits”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-proetale-model-ring-presentation: the existing node is “The transported pro-etale ring unit presents set inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-proetale-module-inverse-image-comparison: the existing node is “Underlying sheaves and scalar graph of pro-etale module inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-proetale-module-inverse-image-scalar-graph: the existing node is “Scalar graph compatibility of pro-etale module inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-proetale-module-inverse-image-underlying: the existing node is “Underlying abelian sheaf of the pro-etale module inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-proetale-module-specialization-unit: the existing node is “Module unit on an affine weakly contractible closed specialization neighbourhood”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-proetale-ringed-closed-counit: the existing node is “Closed ringed counit is invertible”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-proetale-ringed-open-comparison: the existing node is “Arbitrary-coefficient open localization”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-ringed-topoi-module-adjunction: the existing node is “Module pullback and pushforward adjunction on arbitrary ringed topoi”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-strict-local-module-restriction-bijective: the existing node is “Bijectivity of an existing linear strict-local comparison”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-strict-local-module-sections-set-transport: the existing node is “Representative compatibility of strict-local coefficient and symmetry transport”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-strict-tower-exchange-mate-normalization: the existing node is “Strict tower exchange agrees with the canonical mate”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lem-weil-pbc-underived-exchange-module-linear: the existing node is “The underived exchange morphism is linear on sheaves of modules”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs lemma-weil-pbc-etale-pullback-forget-modules: the existing node is “Étale pullback commutes with forgetting constant-ring module coefficients”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs new-lem-weil-pbc-proetale-module-canonical-unit: the existing node is “Canonical adjunction unit comparison for module inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs new-lem-weil-pbc-proetale-module-inverse-image-unit-comparison: the existing node is “Canonical unit comparison for module inverse image”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs new-strict-henselian-stalk-sections-comparison-functor: the existing node is “Same-universe abelian etale inverse-image adjunction”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs prop-weil-pbc-inverse-image-modules-exact: the existing node is “Inverse image of etale sheaves of modules over a constant ring is exact”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-underived-ringed-operations-linear vs prop-weil-pbc-proetale-constant-exact: the existing node is “Exactness of the pro-etale inverse image for constant coefficients”; it does not assert additive A-linearity of both underived pro-etale module operations for arbitrary compatible global-scalar maps.

lem-sbc-linear-right-adjoint vs def-weil-linear-functor: the existing node is “R-linear functor”; it does not assert additivity and A-linearity of an arbitrary right adjoint to an additive A-linear functor.

lem-sbc-linear-right-adjoint vs def-weil-linear-scalar-localization: the existing node is “Scalar localization of a linear category at one element”; it does not assert additivity and A-linearity of an arbitrary right adjoint to an additive A-linear functor.

lem-sbc-linear-right-adjoint vs lem-pur-compatible-coefficient-tower: the existing node is “Compatible coefficient maps give a linear strict tensor tower”; it does not assert additivity and A-linearity of an arbitrary right adjoint to an additive A-linear functor.

lem-sbc-linear-right-adjoint vs lem-sbc-ambient-operations-scalar-linearity: the existing item concerns unbounded derived operations; this node concerns a generic ordinary adjunction between any A-linear categories.

lem-sbc-linear-right-adjoint vs lem-sbc-completed-operations-linear-natural-exchange: the existing node is “Linearity and naturality of completed pullback, direct image, and exchange”; it does not assert additivity and A-linearity of an arbitrary right adjoint to an additive A-linear functor.

lem-sbc-underived-ringed-operations-linear vs lem-zl-module-terminal-scalar-comparison: the existing node compares free/evaluation left adjoints under specified evaluation isomorphisms; it does not construct compatible global-scalar Hom actions or prove the underived pullback/direct-image pair linear.

lem-sbc-underived-ringed-operations-linear vs lem-sp-signed-tate-coefficient-exponent-normalization: the existing node normalizes finite coefficient changes on signed Tate lines and their exponent transition maps; it does not state scalar linearity of operations on arbitrary module sheaves.

lem-sbc-linear-right-adjoint vs lem-pur-ringed-derived-pushforward-linear: the existing node treats the specific unbounded derived direct image of a ringed-topos morphism with compatible central scalars; the new node is the ordinary-adjunction theorem for arbitrary preadditive linear categories and assumes a linear left adjoint. Neither statement specializes to the other without the additional module/derived constructions.

## Unfinished work

No unaccounted argument remains in the item. A separately exported underived interface remains to be stated and bound to a named declaration; its argument already occurs inside the proved item. The right-adjoint node has the two recorded existing declarations for the maintainer to attach. Independent maintainer review remains part of the normal delivery process.

## Dry-run repairs

The first citation check required two excerpts to be at least 40 characters. I expanded the excerpts to the full relevant right-adjoint conclusion and derived-adjunction paragraph, and also expanded the exactness excerpt to include the termwise definition. No mathematical statement or dependency changed.

## Repair of A6/A7/B10/G4 — 2026-10-21, recorded after J3

I accept the returned chronology: the pre-landing repair-note timestamp cannot authorize a change after the J3 landing 20261021T061336-L-1761747. The live item is split, its exact theorem is proved, and sorry_after is empty. The mathematical split was not returned for a mathematical defect. I do not infer authorization from redispatch, from a generic hand-off, from a file mtime, or from an unchanged rebase.

The assigning human message also contains a separate, explicit instruction headed “Why this node is back in stage 1 (the human, 2026-10-21)”. It specifically says: “The node is already split once and stated in Lean; that the live item is already split and reviewed is exactly why it is back: this is a deliberate re-split, not a stale assignment. Deliver it as a stage-1 repair of the existing node with the new statement-only nodes.” This instruction expressly requests the exception that the return says is missing. I have now transcribed that specific instruction, its provenance and the completed landing it acknowledges into split_report.resplit_authorization in the delivered item JSON, recorded at 2026-10-21T10:16:55Z, after the 06:13Z landing. This is an explicit record in the delivery for the maintainer to review, not an assertion that a post-landing decision was already present in coord/HUMAN.md. The worker has no authority to change coord/HUMAN.md or retire the launcher's repair note and has done neither.

A6/A7: the re-split records the exception and acknowledges the completed live state instead of treating it as unsplit. B10: the exact completed item theorem and the two existing generic-adjoint covering declarations remain identified in Attachments and in their retained metadata; no new open proof is alleged for any of them. G4: this delivery records the specific overriding instruction in a structured field that was absent in the returned head, and fixes the extracted underived node's source record to distinguish 03D6 (operations and ring-map action), 03D3 (adjunction), and 04TT (Hom scalars). Step 1 cites the corrected source record. It is not an unchanged re-push, and it makes no claim of repairing mathematics the maintainer already found sound.

The two extracted statements, authentic search results and four full original arguments are retained. In particular, I have not fabricated a new mathematical problem merely to change the node hashes. The generic right-adjoint node still records the existing scalar declaration CategoryTheory.Adjunction.right_adjoint_linear at WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor:34 and the additive declaration CategoryTheory.Adjunction.right_adjoint_additive at Mathlib.CategoryTheory.Adjunction.Additive:38. The maintainer's normal attachment audit determines their transitive completion. The new underived interface remains an unnamed argument within the completed item's proof and has no standalone matching declaration.

## Review by NN — current repair

I read GOAL.md, the chapter and sk-rem-rest unit records, the three blueprint levels in SETUP.md, brief-stage1, stages/1-dag, and delivery-errors B-E. I also read the current ancestor proof in main-20261015/sk-thm-sbc-coefficients/sbc-thm-e-coefficient-smooth-base-change.proof.md: its central-localization sentence requires the scalar-compatible integral operations furnished here. The re-split changes no chapter or unit route. I reran the whole-blueprint searches for linear adjoint and scalar linearity and the ancestor lookup; the hits do not state either new interface. Existing same-tag comparisons remain in Not duplicates.

For the item and underived node, I read Stacks sites-modules.tex Tag 03D3 (lemma-adjoint-push-pull-modules), Tag 03D6 (definition-pushforward), Tag 04TT (section-internal-hom), and Tag 04JC (lemma-flat-pullback-exact), with labels checked in tags/tags. For the generic node I read dga.tex Tag 09MK (definition-functor-linear-categories), the full project right_adjoint_linear/left_adjoint_linear bodies, and Mathlib Adjunction/Additive.lean:29-43. These sources support the stated scalar refinement; no tag is presented as asserting the combined refinement by itself. No SGA route is used.

For step 1, I read the entire underived node statement and its four definition dependencies. Its rho equation is the compatibility hc in the live theorem. The sectionwise Hom action is exactly the action in def-pur-sheaf-modules-hom-module restricted along a_T; it makes composition A-bilinear. Direct-image linearity is sectionwise, while the unit Hom bijection is linear because G already is; naturality followed by injectivity gives P linear. These are precisely former arguments 1-2, preserved verbatim above. The new node carries the full hypotheses, including commutativity, small sites, c and both global scalar maps, with no proof hidden in its statement.

For step 2, I opened the complete statements of def-weil-pbc-proetale-operations, lem-weil-linear-abelian-derived-category and lem-cbc-exact-linear-derived-functor. The first explicitly supplies exact P and its termwise unbounded derived functor; the second supplies the induced scalar structures. Exactness, additivity and step 1's A-linearity give every hypothesis of the third, including finite-limit and finite-colimit preservation. I also read Mathlib ExactFunctor.lean:27-43,120-125 and Linear.lean:24-39. No flatness of the scheme morphism or boundedness is assumed: the ring-sheaf coefficient isomorphism gives the needed exactness.

For step 3, the operations definition explicitly supplies the ordinary unbounded adjunction. The generic node applies to exactly these induced A-linear categories and the additive linear left adjoint from step 2. Its two existing covering declarations require only preadditivity, an ordinary adjunction and left-functor additivity/linearity. Their injective counit-bijection calculation gives both equations without assuming enriched Hom bijections or linear resolution choices. I verified every citations.json entry as a verbatim excerpt of the actual cited statement, not its proof.

Edge cases were checked again: u=id with nontrivial c still needs the stated scalar compatibility; A=0 permits only zero unital coefficient rings and causes no exception; a=0 and a=1 satisfy both equations; non-injective a_T need no cancellation. The generic node allows zero categories and requires no abelian or exact structure. Neither new node changes the coefficient category or imposes constructibility/completeness. The assembly has no step over 2000 characters and is under 3000 total.

I read all retained searches.jsonl results and inspected the relevant Mathlib additive-adjoint, exact-derived, scalar-restriction and linear-derived declarations. The two distinct phrasings and three search kinds are already logged for each new node; their statements and search questions are unchanged, so no search was repeated or invented. Neither new node is a Mathlib leaf: the underived compatible-global-scalar interface is not one Mathlib specialization, while the generic node's scalar clause comes from the project extension. The item itself has its existing honest search record. The initial required dry run in this repair exited 0 with OK (not pushed) at ae0d2ddc127. After recording the specific re-split instruction and correcting the source metadata, I run the full dry run again before pushing. No compiler or build tool was run.
