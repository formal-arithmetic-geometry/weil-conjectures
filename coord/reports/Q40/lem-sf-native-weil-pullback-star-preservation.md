## Files written

Q40, 2026-10-22, stage 1 repair of the released keep_plan re-split order.

- dag/nodes/sec-six-functors/lem-sf-native-weil-pullback-star-preservation.json: unchanged statement and stmt_deps, four-step assembly (2246 characters).
- dag/nodes/sec-six-functors/lem-sf-native-encoding-derived-operations.json: new statement, unsplit, no Mathlib match; native vector-module encoding and actual equivariant derived-operation comparison (2496 characters).
- dag/nodes/sec-six-functors/lem-sf-native-forget-constructible-criterion.json: new statement, unsplit, no Mathlib match; native stratification and derived cohomology/predicate comparison (2487 characters).
- citations.json: one verbatim complete statement for each step/node pair.
- report.md: this report, including the complete returned argument below. previous-report.md is retained as historical Q33 work. Sandbox-only search transcripts, JSON-writing helpers, returned-node.json and the local PDF text extraction are not delivery node files.

## Attachments

None. I read Category.lean:447-480 and LowerStar.lean:79-179. The native pullback supplies only one clause. The full pushforward assertion uses the finiteness theorem whose affine input, SixFunctors/ProEtale/Adic/LowerStar.lean:411-415, is still sorry. The project tag search found no completed declaration covering all clauses. The generic IsoAlgebra derived-forgetting declaration is an input to a new comparison task, not an attachment for its whole native encoding assertion.

## WANTED

None. The blueprint, Bhatt–Scholze PDF, native sources and cited Stacks sources are present.

## Corrections and unfinished work

The sandbox item and current read-clone item were identical before the repair. I read coord/repair-notes/lem-sf-native-weil-pullback-star-preservation.json: stage 1 is explicitly released with keep_plan and the human's re-split order. The initial required dry run exited with the missing report/Review by Q40 diagnostic; it is no longer active. No statement dispute, statement weakening, new source route or change to statement dependencies is involved. The prior nine-step proof was mathematically reviewed, but too large to assign as one task. The repair creates two genuinely separate arguments of comparable size and reuses the existing exact coefficient-ring comparison rather than introducing its duplicate. The remaining unproved work is deliberately assigned to the two new unsplit nodes, as ordered; neither has proof steps or proof dependencies.

## New nodes

lem-sf-native-encoding-derived-operations: native Mod objects live in Omega-vector-space sheaves. The new statement identifies this particular encoding, by explicit action reinterpretation and inverse restriction along constant scalars, with internal abelian coefficient modules. It also compares their actual equivariant ambient derived operations. This is a model/functor comparison for arbitrary complexes; it asserts no bounded-constructible preservation.

lem-sf-native-forget-constructible-criterion: a single-scheme assertion comparing native local stratification, global finite constructibility, cohomology after exact forgetting, boundedness detection, and the coefficient-field finite-Tor predicate. It has no morphism f and asserts no pushforward or pullback preservation. Both new statements introduce the finite field, algebraic closure, prime, schemes, module categories, coefficient ring, equivalence and functors they use. Their definition nodes are in stmt_deps.

## Distribution of the complete returned argument

Old step 1 stays as assembly step 1, with exactly the same base-change, Noetherian and qcqs inputs.
Old step 2 is the already existing lem-sf-locally-finite-coefficient-ring-realization, cited in assembly step 2 and in the new encoding statement. Its statement includes the locally finite function ring, identification on each finite subextension and compatibility with precomposition. I read its proof too: it gives the finite-dimensional-span/basis/compositum argument and an explicit inverse by sheaf gluing. The old affine finite-subcover argument is also retained verbatim below as an alternative descent verification. Creating that argument again would violate the duplicate rule.
Old steps 3 and 4 become the first part of lem-sf-native-encoding-derived-operations; old step 7 becomes its final two natural derived-operation isomorphisms. The report preserves all details below for that worker, including exactness and the K-injective test argument. The generic lem-sf-finite-span-module-derived-comparison, Cartesian coefficient theorem and fixed-pair derived-forget comparison remain available as inputs; they are not themselves copied into new tasks.
Old steps 5 and 6 become lem-sf-native-forget-constructible-criterion, with explicit local/global constructibility, varying finite ranks, every cohomological interval, zero detection and the same [a-1,b] Tor bound. That task can be worked independently by stating its specified E_T interface while the encoding task is open.
Old step 8 stays as assembly step 3, applying precisely the same geometric coefficient stability clauses (1),(3). Old step 9 stays verbatim as assembly step 4. Thus no argument was discarded or replaced by a vague transport sentence. The exact old proof is retained below, with its old node citations and source places, as the workers' starting material.

## Mathlib searches

I read the retained search history in the item; no inherited searches were deleted. Each new node has real msearch.py LeanSearch, Loogle, grep and LeanFinder calls. search-results.json and the corresponding encoding-*.txt and predicate-*.txt files retain complete results; searches.jsonl is the command's unmodified log. Different natural-language phrasings were tried before concluding absence. All these calls answered successfully. Encoding LeanSearch returned sheaf module definitions and section formulas; LeanFinder returned local cohomology and generic condensed/free-forget constructions. Its grep found only AlgCat.algEquivIsoAlgebraIso, an algebra isomorphism rather than an endofunctor fixed-pair comparison; Loogle had zero hits. Predicate LeanSearch returned generic reflects-isomorphisms and limits results, while LeanFinder returned condensed category/Grothendieck constructions. Predicate Loogle and grep had zero hits. None compares native local stratification with coefficient constructibility or proves the entire derived predicate criterion. These are not one-line specializations of a Mathlib result.

## Not duplicates

lem-sf-native-encoding-derived-operations vs lem-sf-finite-span-module-derived-comparison: the existing equivalence starts with internal A_Z-modules in abelian sheaves and sectionwise modules over the function ring, and has no Frobenius fixed-pair category. The new theorem starts with module objects in Omega-vector-space sheaves, supplies the inverse restriction along constant scalars, and compares the actual native equivariant derived functors after forgetting. Its statement does not re-prove the existing coefficient-ring or section-module comparison.
lem-sf-native-encoding-derived-operations vs lem-sf-locally-finite-coefficient-ring-realization: the existing theorem identifies rings and coefficient maps only; the new theorem uses that isomorphism for native vector-module encodings and equivariant derived functors.
lem-sf-native-encoding-derived-operations vs lem-sf-fixed-pair-derived-forget-comparison: that is a generic theorem for already specified Grothendieck abelian categories. It does not give the native vector-module coefficient equivalence or identify the module operations on the other side. The new comparison combines this input with those native identifications.
lem-sf-native-encoding-derived-operations vs lem-pd-module-ringed-topos-derived-comparison: the existing node concerns internal abelian modules and section modules, tensor and canonical mates. It neither starts with the native Omega-vector-module encoding nor gives the two native Frobenius-forgetting comparisons.
lem-sf-native-forget-constructible-criterion vs lem-sf-locally-finite-adic-constructible-realization: the existing theorem is an equivalence from the common finite-field/rationalized coefficient-stage category. The new theorem is a predicate criterion inside the ordinary derived category of native abelian fixed pairs and makes no common-stage realization claim.
lem-sf-native-forget-constructible-criterion vs lem-sf-adic-qbar-constructible-realization: that theorem gives a monoidal common-stage equivalence and internal-Hom comparison; the new one instead compares local stratification and cohomological predicates under native forgetting, not scalar extension from common stages.
lem-sf-native-forget-constructible-criterion vs lem-sf-weil-native-closed-forgetful: the existing statement gives tensor/internal-Hom comparisons and sends the bounded constructible subcategory to underlying modules; it does not assert the equivalence with the blueprint coefficient constructibility and finite-Tor predicate, including reflection of all intervals and local-to-global stratification.
lem-sf-native-forget-constructible-criterion vs sk-lem-coefficient-heart: the existing theorem is for the coefficient-module model and its abelian constructible heart, not native vector-module fixed pairs or local/native stratification and cohomology detection.
lem-sf-native-forget-constructible-criterion vs det-def-localizing-closure-ctf-equals-bc: its Tor bound is reused exactly; the new statement compares native predicates to that coefficient model, not a new Tor theorem.
lem-sf-native-forget-constructible-criterion vs lem-sf-locally-finite-coefficient-ring-realization: a ring identification does not identify local stratification, fixed-pair cohomology or boundedness.
lem-sf-native-encoding-derived-operations vs lem-sf-adic-qbar-constructible-realization: the latter realizes common-stage bounded constructibles with tensor/Hom structure; it does not compare the ambient native Frobenius equivariant f^* and Rf_* for arbitrary complexes.
lem-sf-native-encoding-derived-operations vs lem-sf-locally-finite-adic-constructible-realization: the latter is a finite-stage-to-native equivalence on bounded constructibles, not the native vector-module encoding and ambient equivariant derived operations.

Whole-blueprint searches for native coefficient, locallyFiniteFunctions, native constructibility, native encoding and forget constructible returned no matches. I also searched module objects, locally finite and constructibility, then opened the relevant candidate node statements above. Neither new id occurs already in the DAG or project Lean. The nearest blueprint ancestor is None, as for the returned seed; both breadcrumbs retain that fact, prepend this item to via, and name the exact native obligations serving fix-lem-tensor-adjunction.proof.md Step 1. The chapter and unit are unchanged, and this non-key node does not edit unit realization records.

## Review by Q40

I read delivery-errors.md B–E in full, including the archived copy, against the delivered statements and assembly. The main correction is the requested substantive redistribution rather than prose compression. I retained the entire old proof below because future workers need its basis/compositum, exact-equivalence, stratification and K-injective arguments, not just their summaries.

For the item I read the current direct-image stability proof, clauses (1),(3), and fix-lem-tensor-adjunction.proof.md Step 1. For the first new node I read Adic/Module.lean:50-56, Category.lean:134-198 and 447-480, LowerStar.lean:79-85,116-179 and RightDerivedFunctor/IsoAlgebra.lean:54-97. The code specifies module objects in vector-space sheaves and the transported fixed-pair operations; the generic source explicitly computes right derivation after forgetting on K-injectives. Bhatt–Scholze Definitions 6.8.1 and 6.8.3 provide the underlying coefficient-module presentation, not the claimed native comparison by themselves. I mark the comparison as agent-formulated and preserve its argument below. For the second new node I read Adic/Constructible.lean:84-149, the native framework statement, Bhatt–Scholze Definitions 6.8.3,6.8.6,6.8.8, and the coefficient-heart/Tor statements. The native constructibility is Zariski-local stratified lisseness; the coefficient notion uses a finite stratification. The finite-type/Noetherian assumptions allow the finite refinement, which is explicitly retained in old step 5. The source uses a field coefficient; this is essential to the Dctf=Dbc comparison and is retained.

Assembly step 1 uses exactly the statements of lem-pod-separated-finite-type-base-change (both the morphism and structure maps), lem-weil-pbc-finite-type-over-noetherian (finite type over a Noetherian scheme), and lem-weil-pbc-qcqs-over-affine (separated finite type over a field). I read those statements, and the cited Stacks labels 01KU/01T4/01T6. Characteristic is unchanged by field extension. A field is Noetherian by its two ideals, so there is no extra finiteness hypothesis. Assembly step 2 cites the ring realization's canonical theta and precomposition square, the new encoding node's displayed natural isomorphisms and the new predicate node's displayed equivalence. Each conclusion used appears literally in the cited statement, with their objects and functors introduced there. It does not use a definition node as a finiteness theorem.

Assembly step 3 cites det-thm-sf-ctf-stability-direct-images exactly for clauses (1),(3), and sk-def-sfb-qlbar-condensed to fix the finite-subextension-valued coefficient. I opened those statements. Step 1 verifies separated finite type, positive characteristic different from ell and qcqs, and step 2 supplies the input Dctf membership and both actual-operation comparisons. Output membership therefore includes boundedness, not just constructibility of individual degrees. Applying the reverse implication of the new predicate criterion to those two outputs gives precisely the original conclusions. Step 4 uses only the native framework's literal definitions of restrictions. I read them against Category.lean:472-480 and LowerStar.lean:171-179; the ambient objects and morphisms do not change when the preservation witness changes.

For the intended worker arguments I checked that ringed-site module categories are Grothendieck in a common larger module universe, exactly the hypothesis of lem-weil-pbc-ring-sheaves-grothendieck, and Frobenius pullback is an additive autoequivalence. The fixed-pair comparison therefore applies. The actual direct image is additive left exact and the actual pullback uses the invertible Cartesian coefficient map. The explicit inverse exact encoding preserves K-injectives by its acyclic Hom test; arbitrary exactness alone is not asserted to do this. Forgetting is exact conservative and commutes with cohomology, so zero in each degree is reflected. No equivalence between derived fixed pairs and fixed pairs in a derived category is assumed.

Small cases: zero module, empty scheme and empty finite stratification; rank zero and unequal ranks on different cover members; identity morphism; a single cohomology sheaf in an arbitrary shifted degree. On the empty site the zero category makes every comparison valid; the support equivalence applies to every interval, including a zero object. Rank zero gives the same zero local model. The identity comparisons are those of the same coefficient ring and actions. An arbitrary shift is handled by cohomology in every integer degree, not a bounded-below inference. The non-quasi-compact disjoint union of projective spaces of increasing dimension is outside the finite-type target hypothesis and does not contradict the output bound. Each new statement is smaller than the item: one has no finiteness conclusion, the other has no scheme morphism.

I inspected the existing comparison candidates and their dependency closures for cycles back to this item; none was found. No new node carries proof steps, proof dependencies or a proof sketch in its statement. All mathematical detail from the old proof appears below as report material, rather than being smuggled into new statements. Every assembly step is below 2000 characters and the total is below 3000. proof_deps is the exact union of uses. Every citations.json quote is the complete verbatim cited statement; the new-node quotes are taken from the sandbox version. Existing approved top-level tool_uses are preserved as historical maintainer data; split_report.tool_uses declares the currently used generic ring comparison and geometric/stability tools. No forbidden SGA source is cited, no Lean file is written, no compiler or Lake is run, and all writes remain in the assigned sandbox.

## Validation

The preliminary dry run exited on the missing report diagnostic. The first complete server dry run passed preflight at 439db03650e (not pushed), including the server DAG and split checks. I corrected one report sentence afterward to distinguish the existing ring proof’s explicit gluing inverse from the old proof’s retained affine-cover descent argument. The final dry run checks the exact corrected delivery before pushing. The checks run on the server only.

## Returned proof preserved verbatim

This is historical proof material, distributed as above; it is not a proof field of either new unsplit node.

### Old step 1

Put $k=\overline{k_0}$, $X=X_0\times_{k_0}k$, $Y=Y_0\times_{k_0}k$, and $f=\bar f_0$. By [lem-pod-separated-finite-type-base-change], $X,Y$ and $f$ are separated and of finite type over $k$. Their characteristic is the positive characteristic of $k_0$, different from $\ell$. By [lem-weil-pbc-finite-type-over-noetherian] they are Noetherian: a field is Noetherian since its only ideals are zero and the whole field. By [lem-weil-pbc-qcqs-over-affine] they are qcqs. Thus the geometric schemes meet the standing hypotheses of the coefficient stability theorem, including quasi-compactness of its target.

Cited nodes: lem-pod-separated-finite-type-base-change, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-qcqs-over-affine

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Opening standing hypotheses; Stacks Tags 01KU and 01T4 for base change, 01T6 for Noetherianity.

### Old step 2

Identify the native coefficient ring $B_T$ with $\Omega_T=p_T^*\underline\Omega$, for $T=X,Y$ and their strata. A subset of $\Omega$ spans a finite-dimensional $\mathbf Q_\ell$-space only if it lies in a finite intermediate field: choose a finite basis and take the field generated by its elements, all algebraic over $\mathbf Q_\ell$. The converse follows from $[E:\mathbf Q_\ell]<\infty$. Therefore the native condition on a continuous function is precisely that locally its values lie in one finite $E$. For each such $E$, apply [lem-sfb-totally-disconnected-coefficient-realization] to its Hausdorff ultrametric topology: $E_T$ is the sheaf $U\mapsto C(|U|,E)$, naturally for continuous coefficient maps and finite products. The same lemma for $\Omega$, also Hausdorff and totally disconnected, and for the inclusions $E\subseteq F\subseteq\Omega$ makes every $E_T$ a subsheaf of $U\mapsto C(|U|,\Omega)$, so the filtered union is a subpresheaf of this sheaf and its sheafification is the subsheaf of those $t$ for which some pro-etale covering $\{U_i\to U\}$ has every $t|_{U_i}$ valued in some $E_i$. Such a $t$ meets the native condition: by the covering condition of [def-weil-pbc-proetale-site] each affine open $V\subseteq U$ is the union of the images of finitely many affine opens $V_j\subseteq U_{i_j}$, so $t(V)$ lies in the compositum of the finitely many $E_{i_j}$. Conversely a function meeting the native condition is valued in one $E$ on each member of a Zariski open covering, which is a pro-etale covering. The ring isomorphism $\Omega_T\cong\varinjlim_E E_T$ of [sk-prop-sfb-qlbar-colimit-x] consequently identifies $\Omega_T$ with $B_T$. The identifications respect addition, multiplication and restrictions, since all are pointwise, and respect the coefficient map for $f$, since both maps send a function $t$ to its precomposition with the projection.

Cited nodes: def-sf-native-weil-derived-framework, lem-sfb-totally-disconnected-coefficient-realization, sk-prop-sfb-qlbar-colimit-x, def-weil-pbc-proetale-site

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Lemma 4.2.12 and Lemma 6.8.2; native ConstantSheaf.lean locallyFiniteFunctions.

### Old step 3

Make the abelian encoding identification explicit. A native $B_T$-module object in sheaves of $\Omega$-vector spaces gives a sheaf of $B_T$-modules by the same action on sections. Conversely a sheaf of $B_T$-modules acquires its $\Omega$-linear sheaf structure by restriction along constant functions $\Omega\to B_T$; its $B_T$-action is then $\Omega$-bilinear. These constructions are inverse on objects and on morphisms, since a $B_T$-linear map already commutes with constant scalars. Using Step 2, they identify $\mathcal A_T$ with ordinary $\Omega_T$-module sheaves. Kernels and sheafified cokernels have the same underlying abelian sheaves, so this is an exact equivalence. Applying the inverse constructions degreewise identifies complexes, homotopies and quasi-isomorphisms, hence their ordinary derived categories. This is a comparison of underlying coefficient-module encodings, with no replacement of $D(\mathcal W_T)$ by fixed pairs in a derived category.

Cited nodes: def-sf-native-weil-derived-framework, def-weil-sheaf-of-modules-category

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Definitions 6.8.1 and 6.8.3; expansion of the native module-object definition.

### Old step 4

These identifications use the actual ordinary operations. On section-module sheaves the pullback is $\Omega_X\otimes_{f^{-1}\Omega_Y}f^{-1}(-)$ and direct image is ordinary sheaf direct image with the coefficient action induced by precomposition. These are exactly the native formulas after Step 2. The comparison [lem-pd-module-ringed-topos-derived-comparison] identifies these ringed-module operations with the internal abelian-module operations, also after total derivation. Its hypotheses hold on the geometric schemes of Step 1. The coefficient map $f^{-1}\Omega_Y\to\Omega_X$ is invertible by [sk-prop-sfb-cartesian-coefficients], so pullback is exact and its left-derived functor is termwise pullback. The exact equivalence of Step 3 also preserves K-injectives: its inverse takes acyclic complexes to acyclic complexes, and the equivalence identifies their complexes of maps. Thus the same K-injective resolution computes the two encodings of $Rf_*$. No completed or compactly supported direct image is substituted here.

Cited nodes: lem-pd-module-ringed-topos-derived-comparison, sk-prop-sfb-cartesian-coefficients

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Clauses (1) and (3), ordinary module operations; the explicit ringed/internal comparison.

### Old step 5

The constructibility predicates also agree. On a qcqs $T$, the native Zariski-local finite stratifications give a global finite stratification: choose finitely many open neighbourhoods $V_i$ with such stratifications, replace $V_i$ by the disjoint locally closed pieces $V_i\setminus\bigcup_{j<i}V_j$, and intersect each piece with its original strata. The resulting finite locally closed constructible strata partition $T$ and retain the given trivializations. The reverse implication is restriction. By [sk-lem-coefficient-heart], for $\Lambda=\Omega$ constructibility in the coefficient model is exactly pro-etale local finite freeness on these strata, so it is the native predicate. Equivalently each finite constant local model is $\Omega_U\otimes_\Omega P\cong\Omega_U^{\oplus r}$ after choosing a basis of the finite-dimensional scalar vector space $P$; the ranks may vary with $U$. Consequently Step 3 identifies bounded native underlying complexes with $D^b_c(T,\Omega)$. By [det-def-localizing-closure-ctf-equals-bc](2) these are in $D_{ctf}(T,\Omega)$; explicitly a cohomological interval $[a,b]$ gives finite Tor amplitude contained in $[a-1,b]$. This applies on the qcqs schemes of Step 1.

Cited nodes: def-sf-native-weil-derived-framework, sk-lem-coefficient-heart, det-def-localizing-closure-ctf-equals-bc

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf — Definitions 6.8.3, 6.8.6, 6.8.8; blueprint field-coefficient heart and Tor comparison.

### Old step 6

Let $U_T:\mathcal W_T\to\mathcal A_T$ forget the native Frobenius structure. The small ringed-site module categories are Grothendieck abelian by [lem-weil-pbc-ring-sheaves-grothendieck], using one coefficient universe containing a small model of each site. Frobenius is an automorphism and its pullback is an additive autoequivalence by the native framework. Apply [lem-sf-fixed-pair-derived-forget-comparison]. Then $U_T$ is exact and conservative and preserves K-injectives. For any complex $C$, exactness gives $H^n(U_TC)=U_TH^n(C)$ by preserving kernels and cokernels. Moreover $U_TM=0$ implies $M=0$: the underlying zero object has a unique Frobenius structure and unique morphisms. Therefore $D(U_T)$ preserves and reflects every cohomological vanishing condition, hence boundedness. With the predicate identification in Step 5 this proves
$$C\in\mathrm{WC}^{\mathrm{der}}(T_0)\quad\Longleftrightarrow\quad D(U_T)C\in D^b_c(T,\Omega)=D_{ctf}(T,\Omega).$$

Cited nodes: def-sf-native-weil-derived-framework, lem-weil-pbc-ring-sheaves-grothendieck, lem-sf-fixed-pair-derived-forget-comparison

Source: lean/WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/IsoAlgebra.lean — preservesKInjectiveComplexes_forget and rightDerivedFunctorMapOfNatIsoCompForgetIso, lines 62-97.

### Old step 7

For native pullback, forgetting its transported Frobenius structure leaves exactly the underlying $f^*$ in every degree. This is the lift formula in [def-sf-native-weil-derived-framework]; both differentials and morphisms are sent by the same functor. Hence
$$D(U_X)f^*\cong f^*D(U_Y).$$
For ordinary direct image use [lem-sf-fixed-pair-derived-forget-comparison] with $L=f_*$. It is additive and left exact, and the natural isomorphism $F_Y^*f_*\cong f_*F_X^*$ is the one used in the native lift. The lemma gives
$$D(U_Y)Rf_*\cong Rf_*D(U_X).$$
In both formulas the right-hand operations are the ordinary coefficient-module operations identified in Step 4. The second formula follows from forgetting a native K-injective resolution, not from an asserted equivalence between derived fixed pairs and fixed pairs of derived objects.

Cited nodes: def-sf-native-weil-derived-framework, lem-sf-fixed-pair-derived-forget-comparison

Source: lean/WeilConjectures/WeilSheaf/LowerStar.lean — ProEtaleWeilSheaf.lowerStar and singleFunctor comparison, lines 79-85 and 116-142; Category.lean lines 447-479 for pullback.

### Old step 8

Now apply [det-thm-sf-ctf-stability-direct-images](1),(3) with the admissible coefficient $\Lambda=\Omega$, specifically the finite-subextension-valued condensed algebraic closure of [sk-def-sfb-qlbar-condensed]. This is one of the enumerated coefficients, and the schemes and morphism meet its separated finite-type hypotheses by Step 1. Given the original $L$ and $K$, Step 6 places $D(U_Y)L$ and $D(U_X)K$ in $D_{ctf}$. The cited clauses yield
$$f^*D(U_Y)L\in D_{ctf}(X,\Omega),\qquad Rf_*D(U_X)K\in D_{ctf}(Y,\Omega).$$
Use the actual-operation comparisons of Step 7 and the equivalence of predicates in Step 6 to conclude $f^*L\in\mathrm{WC}^{\mathrm{der}}(X_0)$ and $Rf_*K\in\mathrm{WC}^{\mathrm{der}}(Y_0)$. In particular forgetting reflects the finite cohomological support; the argument proves boundedness, not just constructibility in each degree.

Cited nodes: det-thm-sf-ctf-stability-direct-images, sk-def-sfb-qlbar-condensed

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md — Clauses (1) and (3); field coefficient case of the standing stability theorem.

### Old step 9

Restrict the two ambient functors along the full-subcategory inclusions, using the preservation just proved. By the definitions in [def-sf-native-weil-derived-framework], these restrictions are exactly `AlgebraicGeometry.WeilComplex.upperStar f₀` and `AlgebraicGeometry.WeilComplex.derivedLowerStar f₀`: the first is the full-subcategory lift of termwise exact pullback, and the second is the full-subcategory lift of the total right derived ordinary direct image. Their objects and morphisms are those of the ambient functors. The witnesses that an object belongs to the full subcategory are propositions, so the preservation proofs do not change either restricted functor.

Cited nodes: def-sf-native-weil-derived-framework

Source: lean/WeilConjectures/WeilSheaf/Category.lean — WeilComplex.upperStar lines 472-480; LowerStar.lean WeilComplex.derivedLowerStar lines 171-179.
