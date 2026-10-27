# Repair of lem-sf-native-weil-open-exact-constructible

## Files written

- `dag/nodes/sec-six-functors/lem-sf-native-weil-open-exact-constructible.json`: unchanged statement, three-step assembly, 2185 characters.
- `dag/nodes/sec-six-functors/lem-sf-exact-conservative-square-finite-preservation.json`: statement, unsplit, no Mathlib match for the full conservative-square assertion.
- `dag/nodes/sec-six-functors/lem-sf-native-adic-affine-open-zero-stratification.json`: statement, unsplit, no Mathlib match for the native module stratification certificate.
- `citations.json`: one checked verbatim quotation for each citation of each assembly step.

## Attachments

None. The item declaration in `lean/Sheaf/AlgebraicGeometry/NativeWeilOpenExactConstructible.lean` ends in sorry. The project source has the constituent OpenImmersion instances, not a single declaration of the full item. The generic square criterion and arbitrary-N affine certificate are not the specialized project declarations found in the upstream source. No Lean was written or compiled.

## WANTED

None. All sources used here are present in the read clone.

## Return and allocation of the old argument

This repairs the dedicated handoff at returned head e2a95534abdca96856ae1c3b80c5b78fb624dc06. The supplied sandbox contained only dispatcher marker files, not the promised prior node/report/search log. I restored the item from the current read clone; its seven steps and their lengths match the returned proof. The first required dry run exited 1 because report.md was missing. The current source record, metadata, citations and searches have been retained. No repository git command was run.

The return requires at least two independently workable unsplit nodes and an assembly of at most 3000 characters. The exact-square node takes old steps 2-3 (1564 characters of existing argument); the affine certificate takes old steps 4-6 (2299 characters). They have separate arbitrary categorical and geometric hypotheses and neither depends on the other. Old step 1 remains literally unchanged in the item; old step 7 is the final identification and edge-case assembly. The two statements are strictly intermediate: one has no scheme, coefficient or extension-by-zero hypothesis, and the other has no Frobenius action or extension functor and is about any module N satisfying specified restrictions. No single new node carries the whole item.

## Argument retained for the exact-square node

Take a natural isomorphism eta:qH -> Lp. For parallel a,b, naturality gives eta_Y qH(a+b) = Lp(a+b) eta_X = (Lp(a)+Lp(b)) eta_X = eta_Y(qH(a)+qH(b)); cancel eta_Y and use faithfulness of q. Thus H is additive, without assuming it. Applying p then L to a short exact sequence gives an exact sequence naturally isomorphic, through eta, to q of its H-image. Exactness of q identifies q of each homology object of this image sequence with zero. Conservativity of q makes the map from that homology object to zero invertible, so the homology object is zero; the endpoint tests also give mono and epi. Thus H preserves short exact sequences. An additive exact functor preserves zero and finite biproducts by their projection/injection equations, and preserves kernels and cokernels by applying exactness to the kernel and cokernel sequences. Equalizers are kernels of differences and coequalizers are cokernels of differences. Finite limits are equalizers between the finite products over objects and arrows of a finite diagram; the dual construction gives finite colimits. The empty product/coproduct is the already-preserved zero. These are the original arguments of steps 2-3, generalized to a naturally commuting square.

Source read: `lean/WeilConjectures/WeilSheaf/OpenImmersion.lean` 44-55, 138-150, and `lean/WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean` 63-93. The latter supplies the actual mapOfNatIso/forget square and explains reflection of finite universal constructions. For the generalization I also read Mathlib `CategoryTheory/Preadditive/AdditiveFunctor.lean` 127-132, `CategoryTheory/Abelian/Exact.lean` 216ff, and `Algebra/Homology/ShortComplex/ExactFunctor.lean` 220-245. These are supporting pieces, not an assertion of the full square theorem. The new node has no proof steps because other workers are to develop this argument.

## Argument retained for the affine certificate node

For an affine neighbourhood V in X, base change makes a:D=U x_X V -> V a quasi-compact open immersion. Affineness makes V qcqs. Quasi-compactness of a makes D quasi-compact. Quasi-compact opens of D are quasi-compact opens of V, and their intersections are quasi-compact by quasi-separatedness of V, so D is quasi-separated. Its image in V is an open retrocompact set; it and its complementary closed set Z are constructible. Give Z its reduced induced closed scheme structure. Pullback of the constructible module M along b:D -> U is constructible by lem-sf-native-adic-constructible-pullback, and the verified qcqs hypothesis permits lem-sf-native-adic-qcqs-stratification to give a finite lisse stratification D_r of all of D.

The supplied isomorphism j^*N = M identifies (v^*N)|D with b^*M. For actual module pullbacks, successive coefficient tensors contract: B_C tensor_(f^-1 B_B) f^-1(B_B tensor N) = B_C tensor N; the inverse inserts the unit. The equality of the two composites D -> X then identifies the actual modules, not just underlying abelian sheaves. Restricting this comparison to D_r transfers their lisse models. For g=Z -> V -> X, its image misses j(U): if a point lay in both images, the scheme pullback point-lifting property used in the source would produce a point of D above it, contradicting membership in its complement. The vanishing hypothesis therefore gives g^*N=0, and the same successive-pullback comparison gives z^*v^*N=0. This is lisse of rank zero using the identity pro-etale cover. Apply lem-weil-pbc-constructible-stratification-assembly to the two immersed, constructible, disjoint pieces D,Z, with the finite D_r stratification and the one-stratum Z stratification, taking the predicate to be that the actual pulled-back module is lisse. This gives finite lisse strata on V. Affine neighbourhoods cover X, proving constructibility. No global qcqs hypothesis on X is used. Empty pieces are discarded; the zero module has rank zero.

Sources read: `lean/WeilConjectures/SixFunctors/ProEtale/Adic/ExtensionByZero.lean` 49-105 and 204-242, including the actual inverse-image comparison and disjoint-image check, and the statements of every supporting node listed below. The old pullback/qcqs stratification/open restriction sources remain the same native locally finite continuous coefficients, without finite coefficient descent or a uniform rank. The affine certificate changes the hypothesis from N=j_!M to the precise restriction properties used by that proof, allowing its worker to work independently of extension-by-zero exactness.

## Not duplicates

lem-sf-exact-conservative-square-finite-preservation vs lem-sf-fixed-pair-adjunction-lift: the latter constructs adjunctions from invertible mate data and does not assert additivity, exactness detection or finite universal preservation.
lem-sf-exact-conservative-square-finite-preservation vs lem-sfb-kernel-cokernel-finite-exactness: the latter assumes an additive functor already preserves kernel/cokernel cones; it does not derive these hypotheses from a faithful conservative square.
lem-sf-exact-conservative-square-finite-preservation vs lem-sfb-finite-exactness-nat-iso: the latter only transports given finite preservation across an isomorphism between functors of the same type, without cancellation through q or exact-sequence detection.
lem-sf-exact-conservative-square-finite-preservation vs lem-sfb-scalar-coordinate-limit-criterion: that theorem is about scalar restriction, a supplied finite-power carrier model and finite limits only; it has neither the arbitrary abelian exact square nor the finite colimit conclusion.
lem-sf-native-adic-affine-open-zero-stratification vs lem-weil-pbc-constructible-stratification-assembly: the latter assumes finite stratifications on all immersed pieces. The new certificate must establish qcqs of every affine open intersection, obtain finite lisse strata from only local constructibility of M, and identify the actual coefficient-module pullbacks before applying assembly.
lem-sf-native-adic-affine-open-zero-stratification vs lem-sf-native-adic-qcqs-stratification: that theorem supplies strata on an already-qcqs scheme, with no affine-open intersection geometry, zero complement or carrier comparisons.
lem-sf-native-adic-affine-open-zero-stratification vs lem-sf-native-adic-open-restrictions: that theorem gives the two restriction properties for j_!M, not a constructibility certificate for an arbitrary N from those properties.
lem-sf-native-adic-affine-open-zero-stratification vs lem-sf-open-extension-zero-constant-model-constructible: that node uses pulled-back condensed coefficient rings, global finite stratifications and finite constant models on separated finite-type schemes; the new node uses the native B sheaf on arbitrary schemes, local constructibility and per-cover-member finite lisse ranks, with no assumption N is the extension functor.

I searched all DAG nodes by these notions and candidate declarations, and searched the entire imported blueprint with blueprint_refs.py for extension by zero, fixed pairs, conservative, exact functor, affine neighbourhood and lisse stratification. No imported blueprint node states either new certificate. The seed has no blueprint ancestor; this is recorded literally in blueprint.from.node=null and explained in from.place with the full via chain. Neither new source cites a Stacks tag; therefore there are no new-node/same-Stacks-tag pairs. Existing 03DI/03DJ nodes were searched and the existing ringed-slice theorem was reused in the parent, not cloned.

## Review by Q34

I read the returned item statement against the OpenImmersion source and the native coefficient framework. I kept its statement byte-for-byte. The only requested defect is proof workload: the former seven-step proof had 5078 characters; the new three-step assembly has 2185. The two extracted arguments are 1564 and 2299 characters of the former proof, comparable workloads with independent hypotheses. They are both status unsplit, have complete self-contained statements and definitions, six or more honestly logged searches apiece, empty proof arrays, empty proof_deps and null proof_origin. The statement-only files deliberately do not embed a proof sketch.

Assembly step 1 retains the original text exactly. I opened lem-weil-proetale-weakly-etale-localization and checked its site equivalence (not just its constant coefficient clause), lem-weil-pbc-open-immersion-base-change and lem-pc-quasi-compact-base-change for the two geometric-fibre hypotheses, and lem-weil-pbc-ringed-sheaf-slice-adjunction for its arbitrary ring sheaf and exact additive left adjoint computed by direct sums and sheafification. The framework supplies literal B restriction by equality of the locally finite functions. I read Stacks sites-modules.tex, lemma-extension-by-zero (03DI) and lemma-extension-by-zero-exact (03DJ), including the formula and injectivity/sheafification argument. There is no discrete-ring restriction on this use of a sheaf R. The small-site/universe convention is checked, as required by the slice theorem.

Assembly step 2 uses the framework for the explicit lift on objects/arrows, the fixed-pair definition for faithful forgetting, and lem-sf-native-weil-constructible-abelian for exact conservative forgetting and abelian ambient Weil categories. The statement of def-weil-sheaf-of-modules-category explicitly asserts abelianness of the carrier module categories in small universes; I added this citation so the generic square has all four abelian categories required. The new square statement gives every preservation property the step takes from it. There is no assumption that the lifted H is already additive. Naturality of the Frobenius comparison is still checked in the assembly, not assumed as a separate theorem. The new source and the retained argument above expose exactness and all finite universal constructions for its next worker.

Assembly step 3 uses the two actual module restrictions from lem-sf-native-adic-open-restrictions. Its statement explicitly covers every disjoint scheme morphism and the open unit isomorphism without a quasi-compactness hypothesis. The new affine certificate is applied only after step 1 supplied quasi-compactness of the geometric open. It states the finite lisse strata and nested module comparisons explicitly. The framework identifies the underlying object of the lifted image with N, giving the final clause. Thus no cited definition is being used as a missing theorem, and none of the item citations requires information found only inside another node proof. citations.json copies an exact statement substring for every used node in every step.

For the affine node future proof I separately opened the statements of lem-sf-native-adic-constructible-pullback, lem-sf-native-adic-qcqs-stratification, lem-weil-pbc-affine-scheme-qcqs, both base-change lemmas, def-weil-finite-type-morphism, def-weil-constructible-subset and lem-weil-pbc-constructible-stratification-assembly. The pullback statement allows any scheme morphism. The qcqs statement requires both conditions, and the preceding affine argument supplies both for D. The assembly statement requires a qcqs ambient scheme, a finite immersed partition with constructible images, finite strata on each piece, and a predicate on the composite immersions: these are V, D/Z, the finite D_r plus Z, and lisseness of the actual pulled-back B module. Nothing is transferred from the different condensed-coefficient constructibility notion.

I tested the generic statement with p=q=L=identity, with H the zero functor when its commuting square is zero, and with zero abelian categories; the empty-diagram conclusion really follows from preserved zero. Dropping faithfulness of q would invalidate the additivity inference, so it is retained. I tested the geometric statement with U empty, U=X, empty affine V, M=0, disjoint components with different ranks and an X without a global qcqs assumption. The argument is local on affine V and uses quasi-compactness of j, not any extra finiteness of X. It makes no rank constancy claim across covering members and no identification with a discrete non-torsion coefficient category.

Mathlib checks: I read the hits rather than counting empty searches. exact_tfae states the finite-preservation equivalence after additivity and exactness are established; additive_of_comp_faithful is only the additivity clause, and reflects_exact_of_faithful only reflects one short complex. None supplies the full naturally commuting square and comparison argument as a one-line specialization. For the geometric node the hits are statements about constructible sets, finite affine covers, or structure-sheaf sections; none is native locally finite continuous coefficient lisse stratification. A second phrasing was run for both nodes; queries and actual result digests are in searches.jsonl and the node records, with no unavailable service misrepresented as a failed match.

The B-E checklist was applied to the actual statements and sources: fresh ids, typed and quantified objects, valid TeX, no proof in the unsplit statements, explicit sources and places, blueprint ancestry and searches, no duplicate of the item or one of its clauses, no cycles, and correct citation hypotheses. No assembly step exceeds 2000 characters. No statement dispute, new target hypothesis, source-route change or forbidden SGA source was introduced. Prior accepted tool uses are retained only where used by the parent; the affine assembly theorem now belongs to the future affine-certificate proof and is documented above rather than incorrectly cited by the item.

## What remains

Only the two new statement-only lemmas remain for later workers, as explicitly requested by this repair. The item assembly is complete at stage 1. Delivery validation results are recorded below.

## Original seven proof steps, retained verbatim

### Original step 1

Write $J=\bar j_!$ on the underlying $B$-module sheaves. Base change preserves open immersions and quasi-compactness, so $\bar j$ is a quasi-compact open immersion. The weakly-etale localization identifies $\bar U_{\mathrm{proet}}$ with $\bar T_{\mathrm{proet}}/\bar U$. The coefficient restriction is literally $B_{\bar T}|_{\bar U}=B_{\bar U}$: both assign to $V\to\bar U$ the locally finite continuous functions on $|V|$. Thus $J$ is exactly the direct-sum-presheaf/sheafification extension on this ringed slice. Apply the ringed-sheaf-slice adjunction theorem with its sheaf of sections $A=h_{\bar U}$ and $R=B_{\bar T}$. It says that this extension is additive and exact. The chosen small-site convention is the one in the framework; no finiteness or discreteness assumption on the coefficient ring is used.

Uses: def-sf-native-weil-derived-framework, lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-open-immersion-base-change, lem-pc-quasi-compact-base-change, lem-weil-pbc-ringed-sheaf-slice-adjunction

### Original step 2

The framework defines $j_{0!}(M,\phi)=(JM,J(\phi)\circ c_M)$ and its action on arrows is $J$. Naturality of $c$ gives the commuting-square condition for every image arrow. The forgetful functor is faithful by the fixed-pair definition, so the equality $J(a+b)=J(a)+J(b)$ proves additivity of $j_{0!}$. To check exactness, use the native abelian theorem: both ambient Weil categories are abelian and their forgetful functors are exact and conservative. An exact sequence becomes exact after forgetting, remains exact under $J$, and is the forgotten image sequence. Its homology object therefore has zero image under the target forgetful functor. Conservativity implies that object is zero, since its map to zero becomes an isomorphism. Hence the image sequence is exact in $\mathcal W_T$.

Uses: def-sf-native-weil-derived-framework, def-weil-endofunctor-fixed-pair-category, lem-sf-native-weil-constructible-abelian

### Original step 3

An additive exact functor of abelian categories preserves all finite limits and finite colimits as follows. The zero object and finite biproducts are preserved: the equations $p_ai_b=\delta_{ab}$ and $\sum i_ap_a=1$ survive an additive functor. Exactness applied to $0\to\ker a\to M\xrightarrow{a}N$ and dually to $M\xrightarrow{a}N\to\operatorname{coker}a\to0$ gives the kernel and cokernel comparisons. An equalizer of $a,b$ is $\ker(a-b)$ and a coequalizer is $\operatorname{coker}(a-b)$. A finite diagram limit is the equalizer of the two maps from the product of its objects to the product indexed by its arrows; the dual coequalizer constructs its colimit. This also includes the empty diagram. Apply these formulas to the additive exact $j_{0!}$ from the preceding step.

Uses: lem-sf-native-weil-constructible-abelian

### Original step 4

Let $M$ be the constructible underlying sheaf of $F$. At a point of $\bar T$ choose an affine open $V$. Put $D=\bar U\times_{\bar T}V$ with maps $a:D\hookrightarrow V$ and $b:D\to\bar U$. The base-change lemmas make $a$ a quasi-compact open immersion. Since $V$ is affine it is quasi-compact and quasi-separated. By the definition of quasi-compact morphism, $D=a^{-1}(V)$ is quasi-compact. It is quasi-separated as an open subscheme of $V$: quasi-compact opens of $D$ are quasi-compact opens of $V$, and their intersections are quasi-compact by quasi-separatedness of $V$. Let $Z$ be the reduced closed complement of $D$ in $V$. Thus $D$ and $Z$ partition $V$, and their images are constructible: the quasi-compact open $D$ is retrocompact in the quasi-separated $V$, and $Z$ is its complement.

Uses: def-sf-native-weil-derived-framework, lem-weil-pbc-open-immersion-base-change, lem-pc-quasi-compact-base-change, lem-weil-pbc-affine-scheme-qcqs, def-weil-finite-type-morphism, def-weil-constructible-subset

### Original step 5

The native adic pullback theorem applied to $b$ says that $b^*M$ is constructible on $D$. The preceding step verified both quasi-compactness and quasi-separatedness of $D$, so the native qcqs stratification theorem gives a finite constructible locally closed stratification $D=\coprod_rD_r$ on which $b^*M$ is lisse. These statements concern the actual locally finite continuous coefficient sheaves, and impose neither descent to finite coefficients nor a single rank for every member of a trivializing pro-etale cover.

Uses: lem-sf-native-adic-constructible-pullback, lem-sf-native-adic-qcqs-stratification

### Original step 6

Let $G=\bar j_!M$. The open-restriction unit gives $\bar j^*G\cong M$, hence $(G|_V)|_{D}\cong b^*M$ and the restrictions to each $D_r$ have the same lisse models. Here nested module restrictions use the usual inverse-image composition: the coefficient tensor factors contract by $B_C\otimes_{f^{-1}B_B}f^{-1}(B_B\otimes N)\cong B_C\otimes N$, so these are the actual $B$-module pullbacks. For the composite $Z\to V\to\bar T$, its image misses $\bar j(\bar U)$, so the disjoint-pullback clause gives $(G|_V)|_Z\cong0$. This is lisse of rank zero, with the identity pro-etale cover. Apply constructible stratification assembly to the two immersed pieces $D,Z$ of $V$, with the finite stratification from the preceding step on $D$ and the single stratum on $Z$. Use as predicate that the restricted $B$-module is lisse. The theorem supplies a finite constructible locally closed stratification of $V$ on which $G|_V$ is lisse. Thus $G$ is constructible locally at every point of $\bar T$.

Uses: lem-sf-native-adic-open-restrictions, lem-weil-pbc-constructible-stratification-assembly, def-sf-native-weil-derived-framework

### Original step 7

The underlying sheaf of $j_{0!}F$ is $G$ by the defining lift in the framework. The preceding local stratifications prove the required constructibility. They allow $D=\varnothing$, $Z=\varnothing$ and zero sheaves: empty strata are omitted and the zero restriction has rank zero. Therefore the additive functor $j_{0!}$ has both finite preservation properties and the constructibility property asserted.

Uses: def-sf-native-weil-derived-framework


## Validation and retained earlier reports

The read clone also contains the previous NL stage-1 report and NM statement report. I read both and retained them in retained-stage1-report.md and retained-statement-report.md. The NL report documents the refused generated-instance-name attachment, so this repair makes no renewed ATTACH claim. Its supporting-node searches and closed-declaration findings remain in the live nodes; no old logged search was invented or replayed as new evidence.

The first server review_split check passed. The first complete dry run rejected two citation quotations solely for being shorter than 40 characters; both were replaced by longer exact quotations from the same statements. No mathematical citation or statement changed.
