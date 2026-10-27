# Worker report: lem-sfb-profinite-constant-derived-functions

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-constant-derived-functions.json: repaired split; statement unchanged; proof is 1524 characters in three assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-free-slice-derived-hom.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-point-pullback-derived-hom.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-free-parameter-evaluation-coherence.json: statement, unsplit; no Mathlib match.
- report.md and citations.json: author's review, argument handoff and verbatim citation evidence.

Three new statement-only nodes, zero Mathlib leaves. Every new node has proof=[], proof_deps=[], proof_origin=null. No Lean, compiler, Lake, build, repository write or direct git command was used. The existing Lean, reviewed, blueprint/import and search metadata of the item were retained.

## Attachments

None. I searched lean/WeilConjectures by the item id, blueprint tag, ProfiniteFunctions, derived/profinite and function notions, and read the existing Sheaf/Paper/ProfiniteConstantDerivedFunctions.lean interface. Its comparison_isIso (line 1262), derivedSliceComparison_isIso (line 474), pointHomComparison_constant_isIso (line 1298 onward), delta_normalization, delta_factorization, delta_wholeFamily and comparison_scalarModel still use sorry. The definition delta inverts a comparison whose invertibility is sorry. It is not an attachment, and upstream coefficient-colimit comparison declarations do not supply this all-continuous parameter theorem. The new general statements are not claimed proved by these sorried interfaces.

## WANTED

WANTED: an exact published all-continuous relative-profinite-functions theorem including the whole-family and nonflat coefficient-mate clauses, for lem-sfb-profinite-constant-derived-functions. The blueprint itself labels this an agent-formulated input, and I retain that attribution. The argument is agent-written from the available HRS and Stacks constructions; no unavailable theorem is silently quoted.

## Fault repaired and retained context

The return requires distributing the eight-step, 6450-character proof among at least two independently assignable statement-only nodes. The repair adds three inputs: relative free module and unbounded slice computation; global condensed-point derived Hom comparison; evaluation coherence before invertibility. Their argument allocations are old steps 1–3, 4–5 and 6–8 respectively (2362, 1429 and 2659 characters in the returned text). None restates the entire item: the first has no point/Hom preservation assertion, the second has no relative projection or analytic coefficients, and the third proves identities for a forward evaluation map without asserting it invertible. The parent assembles their independently normalized maps and takes an inverse.

No node/report/search log from a previous Q08 attempt was in the sandbox: it held only dispatcher .brief files. I copied the current returned repository node and preserve its entire old argument below. The current node has already retained maintainer and Lean metadata; I did not overwrite them with older launcher text. The current chapter is sec-six-functors-basics and unit label is sk-thm-sf-ctf-stability; the recorded unit JSON still describes a legacy sec-six-functors unit. I read both records and follow the item's explicit current main-20261015 source, paragraph (3), without modifying the chapter or unit. This item is not the unit's key statement.

I corrected a source-pointer imprecision in the handoff: Stacks 03DI and 03DJ are extension by zero and its exactness, not the free-generator internal-Hom identity. The actual ingredients are 08FI, lemma-restrict-K-injective-to-open; 08J7, section-internal-hom; 03EO, lemma-internal-hom-adjoint-tensor; 0E8H, lemma-internal-hom-restriction; and 08JB, lemma-restriction-RHom-to-U. The archived old proof is verbatim, including its old pointers; the repaired nodes/report give the actual sources. This is a proof/reference repair, not a statement change. There is no STATEMENT-DISPUTED.

## Sources and Mathlib searches

I read Hemo–Richarz–Scholbach 2305.18131, Section 3 (point morphism, Example 3.1, definition of D and tensor/internal Hom), construction (4.1), Proposition 4.3(1), its proof and (4.2). HRS uses a derived infinity category; the assertions used here descend to its ordinary homotopy derived category, and the named existing ringed-site nodes specify the ordinary unbounded K-flat/K-injective models. I do not identify arbitrary coefficients with discrete scalar modules or impose a lisse/perfect condition.

For lem-sfb-profinite-free-slice-derived-hom, I read the Stacks 08FI statement and proof and the construction and adjunction in 08J7, together with 03EO and 0E8H in sites-modules.tex. The module/sheaf transport is supplied by the existing exact tensor comparison, internal-Hom comparison and operations-transport nodes. The new content is the actual representability/free-generator identification and its normalized derived slice isomorphism for arbitrary unbounded K.

For lem-sfb-point-pullback-derived-hom, HRS 4.3(1) supplies precisely the arbitrary unbounded derived internal-Hom assertion on a geometrically w-contractible affine's component site. The new assertion globalizes to p_X, with the evaluation-adjoint morphism fixed before invertibility. Its handoff uses component factorization, exact slice Hom restriction (08JB) and the single-cover theorem; it does not assume that an arbitrary inverse image preserves derived Hom.

For lem-sfb-free-parameter-evaluation-coherence, I read Stacks 08J7's evaluation adjunction and 08JB/0E8H's actual slice restriction construction. I checked the supplied slice evaluation/transposition equations and the derived extension/restriction adjunction in the existing ringed pullback/projection nodes. The new content is the single forward comparison c, its factorization, simultaneous variable parameter/module square, and nonflat coefficient square. This is an identity theorem, so neither its hypotheses nor its proof use the parent's claimed isomorphism.

Before creating nodes I searched the entire DAG by profinite/free/representable/point-Hom/parameter/evaluation and by 08FI, 08J7 and 08JB, and used tools/blueprint_refs.py ancestor and search with profinite, evaluation, internal Hom, free representable, free parameter, parameter and pullback derived internal Hom. The ancestor output is None; the current item's from.node is null, so the children retain that null ancestor and prepend the item to the via chain, with precise places. No blueprint node states any of the new inputs.

All Mathlib queries were run through the required msearch.py command and recorded in searches.jsonl. For each new node I ran LeanFinder, Loogle, grep, a LeanSearch attempt, and a second semantic phrasing plus second Loogle and grep patterns. All three LeanSearch attempts were explicitly unavailable due to HTTP rate limiting; the nodes record unavailable, not absence. The raw actual responses are retained in repair-search-results.json and copied into mathlib_searches; the item's earlier searches are retained.

I read Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean, especially pullbackObjFreeIso at 118: it pulls back a direct sum indexed by an ordinary Type, not a free internal module on a variable representable sheaf. Mathlib/Condensed/Light/InternallyProjective.lean, ihomPoints and its naturality, is underived light condensed Hom over a discrete ordinary ring. I read the sheaf ChangeOfRings.lean restrictScalars at 36 and the ExponentiableMorphism ev_naturality/triangle identities: these give ordinary scalar restriction or ordinary slice adjunctions, not the requested derived family/coefficient comparisons. Other semantic hits are ordinary pullback adjunctions or unrelated cotangent/flatness results. None is an exact match or one-line specialization for a new statement.

## Review by Q08

I checked the repair against B–E, including the duplicate/elementary/whole-item-clause pitfalls and the return's explicit re-split requirement. The three new statements introduce their own schemes, sites, coefficient rings, modules, parameters and maps, with defining nodes for the non-inline notions; no new definition is hollow, no new node contains proof steps, and all three can be assigned as independent arguments (the coherence node uses the stated slice isomorphism but no proof of the parent).

Parent step 1 cites lem-sfb-profinite-free-slice-derived-hom: its displayed gamma is exactly the derived identification used by that step, and its closing clauses supply the internal/section-ring normalization and rho^*p_X^*=p_U^*. The hypotheses allow X affine, Lambda=C_F and K=p_X^*M_F[0] without assuming completion, discreteness or boundedness of resolutions.

Parent step 2 cites lem-sfb-point-pullback-derived-hom: its displayed beta is exactly the evaluation-adjoint isomorphism at (Lambda[P],M_F[0]); its stated all-unbounded hypothesis covers the arguments of step 2. Composing the two isomorphisms and taking their inverse is elementary category theory, so the assembly introduces no further theorem. In particular beta is not selected by asking that delta be invertible.

Parent step 3 cites lem-sfb-free-parameter-evaluation-coherence: clause (1) fixes c=gamma beta, degree-zero normalization, parameter and module naturality and pro-etale base change. Clause (2) gives an equality in D on X[Q] for an arbitrary module morphism u and a parameter map over that slice; it explicitly includes (q,p') to (q,alpha(q,p')), so the parent is using a whole-family statement, not pretending points detect derived maps. The finite-free sentence identifies the action with matrices over B, so arbitrary X-linear maps are covered. The only specialization in the parent is the elementary finite-dimensional basis identification C(Q,F tensor_E M)=C(Q,F)^r, valid with the stated product norm topology even for non-complete Omega. Clause (3) is precisely the forward coefficient square needed for C_E to C_Omega and x to 1 tensor x; multiplying by the two inverse c maps gives the requested inverse square. There is no claim that coefficient extension is exact or that its vertical comparison arrows are isomorphisms.

For the expanded handoffs I reopened every old cited node's statement. Old step 1's equivalence/tensor/Hom/direct-image transport nodes assert those specific operations and evaluation normalization. In old step 2 the two basis-evaluation statements use the categorical evaluation criterion, so the separate source-affine-wcontractible-evaluation node supplies that hypothesis from geometric w-contractibility; det-pe-hypercover-single-cover supplies covers of quasi-compact affine tests. Pullback composition is the explicit monoidal comparison in lem-weil-pbc-profinite-point-pullback. Old step 3 uses only clause (1) of weakly-etale-localization; the later constant-ring clauses are not used for the nonconstant ring B. The 08FI node really says K-injective restriction, and def-pur-derived-internal-hom gives the Hom-complex model, so the generator calculation identifies the same complex on both sides. Old steps 4–5 use the derived tensor comparison and actual slice transpose equations, then the factorization p_W=q_S pi_W, the exact slice Hom comparison and HRS component theorem. Every hypothesis on W is supplied by the single-cover input, and vanishing of a cone's cohomology sheaves is checked locally. Old steps 6–7 use actual transposes, not degree-zero detection of derived morphisms; arbitrary local matrices are evaluated before applying the transpose. Old step 8 uses the extension/restriction derived adjunction with K-flat tensor, not exactness of extension. The unit generator under coefficient extension is [t] to [t]; the two mates evaluate and then apply n in the same order.

I tested P empty (both gamma sides zero), P a point (gamma is the identity), X empty, M=0, Lambda=0, and zero ranks. For beta, arbitrary unbounded K,L are allowed because exact slice restriction and the existing HRS theorem are unbounded; no step uses a uniform cohomological bound. For the family identity Q empty is an equality in the zero slice, while nonconstant alpha and matrices are morphisms on the entire slice. For the scalar square I tested an identity ring map and the nonflat map Z to Z/2: only derived extension is used, so no unjustified flatness inference is made. Normed algebraic closures need not be complete: only finite products and all continuous functions enter. The new statements pass these cases.

I checked the old long steps individually: none exceeds 2000 characters, but the return concerns their combined work. The new parent has no long step; no argument was removed by compressing the parent. The full old arguments and their precise allocations follow. The construction, w-contractible-local isomorphism proof and all three coherence arguments remain explicit handoffs for later workers.

## Argument handoff: verbatim returned proof

This is retained mathematical work for the new statement-only nodes, not proof fields on those nodes. Each old step is reproduced in full, including dependencies and old source pointers. Allocation: old steps 1–3 to lem-sfb-profinite-free-slice-derived-hom; old steps 4–5 to lem-sfb-point-pullback-derived-hom; old steps 6–8 to lem-sfb-free-parameter-evaluation-coherence. The sentence taking the inverse at the end of old step 5 is the parent's assembly; the rest of that step belongs to lem-sfb-point-pullback-derived-hom. Canonical free-generator and restriction identities at the end of old steps 2–3 are also the input used for lem-sfb-free-parameter-evaluation-coherence's factorization and slice statements.

### Old step 1 → lem-sfb-profinite-free-slice-derived-hom

Write $\Lambda=C_F$, $A=\Lambda[P]$, $N=M_F[0]$ and $B=p_X^*\Lambda$. Work interchangeably with internal modules and their section-ring module sheaves: the exact equivalence preserves underlying sheaves, tensor and its derived model, and takes the right-adjoint internal Hom to K-injective derived sheaf Hom with the same evaluation. It likewise transports the entire direct-image functor and its derived adjunction. On the condensed-point site the same exact monoidal equivalence identifies internal and sectionwise modules; preservation of K-flat and K-injective resolutions follows by transporting their defining Hom/tensor acyclicity tests. Thus no change of coefficient category or completion is involved.

Uses: def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-pe-internal-section-tensor-comparison, lem-sfb-module-object-ringed-site-derived-comparison, lem-sfb-internal-module-operations-transport.

Source: literature/stacks-project/sites-cohomology.tex, 08J7 and 08J9; internal/sectionwise transport by the cited exact monoidal equivalences..

### Old step 2 → lem-sfb-profinite-free-slice-derived-hom

There is a canonical identification $p_X^{-1}h_P=h_{X[P]}$. Indeed, on a geometrically w-contractible affine test $V$ both sides are $C(\pi_0V,P)$, with the same restrictions; geometric w-contractibility implies the site evaluation criterion needed by the two cited evaluation statements. Such affines cover every affine test by the single-cover theorem; arbitrary tests have affine open covers. Consequently the identifications determine an equality of sheaves. Pullback also takes $A$ to $B[h_{X[P]}]$: for any $B$-module $T$, the pullback adjunction and the free-module adjunction identify maps from either object to $T$ with maps $h_P\to p_{X*}(\operatorname{Forget}T)$, since module direct image has that underlying sheaf. Yoneda gives the isomorphism, normalized on generators. Similarly $\rho_P^*p_X^*N=p_{X[P]}^*N$ by composition of the condensed-point pullbacks.

Uses: lem-weil-pbc-condensed-point-basis-evaluation, lem-weil-pbc-proetale-point-components-maps, lem-weil-pbc-source-affine-wcontractible-evaluation, det-pe-hypercover-single-cover, lem-weil-pbc-profinite-point-pullback.

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf, Example 3.1; component evaluation and the free-module universal property..

### Old step 3 → lem-sfb-profinite-free-slice-derived-hom

The small pro-etale site of $X[P]$ is the slice $X_{\mathrm{proet}}/X[P]$; use only clause (1) of the localization node. Put $U=X[P]$ and take a K-injective resolution $p_X^*N\to J$. The free-generator adjunction, applied on each slice over $V$, identifies $\mathcal Hom_B(B[h_U],J)(V)$ with $J(V\times_XU)$, degree by degree and with the same differential. By preservation of K-injectives under localization, $J|_U$ is K-injective and resolves $p_{X[P]}^*N$. Thus the identical complex $\mathcal Hom_B(B[h_U],J)=\rho_{P*}(J|_U)$ computes both $R\mathcal Hom_B(p_X^*A,p_X^*N)$ and $R(\rho_P)_*p_{X[P]}^*N$. This is the canonical derived identification, natural in the object, the parameter maps and further localization because its degreewise maps evaluate the same free generator.

Uses: lem-weil-proetale-weakly-etale-localization, lem-pur-kinjective-restrict-localized, def-pur-derived-internal-hom.

Source: literature/stacks-project/sites-modules.tex, 03DI and 03DJ, derived using sites-cohomology 08FI and 08J7..

### Old step 4 → lem-sfb-point-pullback-derived-hom

Pull back the evaluation $R\mathcal Hom_\Lambda(A,N)\otimes_\Lambda^{\mathbf L}A\to N$ along $p_X$, using its exact inverse image and canonical derived tensor comparison. Transposition defines
$\beta_X:p_X^*R\mathcal Hom_\Lambda(A,N)\to R\mathcal Hom_B(p_X^*A,p_X^*N)$.
This defines a morphism before any assertion that it is invertible. Under restriction to a slice it is the same evaluation-adjoint morphism: the cited slice evaluation/transposition identities identify the two transposes. In particular its restriction to a test $W$ is $\beta_W$, using the cartesian coefficient identification for $p_W$.

Uses: lem-weil-pbc-profinite-point-pullback, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-ringed-slice-evaluation-transpose.

Source: literature/stacks-project/sites-cohomology.tex, 08J7 tensor-Hom adjunction; derived monoidal pullback and evaluation normalization as in the cited nodes..

### Old step 5 → lem-sfb-point-pullback-derived-hom

Let $W\to X$ be a geometrically w-contractible affine test and put $S=\pi_0W$. The component morphism gives $p_W^*=\pi_W^*q_S^*$. Restriction $q_S^*$ from the profinite site to its slice over $S$ commutes with derived internal Hom for arbitrary unbounded complexes. The component theorem then identifies
$\pi_W^*q_S^*R\mathcal Hom_\Lambda(A,N)$ with $R\mathcal Hom_{p_W^*\Lambda}(p_W^*A,p_W^*N)$.
Both arrows are normalized by evaluation, so their composite is precisely the restriction of $\beta_X$ constructed in step 4. Hence $\beta_X|_W$ is invertible. Every affine test has such a cover by the single-cover theorem. The cone therefore has all cohomology sheaves zero locally and hence globally; $\beta_X$ is invertible. Compose its inverse with step 3 to obtain $\delta_{X,P,M_F}$ in the direction stated in the item.

Uses: lem-zl-component-relative-profinite-site, lem-weil-pbc-ringed-internal-hom-exact-restriction, lem-sfb-wcontractible-component-derived-hom, det-pe-hypercover-single-cover.

Source: literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf, Proposition 4.3(1); restriction of derived internal Hom is Stacks 08JB..

### Old step 6 → lem-sfb-free-parameter-evaluation-coherence

The slice identification evaluates a free generator, and $\beta_X$ is the transpose of pulled-back evaluation. Thus the inverse composite has exactly the specified degree-zero exponential-law normalization, sending a section on $V[P]$ to its corresponding $P$-indexed function. Uniqueness of transposes gives naturality in $N$ and in maps $h_{P'}\to h_P$, hence in $M$ and continuous maps $P'\to P$. The same argument on a slice, with the slice evaluation identities, gives pro-etale base change. If a base-changed scheme is not affine, this equality holds on its affine open cover and glues. These are equalities of the derived morphisms, since they are obtained by transposing identical evaluation morphisms.

Uses: def-pur-derived-internal-hom, lem-weil-pbc-ringed-slice-evaluation-transpose, lem-weil-pbc-profinite-point-pullback.

Source: literature/stacks-project/sites-cohomology.tex, 08J7 and 08JB; uniqueness of tensor-Hom transposes and slice compatibility..

### Old step 7 → lem-sfb-free-parameter-evaluation-coherence

Choose bases only to check the remaining linear-map clause. The supplied constant models are $B^r$ and $B^s$, since continuous functions into a finite product are products of continuous functions. On every slice an arbitrary map between them is a matrix of sections of $B$; all comparison maps above are $B$-linear and respect finite sums. They therefore commute with this matrix, including matrices not pulled back from the condensed point. This description is independent of the checking bases. Over $X[Q]$, repeat the construction in that slice. A continuous $\alpha:Q\times P'\to P$ induces a map of parameter objects over $X[Q]$. Transposing the two proposed composites gives the same evaluation morphism there: for a local family $f$, it sends $(q,p')$ to $u(q)(f(q,\alpha(q,p')))$. This notation describes evaluation on the entire parameter object, not evaluation only at its points. The equality follows from the free-generator adjunction and associativity of composition, so it holds over $X[Q]$, including all higher derived terms by the same transposition identity.

Uses: lem-weil-pbc-ringed-slice-evaluation-transpose, def-pur-derived-internal-hom.

Source: literature/stacks-project/sites-cohomology.tex, 08J7 and 08JB; formal linearity and evaluation on the slice, with finite free models..

### Old step 8 → lem-sfb-free-parameter-evaluation-coherence

Finally apply the coefficient map $C_E\to C_\Omega$ and the module map $M_E\to\operatorname{Res}M_\Omega$, $x\mapsto1\otimes x$. The free-generator coefficient-extension identification sends the generator $[a]$ to $[a]$. The canonical coefficient-comparison arrows for internal Hom and direct image are mates of these evaluation/module maps. After scalar restriction both composites in the requested square transpose to the identical map, evaluating a function and then applying $x\mapsto1\otimes x$. Hence their mates agree. This argument uses the derived extension/restriction adjunction (K-flat tensor for extension) and does not assert that scalar extension is exact or that the scalar-comparison arrows themselves are isomorphisms. All operations used the original sheaves $C(Q,F)$ and $C(Q,F\otimes_E M)$; no finite-subextension-valued or completed model has entered.

Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-ringed-projection-mate-exact.

Source: literature/stacks-project/sites-cohomology.tex, 08J7: compatibility of evaluation with coefficient maps, by uniqueness of adjunction mates; derived coefficient extension is ringed pullback for the identity topos..

## Additional handoff details

For the arbitrary-unbounded version of the slice lemma, take any K-injective representative J of K rather than the particular p_X^*N representative in old step 3; the identical local generator calculation and 08FI apply with no degree bound. For the generalized point-Hom lemma, replace A,N in old steps 4–5 by arbitrary K,L. The HRS component theorem and slice comparison state exactly that generality. On a non-affine X apply the affine-test argument locally. These generalizations require no new analytic fact.

For the forward evaluation coherence lemma, define c first by the projection adjunction, so its definition contains no inverse beta or delta. The two adjoints c and gamma beta are the same universal-generator evaluation; hence their equality follows by the bijection of adjunction. Under any further localization the evaluation and tensor/Hom comparisons are the specified ones, and this same adjunct proves the base-change identity. For a family map a over V and any u, transpose the square: both composites first substitute a into the universal parameter and then postcompose with u. This is an equality of sheaf-module evaluation maps on V, with the identical Hom-complex differentials and derived transposes, hence an equality in the entire derived slice. For finite free models, apply it to every matrix entry over the coefficient sheaf; finite sums and B-linearity show that changing bases changes both sides by the same invertible matrices. This verifies the supplied X-linear interpretation independently of delta.

For a coefficient morphism Lambda to Lambda', the free-module extension map sends each generalized generator [t] to [t]. Free representable module sheaves are flat: their presheaf free modules are sums of the coefficient presheaf on each section set, so tensoring an exact sequence is sectionwise exact wherever that sequence is exact; exactness of sheaves is local, and sheafification preserves it. Consequently their degree-zero K-flat model gives the same generator identification for derived scalar extension. The derived extension/restriction adjunction, with that identification, makes the two transposes in the coefficient square the identical map which evaluates and then applies n. This explains why no flatness of the coefficient ring morphism, and no preservation of K-injectivity by its ordinary restriction functor, is needed. The direct-image scalar arrow is the derived adjunction mate, not an unproved equality of arbitrarily chosen K-injective resolutions.

## Not duplicates

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-ringed-slice-normalized-comparisons: the existing assertion concerns Existence of normalized slice tensor, Hom and Koszul comparisons; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs def-sf-integral-hom-reduction-comparison: the existing node defines Canonical integral internal Hom reduction comparison; the new node proves relative profinite representability and the normalized unbounded slice direct-image isomorphism.

- lem-sfb-profinite-free-slice-derived-hom vs def-coef-semilinear-derived-calculus: the existing node defines Ordinary derived semilinear calculus interfaces; the new node proves relative profinite representability and the normalized unbounded slice direct-image isomorphism.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sf-coefficient-tensor-curry-normalization: the existing assertion concerns Normalization of coefficient tensor currying; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-pod-point-hom-complex-adjunction: the existing assertion concerns Normalized chain-level Hom adjunction at the point; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-coef-signed-single-dual-restriction: the existing assertion concerns Normalized slice comparison for a single coefficient dual; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sf-scalar-tensor-comparison-transport: the existing assertion concerns Transport of normalized scalar tensor comparison; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs def-sf-coefficient-duality: the existing node defines Coefficient duality and bounded finite-cohomology complexes; the new node proves relative profinite representability and the normalized unbounded slice direct-image isomorphism.

- lem-sfb-profinite-free-slice-derived-hom vs lem-pod-point-tensor-hom-evaluation: the existing assertion concerns The normalized Hom comparison intertwines signed evaluation; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-pod-module-hom-signed-evaluation: the existing assertion concerns Signed evaluation for ordinary module Hom complexes; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-coef-slice-hom-source-shift: the existing assertion concerns Slice restriction preserves the normalized source shift of derived Hom; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-pod-point-sheaf-hom-maps: the existing assertion concerns Sheaf evaluation and sections-tensor maps for the point model; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-coef-semilinear-operations-existence: the existing assertion concerns Geometric and coefficient operations on a fixed semilinear system calculus; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-coef-semilinear-system-existence: the existing assertion concerns Ordinary semilinear system calculus and cartesian internal Hom; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sf-coefficient-cochain-tensor-curry: the existing assertion concerns Componentwise coefficient cochain currying; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs def-sf-evaluation-hom-site-comparison: the existing node defines Evaluation-induced derived Hom comparison for the etale-proetale morphism; the new node proves relative profinite representability and the normalized unbounded slice direct-image isomorphism.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sc-derived-hom-finite-free-model-aux: the existing assertion concerns Bounded-above finite-free Hom computes derived internal Hom into a bounded-below complex; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sc-derived-single-hom-evaluation: the existing assertion concerns Derived single-source Hom evaluation; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sc-derived-internal-hom-unit-iso: the existing assertion concerns Derived internal Hom from the structure sheaf is the identity; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sc-hom-complex-mapping-cone-differential: the existing assertion concerns Differential compatibility of the internal Hom cone comparison; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sc-hom-complex-unit-iso: the existing assertion concerns Hom complex from the structure sheaf is the identity; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sc-hom-complex-mapping-cone: the existing assertion concerns Internal Hom complexes commute with mapping cones; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sc-derived-internal-hom-single-comparison: the existing assertion concerns Unary internal Hom derives to internal RHom from a degree-zero module; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sfb-derived-internal-hom-sections-model: the existing assertion concerns Derived internal Hom into a K-injective and its derived global sections; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sfb-free-representable-derived-functions-model: the existing theorem is for M[0], bounded-below injective resolutions and sheafified derived presheaf sections; the new slice theorem supplies p_X^{-1}h_P=h_{X[P]}, internal coefficients and a normalized isomorphism with actual slice Rrho_*rho^* for arbitrary unbounded K.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sfb-base-change-identity-open-restriction: the existing assertion concerns The canonical base-change mate is identity on an open isomorphism locus; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sfb-identity-open-derived-adjunction-normalization: the existing assertion concerns K-injective normalization and derived adjunction at an identity open locus; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-element-restriction-hom: the existing assertion concerns Exact closed restriction on arbitrary element sites; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-etale-localization-exchange: the existing assertion concerns Exchange along an etale morphism of the target is an isomorphism; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-ringed-slice-pullback-mate-normalization: the existing assertion concerns Slice pullback comparison is induced by the ringed localization square; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-derived-square-shift-on-kinjectives: the existing assertion concerns Shift coherence of a derived square computed on K-injectives; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-ringed-projection-restriction: the existing assertion concerns Localization comparisons for the ringed projection mate; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs def-weil-pbc-ringed-projection-restriction-data: the existing node defines Normalized ringed projection and slice comparison data; the new node proves relative profinite representability and the normalized unbounded slice direct-image isomorphism.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-ringed-completion-unit-naturality: the existing assertion concerns Naturality of the actual derived completion unit; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-ringed-projection-tensor-comparison: the existing assertion concerns Descent and signed shifts of the normalized pro-etale tensor comparison; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-ringed-slice-comparisons-shift: the existing assertion concerns Shift normalization of canonical ringed-slice comparisons; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs def-weil-pbc-ringed-completion-unit: the existing node defines RingedCompletionUnit; the new node proves relative profinite representability and the normalized unbounded slice direct-image isomorphism.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-ringed-projection-global-model: the existing assertion concerns Existence of the canonically normalized global projection package; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-ringed-projection-local-model: the existing assertion concerns Localization of a normalized global projection package; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-pur-kinjective-restrict-localized: the existing assertion concerns Restriction to a localized ringed site preserves K-injectivity; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-exc-finite-coefficient-open-kinjective: the existing assertion concerns Finite coefficient open pullback preserves K-injectivity; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-pur-kinjective-restrict-localized-adjunction: the existing assertion concerns Exact additive extension by zero adjoint to localized restriction; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs new-localized-restriction-extension-exists: the existing assertion concerns Exact extension adjoint for localized restriction; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs new-localized-restriction-extension-exists-universes: the existing assertion concerns Exact extension adjoint for localized restriction with independent coefficient universe; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs def-pur-derived-internal-hom: the existing node defines Derived internal Hom on a ringed site; the new node proves relative profinite representability and the normalized unbounded slice direct-image isomorphism.

- lem-sfb-profinite-free-slice-derived-hom vs lem-dg-etale-injective-finite-cech-rows: the existing assertion concerns Split finite ordered Cech rows for injective etale module sheaves; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-pur-kinjective-restrict-localized-universes: the existing assertion concerns Restriction to a localized ringed site preserves K-injectivity with independent coefficient universe; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-pur-kinjective-restrict-localized-adjunction-universes: the existing assertion concerns Exact additive extension by zero adjoint to localized restriction with independent coefficient universe; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs lem-sp-subterminal-derived-image-calculus: the existing assertion concerns K-injective derived direct-image comparisons for subterminal slices; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-profinite-free-slice-derived-hom vs def-sfb-condensed-free-module-generators: the existing node defines Canonical free internal-module adjunction and local profinite tuple generators; the new node proves relative profinite representability and the normalized unbounded slice direct-image isomorphism.

- lem-sfb-profinite-free-slice-derived-hom vs lem-weil-pbc-profinite-test-object-functor: the existing assertion concerns Relative profinite test schemes: existence, functoriality and site properties; it does not assert both profinite representability under point pullback and the normalized unbounded relative-free slice Rrho_*rho^* identity.

- lem-sfb-point-pullback-derived-hom vs lem-sfb-wcontractible-component-derived-hom: the existing theorem concerns pi_W^* from the relative component site on a w-contractible affine; the new point theorem concerns p_X^* from the absolute condensed point on every scheme, including its globalization and specified evaluation map.

- lem-sfb-point-pullback-derived-hom vs lem-zl-component-relative-profinite-site: the existing assertion concerns The relative profinite test functor over an affine component space; it does not assert the evaluation-adjoint derived Hom isomorphism for absolute p_X^* on every scheme and all unbounded K,L.

- lem-sfb-point-pullback-derived-hom vs lem-sfb-norm-algcl-internal-hom-base-change: the existing theorem is a scalar-extension isomorphism on bounded constructible complexes over finite-subextension/all-continuous coefficient rings; the new point theorem concerns geometric inverse image of arbitrary unbounded complexes, and the new coherence theorem asserts equality of forward mates without invertibility of scalar comparison.

- lem-sfb-free-parameter-evaluation-coherence vs def-sf-integral-hom-reduction-comparison: the existing node defines Canonical integral internal Hom reduction comparison; the new node proves the relative-free evaluation factorization and simultaneous family/coefficient-mate identities.

- lem-sfb-free-parameter-evaluation-coherence vs def-coef-semilinear-derived-calculus: the existing node defines Ordinary derived semilinear calculus interfaces; the new node proves the relative-free evaluation factorization and simultaneous family/coefficient-mate identities.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sf-coefficient-tensor-curry-normalization: the existing assertion concerns Normalization of coefficient tensor currying; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-pod-point-hom-complex-adjunction: the existing assertion concerns Normalized chain-level Hom adjunction at the point; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sf-scalar-tensor-comparison-transport: the existing assertion concerns Transport of normalized scalar tensor comparison; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs def-sf-coefficient-duality: the existing node defines Coefficient duality and bounded finite-cohomology complexes; the new node proves the relative-free evaluation factorization and simultaneous family/coefficient-mate identities.

- lem-sfb-free-parameter-evaluation-coherence vs lem-pod-point-tensor-hom-evaluation: the existing assertion concerns The normalized Hom comparison intertwines signed evaluation; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-pod-module-hom-signed-evaluation: the existing assertion concerns Signed evaluation for ordinary module Hom complexes; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-pod-point-sheaf-hom-maps: the existing assertion concerns Sheaf evaluation and sections-tensor maps for the point model; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-coef-semilinear-operations-existence: the existing assertion concerns Geometric and coefficient operations on a fixed semilinear system calculus; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-coef-semilinear-system-existence: the existing assertion concerns Ordinary semilinear system calculus and cartesian internal Hom; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sf-coefficient-cochain-tensor-curry: the existing assertion concerns Componentwise coefficient cochain currying; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs def-sf-evaluation-hom-site-comparison: the existing node defines Evaluation-induced derived Hom comparison for the etale-proetale morphism; the new node proves the relative-free evaluation factorization and simultaneous family/coefficient-mate identities.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sc-derived-hom-finite-free-model-aux: the existing assertion concerns Bounded-above finite-free Hom computes derived internal Hom into a bounded-below complex; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sc-derived-single-hom-evaluation: the existing assertion concerns Derived single-source Hom evaluation; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sc-derived-internal-hom-unit-iso: the existing assertion concerns Derived internal Hom from the structure sheaf is the identity; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sc-hom-complex-mapping-cone-differential: the existing assertion concerns Differential compatibility of the internal Hom cone comparison; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sc-hom-complex-unit-iso: the existing assertion concerns Hom complex from the structure sheaf is the identity; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sc-hom-complex-mapping-cone: the existing assertion concerns Internal Hom complexes commute with mapping cones; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sc-derived-internal-hom-single-comparison: the existing assertion concerns Unary internal Hom derives to internal RHom from a degree-zero module; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sfb-derived-internal-hom-sections-model: the existing assertion concerns Derived internal Hom into a K-injective and its derived global sections; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sfb-free-representable-derived-functions-model: the existing theorem is for M[0], bounded-below injective resolutions and sheafified derived presheaf sections; the new slice theorem supplies p_X^{-1}h_P=h_{X[P]}, internal coefficients and a normalized isomorphism with actual slice Rrho_*rho^* for arbitrary unbounded K.

- lem-sfb-free-parameter-evaluation-coherence vs lem-weil-pbc-ringed-completion-unit-naturality: the existing assertion concerns Naturality of the actual derived completion unit; it does not assert the forward free-profinite projection comparison with both variable-parameter whole-family substitution and a nonflat coefficient-mate square.

- lem-sfb-free-parameter-evaluation-coherence vs def-weil-pbc-ringed-completion-unit: the existing node defines RingedCompletionUnit; the new node proves the relative-free evaluation factorization and simultaneous family/coefficient-mate identities.

- lem-sfb-free-parameter-evaluation-coherence vs def-pur-derived-internal-hom: the existing node defines Derived internal Hom on a ringed site; the new node proves the relative-free evaluation factorization and simultaneous family/coefficient-mate identities.

- lem-sfb-free-parameter-evaluation-coherence vs lem-weil-pbc-ringed-slice-evaluation-transpose: the existing theorem concerns tensor/Hom transposes under a fixed slice restriction; the new coherence theorem includes the relative-free projection comparison, arbitrary variable parameter maps on X[Q] and a coefficient-changing direct-image mate square.

- lem-sfb-free-parameter-evaluation-coherence vs lem-coef-monoidal-square-hom-transport: the existing theorem concerns Hom comparisons through a square of strong monoidal functors; the new coherence theorem includes projection adjuncts, free-generator evaluation and varying parameter objects, with derived coefficient extension rather than an assumption that restriction is strong monoidal.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sfb-norm-algcl-internal-hom-base-change: the existing theorem is a scalar-extension isomorphism on bounded constructible complexes over finite-subextension/all-continuous coefficient rings; the new point theorem concerns geometric inverse image of arbitrary unbounded complexes, and the new coherence theorem asserts equality of forward mates without invertibility of scalar comparison.

- lem-sfb-free-parameter-evaluation-coherence vs lem-sfb-slice-scalar-hom-chain-adjunction: the existing theorem gives the chain extension/restriction Hom adjunction; the new coherence theorem identifies forward relative-profinite evaluation comparisons and their entire family/scalar squares in the unbounded derived category.

- lem-sfb-free-parameter-evaluation-coherence vs def-sfb-derived-profinite-evaluation: the existing node defines Canonical derived evaluation for profinite internal functions; the new node proves the relative-free evaluation factorization and simultaneous family/coefficient-mate identities.


## Outstanding work

The three new nodes are deliberately unsplit, with the full retained argument allocated above. Their later stage-1 proofs and all Lean work are outside this repair. No mathematical clause of the assigned item is left unassigned. Delivery and server preflight results are recorded by the required delivery command.
