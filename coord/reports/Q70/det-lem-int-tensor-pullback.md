## Worker report

Human-directed re-split of det-lem-int-tensor-pullback, Q70, 2026-10-21. This is the explicit repair assignment of 2026-10-21, not an attempt to supersede a reviewed item without authorization. The statement, statement dependencies, blueprint import fields, reviewed fields and Lean record are retained. There was no earlier sandbox split or report to recover. No Lean was written, no compiler was run, and no repository or launcher file was changed.

## Files written

- dag/nodes/sec-six-functors-basics/det-lem-int-tensor-pullback.json: item, split, five assembly steps, 2061 characters of proof text.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-bounded-stratum-base-change.json: statement, unsplit, no Mathlib match. This separates the two adjunction/cone arguments for ambient bounded complexes and their composite on stratum extensions.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-pullback-strict-roos-normalization.json: statement, unsplit, no Mathlib match. This separates the simultaneous strict quotient diagram, coefficient actions, K-flat scalar restriction, and both coordinates of the cochain Roos comparison, including its actual unit.

The two work items have comparable argument sizes: old steps 3--4 comprise 1905 characters; old steps 8--9 comprise 1874 characters. The latter interface makes the concrete cochain work, already present in the owning Lean module, explicit rather than hiding it in an appeal to an abstract isomorphism in a derived category. Both new files have empty proof/proof_deps, null proof_origin and mathlib_match, status unsplit, and complete blueprint origins. No proof sketch is placed inside either statement.

## Attachments

None. A project-wide search under lean/WeilConjectures for the exact blueprint tag has no hit. I also searched the integral/pro-etale source by concept. The owning module lean/Sheaf/Paper/IntegralTensorPullback.lean has the matching declaration AlgebraicGeometry.ProEtale.IntegralTensorPullback.preserves_and_completed (line 367), but its proof ends in sorry (line 394). Its helper augmentation_condition, towerUnit_compatible, constantTowerUnit_compatible and restrictionPullback_existsUnique are also sorry. These are evidence of the required interfaces, not completed attachments. The Mathlib hits are building blocks only.

## WANTED

None. All source material used here is present in the read clone.

## What was wrong and what changed

The mathematics and the two clauses of the existing item are retained. The human identified its 7429-character proof as too much for one worker. This repair exposes two genuinely independent arguments. Existing scalar-model pullback and scalar-matrix nodes already carry the old finite-presentation argument, so creating another node for it would duplicate the DAG. The five-step parent is a finite-stratum assembly: exact pullback and scalar presentations; generators and the new ambient immersion exchange; finite-extension dévissage; completeness and the new unit comparison; constant-category interpretation. The existing integral-model criterion is used only through clauses (1),(2), never its pullback preservation clause (3), so the proof does not become circular or bypass the assigned unit route.

No STATEMENT-DISPUTED finding and no source correction. No work remains unfinished in this one-level split: the two new unsplit statements are deliberately left to other workers. The unit record is not edited, since this item is only the inverse-image component of the four-part unit, not its key statement.

## Sources and division of arguments

I read the complete current main-20261015 blueprint statement and proof for det-lem-int-tensor-pullback, the chapter sec-six-functors-basics, and all four steps of unit sk-lem-int-tensor. This realizes unit step 2, retaining its reference to the generator/dévissage theorem from step 1. It changes neither the chapter nor the unit route.

For the bounded stratum lemma I read Stacks proetale.tex: 09AA, lemma-closed-immersion; 09BM, lemma-closed-immersion-complement-retrocompact-exact; 09BN, lemma-open-immersion; 09AH, lemma-ses-associated-to-open. These give the full-faithfulness/restriction identities, exactness under a retrocompact complement, and the localization sequence. The new statement is the adjunction-normalized bounded base-change consequence, not a claim that 09AH itself states base change. The original detailed proof is preserved below. No use of proper base change, finite coefficients, or the restricted constructible functors enters this argument.

For the strict normalization lemma I read Stacks algebraization.tex 099I, lemma-restriction-derived-complete-equivalence, and proetale.tex 099L (section-derived-completion-noetherian), 099M (lemma-naive-completion), and 099N (lemma-pushforward-Noetherian-case), especially (2),(5) and the proof of (5). I read IntegralTensorPullback.lean lines 62--330, including the actual quotient steps, the zero-homotopy augmentation, the constant-function coefficient map and the normalized restriction-pullback isomorphism. The new statement is an explicit cochain refinement of the first and last blueprint paragraphs. It asserts no completeness or constructibility conclusion for an arbitrary complex. Consequently it is strictly a tool, not a new name for either clause of the item.

An implementing worker for the second lemma must verify the constant-function map is a ring map; identify its finite quotients; and prove scalar restriction of a flat-term K-flat complex remains flat-term K-flat. For the last assertion: the completed coefficient ring is flat over the constant one, so extension of an acyclic constant-coefficient complex remains acyclic. Associating its tensor with P identifies that tensor with the tensor against Res(P), which is therefore acyclic. Termwise flatness follows by composing the two exact tensor functors. The tensor/pullback comparisons must be the specified balanced quotient maps, so all quotient transitions and augmentations agree before localization. For the Roos map apply the canonical product comparison in each of the two cone coordinates; their commutation with 1-s proves the chain-map equation, and the quotient maps in the unshifted coordinate and zero in the shifted coordinate give exactly the two unit equations. This preserves the argument of old steps 8--9 and makes its representative-level obligations available to a separate worker. The proof of the new node is not being marked complete.

## Search record and existing nodes reused

Every new-node Mathlib query was run with the prescribed msearch.py command; searches.jsonl is the unmodified automatic log. The JSON search records have the exact tool and query strings, actual returned names and verdicts. Both new nodes have LeanSearch, LeanFinder, Loogle and grep, with a second phrasing. There were no unavailable services. For bounded base change, LeanFinder found scheme-structure-sheaf restriction isomorphisms (Mathlib/AlgebraicGeometry/Modules/Sheaf.lean, restrictFunctorIsoPullback at 453), not pro-etale condensed integral ambient base change; the grep hit GuitartExact/KanExtension.lean:166 is a Kan-extension natural transformation, not this theorem. The second grep found only stability of scheme morphism properties. For strict normalization, LeanFinder found flat tensor exactness and algebraic adic completions; LeanSearch found ordinary pullbacks and scalar restriction. Loogle found CochainComplex.mappingCocone and its lift constructors (MappingCocone.lean:33,282), and ModuleCat.restrictScalars (ChangeOfRings.lean:85). These do not identify these coefficient systems, quotient diagrams and units in one-line specializations. Grep returned no strict reduction/Roos comparison. I read the displayed signatures and the relevant local source definitions. No Mathlib leaf is asserted.

Before writing, I searched the whole DAG by tags 09AA/09AH/09BN/09BM and 099I/099M/099N, and by base change, local models, scalar matrices, reduction towers, restriction and Roos. I ran blueprint_refs.py ancestor, and whole-blueprint searches for base change, locally closed, local models, completed inverse image, reduction tower, finite reduction, Roos, scalar restriction, restriction of scalars, closed direct image, strict quotient and completion unit. No existing blueprint node states either new interface. The parent's same_as det-sfb-dc-restricted-functors-completed-pullback remains correct; it concerns the whole theorem, not either tool.

The existing lem-sfb-pullback-constant-model-constructible gives precisely the same scalar modules on base-changed strata/covers; lem-sfb-scalar-matrix-inverse-image gives preservation of each scalar differential and cokernel. They replace creation of another finite-presentation pullback node. lem-sfb-proetale-fp-local-models-pullback instead uses discrete constant coefficients. lem-sfb-local-integral-perfect-model-cohomology instead concerns restriction by an immersion and cohomology of a supplied perfect scalar model.

I read lem-weil-pbc-pulled-reduction-strict-tower-comparison, which supplies the abstract strict-derived-tower comparison and unit, and lem-weil-pbc-constant-completion-equivalence, which supplies flatness, finite comparisons and derived-limit compatibility. They are relevant tools for the second new worker. They do not specify the isomorphism of the fixed cochain Roos models of IntegralTensorPullback.lean with its product coordinates, the normalized chain map d, and both chain-level equalities for every flat-term K-flat P. I also checked lem-pur-roos-additive-comparison: it conditionally compares Roos cones for an additive product-preserving functor, and has no coefficient, K-flat or completion-unit assertion. Those ingredients alone do not establish the new lemma by a one-line specialization. Likewise the restricted thm-sfb-dc-open-base-change-iso applies only on constructible subcategories; using it here would presuppose the preservation under construction.

## Review by Q70

I checked the new statement of bounded stratum base change against the source identities and the old steps 3--4: all schemes and fibre products remain separated finite-type k-schemes, hence Noetherian. Thus each complementary open is quasi-compact and each closed direct image in the calculation is exact. Inputs are bounded ambient complexes, so the cone is bounded and the cited D+ localization triangle applies. The adjoint defining beta uses the invertible open unit; gamma uses the closed unit followed by the counit i^*i_* = id. The order on a=i u is important: its extension is i_*u_!, and the composite from the base-changed extension to h^*a_! first uses beta inside i'_*, then gamma inverse. I checked the normalized restrictions are identity or zero, so these really are the maps whose cones are tested. This is two separate adjunction calculations and their composition, not an elementary two-line statement or one clause of the parent.

For strict normalization, I kept C_T and R_T distinct throughout, and specified the constant-function map. I checked the tensor comparisons have the right orientation: theta has source Res_X T and target V, hence uses the inverse of Res(P) tensor_C A_n -> P tensor_R A_n after the normalized source comparison d. I included K-flatness over the constant coefficient sheaf, which is needed to compute the constant derived reduction using Res(P). I defined the cochain cone and its sign explicitly. No arbitrary choice of a cone arrow is permitted: both Roos coordinates are prescribed. The statement says these actual chain comparisons localize to the canonical tower comparisons; it does not infer equality of maps merely from equality of the endpoints in a derived category. No inverse-image/product commutation is used: products are compared only for restriction of scalars, after inverse image has been applied levelwise.

Parent step 1 uses the exactness assertion at the end of sk-prop-sfb-cartesian-coefficients and the actual derived-pullback definition. Exactness applied to kernels and images proves the cohomology equality and preserves bounds; termwise cones prove triangle preservation. The full statement of lem-sfb-pullback-constant-model-constructible supplies the base-changed finite stratification, covers and identical scalar modules, so this is not an appeal to the proof of a definition. Step 2 uses the new lemma's last natural isomorphism on bounded M, the two exact clauses of det-lem-int-tensor-shriek, the cartesian coefficient isomorphism, and the matrix intertwining equality in lem-sfb-scalar-matrix-inverse-image. Its reference to Dbc uses the constructible-cohomology definition in sk-def-sfb-constructible. Together these give exactly the membership of each generator, without an assumption on arbitrary inverse image preserving products.

Parent step 3 uses sk-lem-int-integral-heart clause (1), whose statement makes Dbc triangulated, and the full two-out-of-three generation assertion of det-lem-int-tensor-shriek clause (2), not just a vague assertion of generation. Thus the finite-stratum route is explicit. Step 4 uses only sk-lem-integral-models clause (2) in its stated separated finite-type characteristic-p setting and the actual canonical-unit definition of sk-def-pe-derived-completion. The second new lemma then identifies the particular c_K with that unit, including the transitions. Step 5 uses its second chain-level equality, the Res(K) criterion of sk-lem-integral-models (2), and the final paragraph of def-weil-pbc-completed-pullback, which explicitly identifies the same strict tower and unit with Stacks 099N(2),(5). All citations are in citations.json with verbatim excerpts of the opened node statements. The steps' proof_deps are exactly their uses union. No definition node is used to assert an unstated theorem.

Small cases tested for the new interfaces: empty U or Z and empty schemes give zero/identity maps and require no excluded stratum. For h=id, beta and gamma reduce to the normalized restriction identities and the stratum map is identity. For the second node P=0 gives zero towers and zero-coordinate identities. Taking P=R_Y gives its actual coefficient quotients and projection maps; h=id leaves the finite tensor and scalar restriction comparisons with exactly those quotient units. For a shifted scalar complex the differential signs agree with Cone(f)[-1]. For a K-flat resolution [R_Y --pi--> R_Y] of the torsion module A/pi, the reductions have the expected extra degree -1 terms: none is discarded or mistaken for underived reduction. A general noncomplete P is allowed, but the new statement never asserts that its unit is invertible. These checks distinguish the new comparison statement from the parent's constructibility/completeness conclusions.

Self-review B--E: every new object is introduced, definitions are inline or have exact definition dependencies; both new files are statement-only with normal JSON TeX. Source tags and TeX labels were read, not guessed section numbers. Searches were logged by the actual tool. The near-duplicate checks above and below prevent re-creating the known scalar presentation or abstract tower lemma. The parent is an assembly that still proves its two clauses; neither new node asserts either clause. I found no statement correction necessary. I corrected the planned split during review: discarded a prospective duplicate scalar-model lemma in favor of the existing one, combined the two closely related concrete tower comparisons into one independent work item, and explicitly included K-flat scalar restriction and the two cochain coordinates instead of using abstract derived isomorphisms as though they determined a cone map. Every parent step is below 2000 characters; the long-step hidden-lemma rule has no remaining case in the assembly. The full old proof is retained below, with a map of its work, so the repair does not discard an argument to meet the text limit.

## Preservation map for all nine old steps

1. Exact pullback, bounds, cohomology and triangles: parent step 1, cartesian-coefficient node and derived definition; scalar differential part also in the strict normalization node.
2. Finite presentations on pulled-back strata/covers: reused lem-sfb-pullback-constant-model-constructible, whose statement includes the same scalar modules, and lem-sfb-scalar-matrix-inverse-image. Parent steps 1--2 use them.
3. Adjunction-normalized open exchange and vanishing of its bounded cone: first clause of new bounded stratum base-change node.
4. Closed exchange and its bounded cone; factorization into closed and open: second and third clauses of that same new node.
5. Same finite free scalar models and constructible cohomology on the pulled-back generator: parent step 2, step 1, and the scalar-matrix node, followed by new stratum exchange and shriek preservation.
6. Closure under isomorphisms and all three two-out-of-three operations; finite generator argument: parent step 3 with the integral-heart and shriek statements.
7. Apply the existing integral-model criterion on both schemes after constructibility: parent step 4.
8. Naturality of every quotient level, transition and augmentation; actual c_K is the completion unit: the first strict-tower/Roos comparison and its chain-level unit equation in the new normalization node; parent step 4 applies it.
9. Integral coefficient limit, constant scalar action, pullback comparison, finite tensor comparison, strict limit and unit, and Stacks interpretation: second strict-tower/Roos comparison and its chain equality in the new normalization node. Parent step 5 supplies the criterion for Res(K) and the final Stacks interpretation. The integral limit and flat finite comparison are reused in the new node's intended proof, as in the old one, rather than assumed to make the ambient coefficient categories identical.

## Original proof retained verbatim

### Old step 1

Put $R_T=\mathcal O_{E,T}$, $C_T=(\mathcal O_E)_T$ (the discrete constant sheaf), and $A_{n,T}=(\mathcal O_E/\pi_E^n)_T$. The cartesian coefficient statement gives $g^{-1}R_Y\cong R_X$ and $g^{-1}A_{n,Y}\cong A_{n,X}$, and identifies module pullback with the exact functor $g^{-1}$. Thus it is computed termwise on complexes, preserves distinguished triangles (it commutes with shifts and the finite direct sums and differentials defining mapping cones), and $H^q(g^*N)=g^*H^q(N)$: apply the exact functor to kernels and images of the differential. In particular it preserves a given cohomological bound. The module pullback composition isomorphisms will identify restrictions after base change.

Cited nodes: sk-prop-sfb-cartesian-coefficients, sk-def-sfb-module-derived-pushpull, sk-def-sfb-module-pushforward-pullback

### Old step 2

Here is the elementary finite-presentation argument needed for the local models. For a constructible $R_T$-module $F$ on a standing scheme $T$ and a morphism $h:T'\to T$, choose its finite stratification and, on each stratum $S$, a pro-étale covering $W_j\to S$ with presentations $R_{W_j}^{r_j}\xrightarrow{B_j}R_{W_j}^{s_j}\to F|_{W_j}\to0$, where $B_j$ has entries in $\mathcal O_E$. The base-changed strata form a finite stratification of $T'$. The inverse-image construction sends the covering to its base-changed covering. On $W_j\times_TT'$ exact pullback and the cartesian coefficients give the same presentation with the same scalar matrix $B_j$ over $R_{W_j\times_TT'}$. This is a finite constant local model, so $h^*F$ is constructible by its definition. Empty strata are simply discarded.

Cited nodes: sk-def-sfb-constructible, lemma-constructible-pullback-stratification, def-weil-proetale-inverse-image, sk-prop-sfb-cartesian-coefficients, sk-def-sfb-module-pushforward-pullback

### Old step 3

For an open immersion $j:U\hookrightarrow T$ of standing schemes, write $i:Z\hookrightarrow T$ for its closed complement, and let $j':U'\hookrightarrow T'$ and $i':Z'\hookrightarrow T'$ be their base changes by $h:T'\to T$. The schemes are Noetherian, so these opens are quasi-compact as morphisms. Take $N\in D^b(U,R_U)$; this is the case needed for the generators below. Adjunction gives $\beta:j'_!h_U^*N\to h^*j_!N$: its adjoint is $h_U^*N\cong j'^*h^*j_!N$, using pullback composition and $j^*j_!\cong\mathrm{id}$. The adjunction triangle identity makes $j'^*\beta$ the identity under these identifications; $i'^*\beta$ is $0\to0$ by $i^*j_!=0$ and pullback composition. Exactness preserves cohomological bounds, so $C=\operatorname{Cone}(\beta)$ is bounded and the cited $D^+$ localization triangle applies. Its two end terms $j'_!j'^*C$ and $i'_*i'^*C$ are zero, hence $C=0$. Thus $h^*j_!N\cong j'_!h_U^*N$ for these bounded complexes.

Cited nodes: lem-weil-pbc-condensed-open-closed-recollement, lem-weil-pbc-proetale-ringed-open-closed, sk-def-sfb-module-pushforward-pullback

### Old step 4

For the closed immersion in the square of step 3, take $N\in D^b(Z,R_Z)$. The unit for $i'^*\dashv i'_*$ gives $\gamma:h^*i_*N\to i'_*i'^*h^*i_*N\cong i'_*h_Z^*N$. The last identification uses pullback composition and $i^*i_*\cong\mathrm{id}$. The adjunction triangle identity makes $i'^*\gamma$ the identity under these identifications, and $j'^*\gamma$ is $0\to0$ since $j^*i_*=0$. Both $i_*$ and $i'_*$ are exact because their complementary opens are quasi-compact, so $C=\operatorname{Cone}(\gamma)$ is bounded. In its localization triangle $j'_!j'^*C\to C\to i'_*i'^*C\to$, the two end terms vanish, hence $C=0$ and $h^*i_*N\cong i'_*h_Z^*N$. For a locally closed immersion factor $a=i\circ u:S\hookrightarrow\overline S\hookrightarrow T$, with $u$ open and $i$ closed. For bounded $M$ the two calculations give $h^*i_*u_!M\cong i'_*h_{\overline S}^*u_!M\cong i'_*u'_!h_S^*M=a'_!h_S^*M$. All complexes entering these calculations remain bounded by exactness.

Cited nodes: lem-weil-pbc-condensed-open-closed-recollement, lem-weil-pbc-proetale-ringed-open-closed, sk-def-sfb-module-pushforward-pullback

### Old step 5

Consider a generator $a_!M$ supplied by clause (2) of [det-lem-int-tensor-shriek]. Write $S'=S\times_YX$ and $g_S:S'\to S$. On the base-changed local-model covering, $g_S^*M$ is the same bounded finite free scalar complex $P_j\otimes_{\mathcal O_E}R_{W'_j}$, by termwise exact pullback and coefficient compatibility. To check membership without assuming any commutation of arbitrary inverse image with inverse limits, use $M\in\Dbc(S,\mathcal O_E)$: its finitely many nonzero cohomology sheaves are constructible, and the finite-presentation argument of step 2 shows that their pullbacks are constructible. Step 1 gives the same bounds and identifies these with the cohomology of $g_S^*M$. Thus $g_S^*M\in\Dbc(S',\mathcal O_E)$. Clause (1) of [det-lem-int-tensor-shriek] gives $a'_!g_S^*M\in\Dbc(X,\mathcal O_E)$, and steps 3--4 identify this with $g^*a_!M$.

Cited nodes: det-lem-int-tensor-shriek, sk-def-sfb-constructible

### Old step 6

The full subcategory of $\Dbc(Y,\mathcal O_E)$ consisting of $N$ for which $g^*N\in\Dbc(X,\mathcal O_E)$ is closed under isomorphisms and the two-out-of-three operation on distinguished triangles: by clause (1) of [sk-lem-int-integral-heart] applied on both schemes, two vertices in $\Dbc(Y,\mathcal O_E)$ force the third to lie there; $g^*$ takes that triangle to a triangle, and the triangulatedness of $\Dbc(X,\mathcal O_E)$ gives the same conclusion for their pullbacks. It contains every generator of step 5. Clause (2) of [det-lem-int-tensor-shriek] therefore implies that it contains every $K\in\Dbc(Y,\mathcal O_E)$. This proves (1), by the finite-stratum dévissage required by the unit.

Cited nodes: det-lem-int-tensor-shriek, sk-lem-int-integral-heart

### Old step 7

Apply the criterion in clause (2) of [sk-lem-integral-models] to the object $g^*K$ just proved bounded constructible. The scheme $X$ is in its separated finite-type characteristic-$p$ setting, and $E/\mathbf Q_\ell$ is finite with $\ell\ne p$, exactly as required. The same criterion applies to $K$ on $Y$. In particular both $K$ and $g^*K$ are derived $\pi_E$-complete. Consequently its canonical unit $g^*K\to R\varprojlim_n(g^*K\otimes^L_{R_X}A_{n,X})$ is an isomorphism, by [sk-def-pe-derived-completion]. Only the criterion in clause (2) is used here, not the preservation assertion in clause (3).

Cited nodes: sk-lem-integral-models, sk-def-pe-derived-completion

### Old step 8

Derived tensor compatibility for ringed-topos pullback gives natural isomorphisms $g^*(K\otimes^L_{R_Y}A_{n,Y})\cong g^*K\otimes^L_{R_X}A_{n,X}$. Naturality in the second variable makes these commute with $A_{n+1}\to A_n$ and with the quotient maps out of $K$. Use the functorial strict reduction-tower construction of [def-weil-pbc-completed-pullback], not an unspecified cone of unrelated maps. It therefore identifies the displayed unit in step 7 with precisely $c_K$ in the statement, including its transition maps and its map from $g^*K$. Since $g^*=g^{-1}$ on these coefficient modules, its target is the stated $R\varprojlim_ng^{-1}(K\otimes^L A_{n,Y})$. Thus $c_K$ is an isomorphism.

Cited nodes: lem-weil-pbc-ringed-topoi-derived-tensor-pullback, sk-prop-sfb-cartesian-coefficients, def-weil-pbc-completed-pullback

### Old step 9

Finally $R_T\cong\varprojlim_n A_{n,T}$ by [det-prop-sfb-qlbar-colimit-x-integral-limit]. The cartesian coefficient isomorphism in [sk-prop-sfb-cartesian-coefficients] identifies the source $\operatorname{Res}_X(g^*K)$ canonically with $g^{-1}\operatorname{Res}_Y K$: the scalar-extension map is an isomorphism because $g^{-1}R_Y\to R_X$ is one. Restriction of scalars $C_T\to R_T$ has, by [lem-weil-pbc-constant-completion-equivalence], the natural finite-reduction comparison, its compatibility with pullback and quotient transitions, and preservation of the derived limits of these strict towers and their completion units. Hence the restriction of the target of $c_K$ is $R\varprojlim_ng^{-1}(\operatorname{Res}_Y K\otimes^L_{C_Y}A_{n,Y})$, with the same comparison map. By [sk-lem-integral-models] (1),(2), $\operatorname{Res}_Y K$ is an object of the constant-coefficient derived-complete constructible category. The last paragraph of [def-weil-pbc-completed-pullback] identifies exactly this tower and its unit with the Stacks completed inverse image (Tag 099N, proetale-lemma-pushforward-Noetherian-case, clauses (2),(5)). This proves the scalar-restriction assertion in (2).

Cited nodes: det-prop-sfb-qlbar-colimit-x-integral-limit, lem-weil-pbc-constant-completion-equivalence, sk-lem-integral-models, def-weil-pbc-completed-pullback, sk-prop-sfb-cartesian-coefficients

## Not duplicates

lem-sfb-integral-bounded-stratum-base-change vs det-formal-closed-support-ii-left-exact: Existing scope: “Left $t$-exactness of sections with closed support”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-formal-closed-support-ii-limits: Existing scope: “Closed support commutes with derived limits of sequences”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-lem-formal-closed-support-sheaves: Existing scope: “Sections with support: the sheaf-level adjunction”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-lem-int-ext-bound: Existing scope: “Uniform vanishing of Ext between integral constructible sheaves”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-prop-closed-adjoint-constructible-support: Existing scope: “Sections with support of a constructible complex are constructible”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-proper-heart-bound-lattice: Existing scope: “The lattice bound $2d+1$”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-sf-comp-coherence-refinement: Existing scope: “The refinement map on the localizing category”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-sf-comp-composition-base-change: Existing scope: “Base change for $Rf_!$ on the localizing category”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-sf-comp-composition-interchange: Existing scope: “Interchanging proper direct image and extension by zero”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-sfb-dc-restricted-functors-closed-image: Existing scope: “Extension by zero and closed direct image preserve integral constructible complexes”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs det-uniform-constructible-ext-integral: Existing scope: “The integral stratum bound”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-cbc-extension-zero-perfect-model-transport: Existing scope: “Transport a single local completed constant model across open extension by zero”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-cbc-extension-zero-stratified-perfect: Existing scope: “Extension by zero preserves stratified perfect local models”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-exc-etale-origin-open-restriction-transport: Existing scope: “Canonical comparison preserves normalized derived open restriction”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-exc-proetale-cartesian-open-injective-acyclic: Existing scope: “Proper acyclicity of injectives extended from an arbitrary Cartesian open”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-exc-proetale-derived-open-restriction: Existing scope: “Unbounded pro-etale direct image commutes with open restriction”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-exc-proetale-proper-open-sheaf-comparison: Existing scope: “Proper/open comparison for pro-etale module sheaves”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-formal-closed-pullback-derived-products: Existing scope: “Closed coefficient-compatible pullback preserves derived products”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-pur-closed-support-exceptional-comparison: Existing scope: “Comparison of closed support with the transported finite exceptional value”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-pur-proetale-open-unit-evaluation: Existing scope: “Canonical open pro-etale pullback evaluation and its unit”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sf-open-finite-constructibility-interval: Existing scope: “Open extension preserves finite constructibility and its cohomological interval”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sf-proetale-open-closed-sequence: Existing scope: “Open-closed short exact sequence on the pro-etale site”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sf-ring-sheaf-closed-localization: Existing scope: “Closed localization for arbitrary pro-etale ring-sheaf module objects”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sf-ringed-closed-kernel-adjoint: Existing scope: “The support-kernel adjoint for an arbitrary pro-etale ring sheaf”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sf-ringed-open-roos-preservation: Existing scope: “Ringed pro-etale open extension preserves products and Roos triangles”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-closed-support-bounded-continuity: Existing scope: “Bounded-below continuity for open direct image and closed support”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-closed-supported-scalar-comparison: Existing scope: “Supported closed-unit construction and normalization of scalar comparison”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-condensed-support-derived-localization: Existing scope: “Open/closed localization for ordinary derived condensed module objects”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-condensed-support-projection-formula: Existing scope: “Natural support tensor projection formulas on unbounded condensed modules”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-exact-open-closed-unbounded-calculus: Existing scope: “Unbounded support calculus from exact abelian open/closed localization data”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-local-integral-perfect-model-cohomology: Existing scope: “Cohomology of a local integral perfect scalar model”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-locally-closed-extension-coherence: Existing scope: “Restriction and composition for locally closed extension by zero”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-locally-closed-module-extension-coherence: Existing module-sheaf extension/composition coherence has no arbitrary h base-change assertion; the new lemma constructs and proves the normalized bounded ambient exchanges.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-normalized-immersion-comparison-coherence: Existing coherence is conditional on already supplied comparisons on the same scheme; the new lemma supplies geometric base-change isomorphisms across arbitrary h.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-open-closed-flatness: Existing scope: “Flatness detected on a complementary open and closed pair”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-open-filtration-successor: Existing scope: “Natural quotient for two nested open module pieces”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-proetale-fixed-scalar-zero-detection: Existing scope: “Complementary restrictions detect zero fixed-scalar pro-etale sheaves”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-proetale-identified-open-closed: Existing scope: “Exact open and closed extensions with identified inverse-image coefficients”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-proetale-identified-supported-reconstruction: Existing scope: “Normalized supported reconstruction for actual tensor pullbacks”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-proetale-locally-closed-extension: Existing scope: “Pointwise exact locally closed extension”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-proetale-open-disjoint-direct-image: Existing scope: “Direct image restricts to zero on a disjoint pro-etale open”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-sfb-proetale-supported-reconstruction: Existing scope: “Normalized reconstruction from two successive support conditions”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-condensed-open-closed-recollement: Existing scope: “Open/closed recollement for condensed coefficient modules”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-integral-model-open-closed-pieces: Existing scope: “Integral open and closed pieces remain constructible and rationalize to the localization sequence”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-noetherian-stratum-detection: Existing scope: “Finite stratified restrictions detect pro-etale sheaves”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-proetale-abelian-closed-counit: Existing scope: “The closed counit on abelian pro-etale sheaves”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-proetale-abelian-closed-support: Existing scope: “Closed support for abelian pro-etale sheaves”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-proetale-immersion-limit-preservation: Existing scope: “Inverse images along immersions preserve pro-etale limits”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-proetale-inverse-image-limits-zariski-local: Existing scope: “Zariski locality of preservation of pro-etale inverse-image limits”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-proetale-restriction-preserves-limits: Existing scope: “Limits preserved by weakly etale pro-etale restriction”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-proetale-ringed-closed-counit: Existing scope: “Closed ringed counit is invertible”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-proetale-ringed-localization-sequence: Existing scope: “Ringed local open-closed short exact sequence”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-proetale-ringed-open-closed: Existing scope: “Ringed pro-etale open-closed localization”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-proetale-ringed-open-comparison: Existing scope: “Arbitrary-coefficient open localization”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs lem-weil-pbc-wcontractible-closed-localization: Existing scope: “Closed localization of a w-contractible ring”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs new-lem-weil-pbc-condensed-finite-model-immersion-restriction: Existing scope: “finite model on immersion range”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: Existing scope: “condensedSurjectiveClosedPullback isEquivalence”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs new-lem-weil-pbc-condensed-surjective-closed-local-presentation: Existing scope: “lfp lowerStar of surjective closed”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs sk-lem-formal-closed-support-ii: Existing scope: “Closed support, truncation and derived limits”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs sk-lem-int-ext: Existing scope: “Continuity and boundedness of Ext”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs sk-lem-int-tensor: Existing scope: “Inverse image and tensor product”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs sk-lem-proper-heart-bound: Existing scope: “A uniform bound for proper direct image”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs sk-lem-uniform-constructible-ext: Existing scope: “Uniform Ext bound”; new scope: the normalized ambient bounded cartesian open/closed exchange maps across an arbitrary scheme morphism. The existing statement does not supply this geometric exchange.

lem-sfb-integral-bounded-stratum-base-change vs thm-sfb-dc-open-base-change-iso: The existing theorem is on restricted constructible functors, while the new statement is ambient D^b on arbitrary bounded integral inputs and also supplies closed and composite stratum exchanges.

lem-sfb-integral-pullback-strict-roos-normalization vs def-a1-integral-completed-pullback-interfaces: Existing scope: “Projection-normalized completed coefficient transport and finite pullback evaluation interfaces”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-derived-cochain-comparison-factors: Existing scope: “Localization comparison for an additive functor on complexes”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-derived-cochain-counit: Existing scope: “Derived counit on complex localization”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-derived-cochain-right-unit: Existing scope: “Derived unit on complex localization”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-derived-exact-equivalence-square-data: Existing scope: “Data of compatible exact-equivalence derived squares”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-pur-completed-coefficient-presentation-transport: Existing scope: “Normalized tensor comparison between completed coefficient presentations”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-pur-integral-derived-operations: Existing scope: “Integral derived pullback, completed tensor product and internal Hom”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-sf-pull-completion-comparison: Existing scope: “Strict quotient normalization of pullback completion”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-sf-tensor-completion-comparison: Existing scope: “Roos normalization of the tensor completion comparison”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-sfb-quotient-kernel-completeness: Existing scope: “Local derived completeness for a ring-sheaf quotient kernel”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-trf-integral-comparison-realization-models: Existing scope: “Normalized realization interfaces for integral quotient systems”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-trf-integral-comparison-sequence-systems: Existing scope: “Canonical pullback and scalar change of whole quotient systems”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-common-stage-derived-direct-image: Existing scope: “Common-stage derived direct image and induced Weil adjunction”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-adic-coefficient-datum: Existing scope: “Tower category and adic coefficient datum”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-completed-base-change-map: Existing scope: “Completed base-change map”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-completed-constant-presentation-data: Existing scope: “Common constant presentation of the two completion objects”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-completed-pullback: Existing node defines a strict derived-tower functor and its unit; new node is a theorem about the explicitly prescribed cochain reduction, source and two Roos product-coordinate maps, including scalar-restricted K-flatness.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-completed-quotient-completion-unit: Existing scope: “Bundled specified completed quotient-completion unit”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-completed-quotient-ordinary-unit: Existing scope: “Ordinary completed quotient-limit unit”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-four-corners: Existing scope: “Four finite-level corners”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-intrinsic-completion: Existing scope: “Intrinsic derived completion”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-ringed-scalar-extension-complex-adjunction: Existing scope: “Termwise scalar-extension adjunction on ringed-site complexes”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-weil-pbc-ringed-site-ideal: Existing scope: “Ideal subsheaves on a ringed site and extension of ideals”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs def-zl-field-weil-shriek-shift-data: Existing scope: “Canonical field-coefficient Weil compact support and shift data”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs det-lem-int-integral-heart-local-model: Existing scope: “Local models of integral constructible complexes and their cohomology”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs det-lem-int-tensor-pullback: The parent proves constructible preservation and invertibility of c_K; new lemma assumes neither constructibility nor completeness and proves only a strict cochain diagram comparison, whose augmentation need not be invertible.

lem-sfb-integral-pullback-strict-roos-normalization vs det-prop-diagonal-tower-limit: Existing scope: “The $\ell$-adic diagonal class over the completed coefficient sheaf”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs det-prop-diagonal-tower-system: Existing scope: “The torsion diagonal classes as one morphism of inverse systems”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs det-thm-sf-pf-adic-projection: Existing scope: “The integral proper projection formula”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-a1-integral-pullback-completed-comparison: Existing scope: “The integral derived pullback agrees with the strict-tower completed pullback”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-cbc-completed-pullback-triangles: Existing scope: “Completed pullback preserves shifts and distinguished triangles”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-constant-completion-unit-normalization: Existing scope: “Constant quotient completion unit on every complex”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-derived-exact-equivalence-squares: Existing scope: “Compatible derived squares under exact equivalences”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-fix-residue-lisse-projective-models: Existing scope: “Projective sheaf models from lisse residue cohomology on a weakly contractible affine”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-pod-integral-pullback-composition: Existing scope: “Composition isomorphism for integral derived pullbacks”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-pod-integral-pullback-system-comparison: Existing scope: “For every morphism f:X→Y of schemes with ell invertible, the actual constructible completed integral pullback followed by coherent system reduction is naturally isomorphic to coherent system reduction followed by exact finite-system inverse image”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-pod-integral-system-pullback-lift-associativity: Existing scope: “Associativity of a fixed fully faithful integral pullback lift”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-pod-integral-system-reduction-fully-faithful: Existing scope: “Coherent reduction is fully faithful on the full category of derived-complete bounded constructible integral coefficient objects”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-pur-completed-coefficient-pushforward-comparison: Existing scope: “Completed-coefficient pushforward restriction and strict reduction towers”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-pur-integral-operation-roos-effectivity: Existing scope: “Effectivity of the strict finite-operation Roos towers”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-pur-ordinary-adjunction-scalar-compatibility: Existing scope: “Scalar compatibility of the ordinary completed adjunction”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-pur-roos-additive-comparison: Existing statement is conditional additive/product-preserving Roos coherence; new statement includes the integral/constant coefficient square, finite reduction maps, K-flatness and their specific augmentation equations.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sbc-completed-operations-linear-natural-exchange: Existing scope: “Linearity and naturality of completed pullback, direct image, and exchange”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sbc-reflected-compositor-unit-normalization: Existing scope: “Compatibility of a reflected composition isomorphism with completion units”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-cbc-compact-support-composition-limit: Existing scope: “Normalized reconstruction of composites of completed operations”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-cbc-extension-zero-completion: Existing scope: “Strict reduction of completed extension by zero”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-coherent-rational-pullback-identity: Existing scope: “Scalar-compatible identity pullback comparisons at rational stages”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-common-stage-pullback-identity: Existing scope: “Identity comparison for common-stage derived pullback”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-complete-residue-cohomology-bounds: Existing scope: “Cohomological bounds for a complete complex from residue Tor amplitude”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-completion-finite-reduction: Existing scope: “Finite reduction inverts the completion unit”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-completion-unit-finite-projection: Existing scope: “Projection of the completion unit is the finite scalar-extension unit”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-integral-pullback-linear-adjunction: Existing scope: “Integral constructible pullback has a coefficient-linear right adjoint”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-quotient-tower-evaluation-complex: Existing scope: “Explicit finite evaluation of a quotient-tower complex”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sf-reduction-pull-finite-evaluation: Existing scope: “Finite evaluation respects the specified reduction/pullback comparison”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sfb-adic-complete-reduction-cone: Existing scope: “Normalized quotient homotopy-limit cone for a complete object”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sfb-adic-complete-residue-conservative: Existing scope: “Residue reduction is conservative on locally complete objects”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sfb-adic-stratum-completion-unit: Existing scope: “Restriction of the completion unit to strata and covering slices”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sp-completed-pullback-adjunction: Existing scope: “Completed pullback is left adjoint to direct image”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-sp-completion-mate-comparison: Existing scope: “The strict quotient-tower exchange realizes the completed-adjunction mate”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-trf-integral-pullback-comparison-realization: Existing scope: “Strict-system realization and composition coherence of integral pullback comparisons”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-bilinear-hom-complex: Existing scope: “Product Hom complexes for an additive coefficient bifunctor”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-coefficient-hom-augmentation: Existing scope: “Natural coefficient-Hom augmentation and its restriction identity”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-completed-constant-coefficient-equivalence: Existing scope: “Scalar and strict quotient compatibility of the completed coefficient equivalence”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-completed-constant-presentation-transport: Existing scope: “Joint transport of the completed quotient and Koszul presentations”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-completed-koszul-constant-transport: Existing scope: “Koszul completion under a scalar-preserving completed coefficient isomorphism”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-completed-koszul-quotient-comparison: Existing scope: “Unit-compatible Koszul-to-quotient comparison in the completed coefficient presentation”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-completed-koszul-quotient-roos-augmentation: Existing scope: “The completed strict Koszul quotient augmentation on Roos models”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-completed-koszul-reduction-roos-triangle: Existing scope: “Normalized quotient Roos triangle on explicit Koszul completion”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-completed-quotient-unit-normalization: Existing scope: “Actual completed quotient unit on a K-flat complex”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-constant-completion-equivalence: Existing statement gives abstract finite derived comparisons, derived limits and completion units; new statement fixes actual cochain towers for every flat-term K-flat P, proves restricted K-flatness and prescribes both coordinates of L_P,E_P and the chain source comparison d.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-finite-reduction-reconstruction: Existing scope: “Finite reduction of reconstruction”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-flat-constant-tensor-pro-zero-cones: Existing scope: “Flat constant extension and K-flat tensor of pro-zero cone towers”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-flat-ringed-cech-base-change: Existing scope: “Flat scalar extension of a global augmented Cech model”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-flat-ringed-cech-base-change-quasi-iso: Existing scope: “Quasi-isomorphism of flat ringed Cech base-change data”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-flat-ringed-cech-local-unit-comparison: Existing scope: “Scalar-extension unit comparison on a finite generating slice”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-flat-ringed-ideal-complete-equivalence: Existing scope: “Flat ringed complete equivalence”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-intrinsic-to-tower-complete: Existing scope: “Intrinsic completeness implies quotient-tower completeness”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-koszul-localization-assembly: Existing scope: “Localization assembly for the Koszul comparison”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-levelwise-isomorphism-cones: Existing scope: “Levelwise isomorphisms and complete cones”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-ordered-exchange-coefficient-comparison: Existing scope: “Coefficient normalization of the raw ordered completed exchange”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-pulled-reduction-strict-tower-comparison: Existing tau and rho are comparisons in derived categories on compatible replacements; new statement fixes the particular cochain models and normalized d of the owning Lean module, including K-flatness and both coordinatewise chain equalities.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-reconstruction-uniform-tower: Existing scope: “Reconstruction of a uniform local tower”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-restricted-coefficient-hom: Existing scope: “Functorial coefficient action on restricted internal Hom”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-restricted-coefficient-hom-complex: Existing scope: “The coefficient action on product Hom complexes”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-ringed-ideal-quotient-comparison: Existing scope: “Quotient criterion for the scalar-extension unit of an ideal subsheaf”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lem-weil-pbc-tower-compatibility: Existing scope: “Compatibility with the coefficient tower”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lemma-weil-pbc-completed-exchange-coherence: Existing scope: “Completed exchange coherence”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lemma-weil-pbc-completed-map-reduction: Existing scope: “Finite reduction of the completed map”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs lemma-weil-pbc-completed-pullback-reduction: Existing scope: “Reduction commutes with completed pullback”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs prop-weil-pbc-direct-image-limits: Existing scope: “Direct image, derived limits, and completeness”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs prop-weil-pbc-koszul-reconstruction: Existing scope: “Koszul and quotient reconstruction”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs prop-weil-pbc-koszul-reconstruction-comparison: Existing scope: “Comparison of completed Koszul and quotient derived limits”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs prop-weil-pbc-levelwise-truncations: Existing scope: “Levelwise truncations of the adic tower”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs sk-lem-int-integral-heart: Existing scope: “Structure of integral constructible complexes”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs sk-thm-sf-pf-adic: Existing scope: “Open direct image and projection formula”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

lem-sfb-integral-pullback-strict-roos-normalization vs thm-weil-pbc-complete-proetale: Existing scope: “Complete pro-etale proper base change”; new scope: the fixed-representative integral/constant cochain tower and both Roos coordinates, with chain-level augmentation equalities and K-flat restriction. The existing statement does not prescribe this fixed cochain comparison.

## Validation

Server review_split passed. Server check_dag reported no finding introduced by the sandbox or on its nodes; the two scalar-presentation tools are explicitly declared in split_report.tool_uses. The first required deliver.py --no-push exited successfully with OK at b8e5874884c, preflight passed. Local source-only validation found unchanged statement/Lean record, proof texts of 313, 427, 346, 467, 508 characters, exactly the proof dependency union, and all 16 verbatim citation quotes. A final dry run of this finalized report and the clarified identity normalization of d is run before the delivery push.
