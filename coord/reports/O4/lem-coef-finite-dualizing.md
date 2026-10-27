# Repair: lem-coef-finite-dualizing

## Worker report

Files written: `dag/nodes/sec-six-functors/lem-coef-finite-dualizing.json` (item, statement unchanged; short assembly) and the following eleven statement-only nodes. All eleven have status `unsplit`, empty proof/proof_deps, and no Mathlib match. No Lean file is written or compiled.

- `lem-coef-dualizing-construction`: statement; no Mathlib match — Bounded etale dualizing objects and their coefficient counit mates.
- `lem-coef-dualizing-affine-space`: statement; no Mathlib match — Invertibility of the counit-defined affine-space coefficient mate.
- `lem-coef-dualizing-closed-chart`: statement; no Mathlib match — Affine closed charts with exact pushforward and normalized dualizing composition.
- `lem-coef-dualizing-closed-site`: statement; no Mathlib match — Bounded site transport of closed exceptional Tate objects.
- `lem-coef-dualizing-closed-descent`: statement; no Mathlib match — Descent of the closed exceptional coefficient mate to the etale site.
- `lem-coef-dualizing-closed-assembly`: statement; no Mathlib match — Identification of the affine structural mate by composite counits.
- `lem-coef-dualizing-open-adjoint`: statement; no Mathlib match — Open structural adjunction with normalized composite counit.
- `lem-coef-dualizing-open-tensor`: statement; no Mathlib match — Open coefficient tensor respects evaluation and finite Tor bounds.
- `lem-coef-dualizing-open-mate`: statement; no Mathlib match — Restriction of a counit-defined structural coefficient mate.
- `lem-coef-dualizing-quotient-mates`: statement; no Mathlib match — Cocycle for counit mates of coherent coefficient comparisons.
- `lem-coef-dualizing-site-mates`: statement; no Mathlib match — Site realization of a normalized coefficient counit mate.

Attachments: none. The live `Sheaf.SixFunctors.FiniteDualizing` theorem `WeilConjectures.finiteDualizingCoefficientComparisons` ends in `sorry`; the upstream project-source search found no closed declaration covering the item.

WANTED: none.

The sandbox initially contained only dispatcher markers, no retained node/report/search log. I copied the live node, which already contains the repaired 27-step expansion (the return described 23 earlier steps). This repair preserves that newer expansion rather than discarding its corrections. The copied source and full old proof are preserved below. The old node statement, source record, Lean record, blueprint metadata and other maintainer-owned fields are retained. I compared the source snapshot with current main-20261015: its finite-dualizing statement and affine/closed/open proof agree.

No part of the requested re-split is left unfinished: every argument block is assigned below, except the routine covering detection from old step 25, which remains a written elementary assembly step. This is a stage-1 delivery of statements for subsequent independent proofs, as requested.

## Repair of the return

1. The formerly long proof is divided into eleven separate arguments; none is the whole result. Their statements introduce every scheme, ring, functor and canonical map used.
2. Each new node is statement-only, status unsplit, with source, blueprint origin and the actually executed semantic, Loogle and source searches. Searches and unavailable services are recorded without inventing results.
3. The item keeps its exact statement and has an eight-step assembly of 2351 characters, below 3000. Every new node is cited by the assembly.
4. Every word of the retained expanded arguments and every old equation appears verbatim in the argument handoffs below; no calculation is compressed away. Every old step is assigned, including the newer bounded-below/site transport repairs.
5. No new proof step is long: all parent steps are below 2000 characters, and the new nodes have no proof steps at all.

## Review by O4

I read coord/delivery-errors.md B–E whole, the current and retained blueprint lemma/proof, the unit and chapter records, and the actual cited statements. The route is the original finite etale affine/closed/open route; no SGA source is used. The ordinary small-etale categories are not silently replaced by pro-etale or condensed categories. The new nodes all introduce their objects and use single TeX backslashes; the inherited regular-object and local computations are preserved, not weakened.

Construction and normalization (steps 1–3): I checked the regular constant object has Tor amplitude [0,0], so Verdier preservation applies without assuming coefficient flatness. Noetherian permanence and Nagata apply over the field. The D+ representability argument needs both representing objects bounded below; the new statement explicitly retains that limitation and the composite coefficient formula. Its conclusion does not assert invertibility of u_X.

Affine space (4–6): I read the ordinary finite Tate definition, affine-space adjunction and top-trace statements. Both source and target are the same shifted B-line after reduction. The top trace shows F_B(u_P) invertible and the connected Tate-line lemma detects invertibility; this is more than an object-only purity identification. Affine space is nonempty and connected, including r=0, and the chosen adjoint counit is fixed by its representability comparison.

Closed chart (7–8): The polynomial presentation is a closed immersion of an affine finite-type chart, not a global embedding of X. Exact finite etale direct image extends termwise to the unbounded category and preserves both bounds. Its right adjoint preserves D+ by amplitude zero. The existing boundary-dualizing-composition node supplies the composite normalization, but does not include this polynomial construction, exactness, and explicit bound verification.

Closed site input (9–12): I read the site-comparison unit, closed-counit transport, canonical direct-image mate, and the finite transported exceptional definition. M and I_AM are bounded independently of coefficient change; M_B is a shifted Tate line and I_BM_B is independently bounded. Thus alpha is exactly S I(eta), and all counits are those of the published bounded-below Hom chain. The B-action is verified on the K-flat tensor models, not on a bare derived A-object.

Closed coefficient descent (13–16): I read the two-site coefficient square and the objectwise fully-faithful descent statement. The old formulas (*) and (**) appear in the respective new statements. The pro-etale closed-shriek theorem is used only on that site. All inverse c components at S N and J S M are justified before descent. T N, I_B M_B, i_*T N and T i_*N are bounded for the stated reasons; full faithfulness is invoked only for those Hom sets, not for arbitrary coefficient tensors of D+ objects.

Affine assembly (17–19): I checked the full five-line composite-counit calculation and its arrow types. The formula for c_U cancels c_i at N; naturality uses c_{p,i_*N} without inverting it. Only M, N and the structural coefficient comparison at N require inverses. Thus this statement gives an equality of actual canonical maps under precise hypotheses, not a second isomorphism between the objects.

Open adjoint (20–21): An affine open in a Noetherian scheme is quasi-compact, and its intersections with target affine opens are quasi-compact. It is separated, etale and finite type, so the locality theorem applies. The identity-proper compactification yields the actual exact j_!, and the Hom chain gives its evaluation counit and the displayed pasted structural counit.

Open tensor (22–23): I read Stacks Tag 0GL1, sites-cohomology.tex, lemma-j-shriek-and-tensor, as well as the project open-derived-tensor statement. The B-linear tensor comparison commutes with evaluation on the chain models: inside U the same evaluation, outside U the zero source. Stalk conservativity is used on the image sheaf degreewise. Exact extension by zero preserves the Tor interval via projection; constructibility extends a finite locally closed stratification, adding the zero complement.

Open mate (24): I checked the five-line adjunct computation against the open normalization and tensor/evaluation statements. Every equality uses naturality, the explicit evaluation identity, or the normalized coefficient compositor. The exact u_U is obtained by injectivity of the adjunction bijection. No equality of arbitrary derived maps is deduced just from equality on an open cover.

Quotient mates (26): I separated the formal objectwise cocycle from the specific dualizing clause. The new statement lists all four invertible coefficient components, coherent coefficient functors and coefficient-unit objects N_R. Transposing the composite gives the four-line old calculation. In the parent, the newly proved isomorphism T omega_A ≅ omega_B discharges the fourth component domain, so there is no assumption that B has finite projective dimension over A.

Site mates (27): I generalized only the transported adjunct argument to an arbitrary separated finite-type f with independently bounded finite-Tor images and input N. Its displayed conjugation is correctly typed from Tpro J_A S N to J_B Tpro S N. I read the finite dualizing site comparison and bounded-site transpose statement; their comparisons use the actual site unit. At f=a_X, N=A_s this gives the final realization, and functorial transport preserves the actual counit/cocycle equations.

Parent citation audit, with the exact statements open (the full verbatim statements are also in citations.json):

- Step 1 takes existence, bounded finite-Tor objects and the defining counit equation from construction. It does not assume its conclusion is invertible.
- Step 2 takes an affine closed embedding, exact i_* and the counit-compatible omega identification from closed-chart; affine-space says specifically that the counit-defined u_P is invertible.
- Step 3 takes the independently bounded M,N,M_B,I_BM_B and the specified normalized alpha/delta from closed-site, then the etale isomorphism and its etale counit equation from closed-descent. The latter statement explicitly covers the empty chart.
- Step 4 uses closed-assembly with precisely the two isomorphisms obtained in steps 2–3; its conclusion is v=u_U, rather than only object isomorphism.
- Step 5 uses the normalized open structural counit from open-adjoint, the chain-level evaluation identity and finite-Tor domains from open-tensor, and the literal equality j^*u_X=u_U from open-mate.
- Step 6 is elementary covering detection: exact inverse image preserves kernels/cokernels and cohomology. The sheaf axiom kills the restrictions; the derived localization in the abstract-derived-category statement kills the acyclic cone. No derived morphism is glued.
- Step 7 applies the abstract quotient-mates statement with N_R=R_s. The finite-Tor domain of the fourth component is checked using the already proved invertibility. The existing compact-support coefficient statement explicitly says compatibility with successive reductions.
- Step 8 uses site-mates at the structural morphism and regular input. Its conclusion gives the literal transported transpose and the dualizing-object identification, with preservation of all actual identities.

Edge cases checked: n=m gives the tensor unit and identity mate; h=m or m=n reduces the cocycle to a unit identity. At r=0 affine space is Spec k with identity adjunction and invertible trace. The empty affine chart has zero derived category, unique closed comparison and valid zero counit equation; empty X satisfies covering detection and all identities. Singular/reducible affine Y is allowed since the closed construction uses a polynomial quotient without smoothness. Ramified E is allowed: a power of ell annihilates every finite stage, but B need not be flat over A. In open-tensor, arbitrary finite Tor interval [a,b] is retained over A and over B by the derived associativity test against degree-zero B modules. None of these tests calls for stronger hypotheses on the item.

Corrections made during self-review: the later affine-space, closed-assembly and open-mate statements explicitly assume the finite-Tor domain for their named dualizing objects; the parent discharges it using construction. The abstract quotient lemma lists four local invertibility hypotheses rather than assuming a globally invertible natural coefficient transformation. The old bounded-below site counit and coefficient-square repairs have been retained in full. A final notation reading also expanded S, U, Tpro, t, alpha, delta, both closed counits and the pro-etale coefficient map directly in the closed statements; the source argument is unchanged. No imported statement dispute or target change was found.

## Not duplicates

lem-coef-dualizing-construction vs lem-weil-verdier-preservation-strata: that node gives preservation of Dctf, not the structural regular-object construction, coefficient adjunct and D+ composition normalization.
lem-coef-dualizing-affine-space vs cor-amb-affine-space-adjunction: the existing adjunction identifies objects at one coefficient ring; the new statement proves invertibility of the specified map between two rings using its trace.
lem-coef-dualizing-affine-space vs lem-coef-connected-tate-line-endomorphisms: that node is the scalar detection tool, without structural dualizing mates or normalized affine trace.
lem-coef-dualizing-closed-chart vs lem-weil-boundary-dualizing-composition: the existing node supplies the composite-adjoint normalization for a given factorization; the new statement supplies an affine polynomial closed chart, its exact termwise pushforward and bound checks.
lem-coef-dualizing-closed-chart vs lem-pur-etale-closed-chart-exceptional-preservation: the existing theorem assumes a closed chart and proves preservation; it does not construct the chart or state exact closed direct image and the D+ bound.
lem-coef-dualizing-closed-site vs lem-coef-site-closed-counit-transport: that node assumes IH bounded below; the new statement identifies the closed Tate inputs, proves those domains and finite-Tor properties at both coefficients, and fixes the B-linear tensor comparison.
lem-coef-dualizing-closed-descent vs lem-coef-finite-closed-shriek: that theorem is on the pro-etale site; the new conclusion is an ordinary etale closed coefficient comparison with an explicitly descended etale counit.
lem-coef-dualizing-closed-descent vs lem-coef-fully-faithful-counit-descent: the existing abstract lemma requires a coefficient square, two inverted components and precise full-faithfulness hypotheses; the new geometric statement verifies those hypotheses for the closed Tate input.
lem-coef-dualizing-closed-descent vs lem-sp-et-proet-coefficient-compatibility: that node supplies a square for left functors; it does not descend a closed exceptional right-adjoint coefficient map.
lem-coef-dualizing-closed-assembly vs lem-sf-compact-coefficient-composition: the existing node states the left-functor compositor square; the new conclusion identifies the particular right-adjoint structural map, retaining the non-inverted intermediate component.
lem-coef-dualizing-open-adjoint vs lem-amb-etale-adjoint-locality: the existing canonical natural object isomorphism does not state the chosen identity-proper open compactification or explicit evaluation-normalized structural counit.
lem-coef-dualizing-open-tensor vs lem-pur-etale-open-derived-tensor: the existing tensor isomorphism does not state its B-linear evaluation counit identity or bounded constructible Tor-interval preservation.
lem-coef-dualizing-open-mate vs lem-amb-etale-adjoint-locality: object locality alone does not identify a coefficient counit-mate with its open restriction.
lem-coef-dualizing-quotient-mates vs lem-pur-ringed-coefficient-projection-cocycle: that lemma is for ordinary direct-image projection mates from inverse image adjunction; the new lemma treats arbitrary F_R right-adjoint object mates with only four invertible coefficient components.
lem-coef-dualizing-quotient-mates vs lem-coef-finite-exceptional: that statement is a geometric pro-etale theorem and depends on the item; the new lemma is abstract adjunction algebra without assuming exceptional coefficient compatibility.
lem-coef-dualizing-site-mates vs lem-pur-bounded-site-adjunction-transpose: that node transports a single-ring adjunct; the new statement includes two coefficient stages and explicitly conjugates their coefficient mate, with iterated-coefficient equations.
lem-coef-dualizing-site-mates vs lem-pur-finite-site-counit-projection-transport: that node is single-coefficient counit/projection transport, whereas this conclusion is the displayed two-coefficient exceptional comparison mate.

DAG searches used statements/titles and source keywords across every chapter, not just the item directory; duplicate-searches.json records the complete candidate id sets. Whole-blueprint queries were dualizing, closed exceptional, coefficient counit, open tensor, quotient cocycle, closed embedding, site transport, composite adjunction, and affine space. The potentially relevant imported finite-exceptional theorem depends on this item, so it is not used circularly. Generic existing normalization/descent/tensor nodes are reused as tools in the preserved handoffs, not recreated. `same_as=[]` means no imported blueprint node states each new full statement. Project Lean source searches are retained in lean-source-search.txt.

## Mathlib search review

- lem-coef-dualizing-construction: The hits concern condensed free adjunctions, counits, and generic derived adjunctions; none constructs the ordinary etale dualizing object or proves its constructible finite-Tor bound.
- lem-coef-dualizing-affine-space: The hits concern standard etale ring presentations, algebraic trace, and generic isomorphism/adjunction facts; none proves invertibility of the specified etale affine-space counit mate.
- lem-coef-dualizing-closed-chart: Closed immersion geometry is in Mathlib, but no returned declaration includes exact constant-coefficient small-etale pushforward, its D+ right-adjoint bound, and the specified structural counit comparison.
- lem-coef-dualizing-closed-site: The hits give abstract fully faithful restriction of adjunctions or bounded representatives. They do not identify the finite etale/pro-etale coefficient objects, the actual B-module tensor comparison, and the prescribed closed exceptional counit.
- lem-coef-dualizing-closed-descent: The returned etale forgetful full-faithfulness concerns over-categories of schemes, not derived sheaves. Generic preimageIso does not verify the two coefficient components, normalized square and bounded Hom domains needed here.
- lem-coef-dualizing-closed-assembly: Generic mate and derived-counit lemmas do not identify the specific compact-support coefficient components on an affine closed factorization; the source calculation keeps track of an intermediate component that is not inverted.
- lem-coef-dualizing-open-adjoint: Scheme.Modules restriction adjunctions are for structural O-modules on the Zariski site, not constant finite coefficients on the small etale site, and do not give compact-support structural counits.
- lem-coef-dualizing-open-tensor: The hits concern formally etale tensor products, ordinary algebra, or Tor vanishing for projectives; none is the B-linear derived extension-by-zero comparison with evaluation and constructible finite-Tor bounds.
- lem-coef-dualizing-open-mate: The hits concern O-module restriction or abstract adjunction naturality; none proves that this compact-support counit-defined coefficient mate restricts to the canonical mate on an affine open.
- lem-coef-dualizing-quotient-mates: Read Mathlib/CategoryTheory/Adjunction/Mates.lean: mateEquiv_vcomp/hcomp concern complete natural-transformation squares. Here c is only invertible at the four stated objects, so there is no natural inverse square to specialize; ModuleCat.homEquiv_extendScalarsComp is only the scalar adjunction, not this arbitrary F_R counit-mate cocycle.
- lem-coef-dualizing-site-mates: Read Mates.lean and Adjunction/Restrict.lean. Their generic mate/restriction results do not identify canonical etale/pro-etale coefficient tensor, compact-support and comparison-unit maps. The displayed concrete realization needs the normalized two-site coefficient square.

I read all returned hits in search-results/. The initial broad greps were followed by targeted Sites/CategoryTheory greps. LeanSearch rate-limit responses remain unavailable; both phrasings were run and the second was also sent to LeanFinder. I read the actual mateEquiv_vcomp, mateEquiv_hcomp, mateEquiv_counit and restrictFullyFaithful source statements; none is an exact match or a one-line specialization of these concrete site/coefficient assertions. The quotient-mates statement deliberately allows inverses only at four objects, unlike an inverse natural-transformation square. Zero Mathlib leaves are claimed.

## Argument handoffs (retained proof, verbatim)

These are proof materials for the workers who split the new statement-only nodes. They are intentionally in the report, not proof sketches inside unsplit node statements. Every retained proof text is copied below without shortening. The old step numbers are the 27-step live expansion, newer than the 23-step return.

### lem-coef-dualizing-construction

Original steps: 1, 2, 3.

Retained step 1; cited statements: lem-weil-pbc-finite-type-over-noetherian, thm-nagata-compactification, thm-amb-etale-exceptional-adjoint.

The existence hypotheses are in force. A field is Noetherian since its only ideals are $0$ and itself; hence $s$ is Noetherian. By [lem-weil-pbc-finite-type-over-noetherian], $X$ and all its finite-type affine charts are Noetherian. By [thm-nagata-compactification], the separated finite-type $a_X$ is compactifiable (the one-point affine base is quasi-compact and quasi-separated). Thus [thm-amb-etale-exceptional-adjoint] supplies the ordinary etale adjoints at each of $A,B,C$. No adjoint on arbitrary pro-etale sheaves is used.

Retained step 2; cited statements: lem-weil-verdier-preservation-strata, lem-fix-compact-support-coefficient-change.

The constant coefficient sheaf $A_X$ is bounded constructible and has Tor amplitude $[0,0]$: tensor with $A_X$ is the identity. Apply [lem-weil-verdier-preservation-strata] to $K=A_X$. Its dual is $R\mathcal Hom_A(A_X,\omega_{X,A})=\omega_{X,A}$ by evaluation at $1$, so $\omega_{X,A}$ is bounded constructible of finite Tor amplitude. The same holds for $B$ and $C$. Consequently [lem-fix-compact-support-coefficient-change] applies to $K=\omega_{X,A}$. Write $F_R=F_{X,R}$, $T=T_{A,B}$, and $c=c_{X,A,B}$. The adjunction bijection defines one global map $u_{X,A,B}$ with
$$\varepsilon_{X,B}F_B(u_{X,A,B})=(T\varepsilon_{X,A})c_{\omega_{X,A}}^{-1}.$$
This is exactly the displayed definition and counit assertion; existence of a coefficient comparison for an exceptional adjoint has not been assumed.

Retained step 3; cited statements: lem-amb-etale-compact-comparisons, def-weil-pbc-composite-adjunction, lem-trf-adjoint-mate, lem-fix-compact-support-coefficient-change, lem-sf-compact-coefficient-composition.

We spell out the formal normalization used below. For composable compact-support functors $F_pF_i\cong F_{pi}$ use [lem-amb-etale-compact-comparisons]. The composite-adjunction rule [def-weil-pbc-composite-adjunction] says its counit is
$$\varepsilon_{pi}=\varepsilon_p\circ F_p(\varepsilon_i).$$
When the left-functor comparison is available on the whole categories, the comparison with any chosen right adjoint is the counit-compatible unique mate of [lem-trf-adjoint-mate]. For the bounded-below composition comparison, we need only its objectwise version: if $Q_1,Q_2\in D^+$ both represent $L\mapsto\operatorname{Hom}(F(L),N)$ for $L\in D^+$, the natural Hom bijections give mutually inverse maps $Q_1\to Q_2$ and $Q_2\to Q_1$ by evaluating on their identities. Naturality says their composites are identities and their transposes are the specified counits. We use this argument only after verifying that both representing objects are bounded below; it requires no composition comparison on unbounded inputs. The coefficient tensor comparisons paste in the same order:
$$c_{pi,K}=F_{p,B}(c_{i,K})\circ c_{p,F_{i,A}K}.$$
This is the normalized coefficient/composition square stated in [lem-sf-compact-coefficient-composition], with the two compact-support composition isomorphisms understood. Its hypotheses hold for the separated finite-type schemes and morphisms used below; its input is finite-Tor constructible by the construction and finite-Tor verification for the closed factor and by the extension-by-zero check in the open-locality calculation for the open factor. The cited statement concerns the actual canonical comparison maps and supplies this equality with the composition identifications. We use the coefficient comparison only in the finite-Tor situations certified in the construction and finite-Tor verification or in the closed-support assertion below; no claim that $B$ has finite Tor dimension over $A$ is required.

### lem-coef-dualizing-affine-space

Original steps: 4, 5, 6.

Retained step 4; cited statements: lem-asd-etale-finite-twist-pullback, lem-kun-derived-tensor-triangulated, def-kun-tor-amplitude, def-weil-pbc-constructible-complexes.

For $P=\mathbf A^r_k$ and $p:P\to s$, use the ordinary etale Tate sheaves of [lem-asd-etale-finite-twist-pullback]. Choose one power $N$ of $\ell$ annihilating $A$ (and hence $B,C$). Its definition $A_P(1)=\mu_{N,P}\otimes_{\mathbf Z/N}A$ gives
$$A_P(r)\otimes_A^L B\cong B_P(r).$$
Indeed the Tate sheaf is locally free of rank one by that node, so ordinary tensor computes this derived tensor; on trivializations the comparison is $A\otimes_A B=B$, and the transition units reduce to the transition units for $B$. Tensor powers give the assertion for every $r\ge0$; shifts commute with this tensor by [lem-kun-derived-tensor-triangulated]. The shifted Tate line $A_P(r)[2r]$ is bounded constructible of finite Tor amplitude, directly from a finite locally free rank-one sheaf and the definition of Tor amplitude [def-kun-tor-amplitude, def-weil-pbc-constructible-complexes]. Thus all coefficient comparisons used for it are in the stated domain.

Retained step 5; cited statements: cor-amb-affine-space-adjunction, lem-amb-affine-space-top-trace, lem-weil-pbc-derived-single-fully-faithful.

Here is why the specified map is an isomorphism on $P$, without assuming coefficient compatibility of a chosen purity adjunction. By [cor-amb-affine-space-adjunction], identify $\omega_{P,R}$ with $R_P(r)[2r]$ for $R=A,B$, using the counit-compatible comparison of the composite-adjunction normalization. For the explicit coordinate-tower adjunction in the top-trace node, use that comparison on $D^+$: its representing object $R_P(r)[2r]$ is bounded, and the chosen $\omega_{P,R}$ is bounded by the construction and finite-Tor verification, so the objectwise argument applies. By [lem-amb-affine-space-top-trace], the counit $\varepsilon_{P,R}$ is an isomorphism; that statement concerns the explicit adjunction, and the composite-adjunction normalization carries its counit to the chosen one. Step 2 therefore gives
$$F_{P,B}(u_{P,A,B})=\varepsilon_{P,B}^{-1}(T_{A,B}\varepsilon_{P,A})c_{P,\omega_{P,A}}^{-1},$$
an isomorphism. By the Tate-tensor calculation, source and target of $u_{P,A,B}$ are shifted copies of the same Tate line. By [lem-weil-pbc-derived-single-fully-faithful], after cancelling the shift their morphisms are sheaf morphisms. 

Retained step 6; cited statements: lem-coef-connected-tate-line-endomorphisms, lem-amb-affine-space-top-trace, def-weil-pbc-composite-adjunction.

Apply [lem-coef-connected-tate-line-endomorphisms] to $P=\mathbf A^r_k$, the finite $\mathbf Z/N$-algebra $B$, and $L=B_P(r)[2r]$. Here $P$ is nonempty and connected: $k[t_1,\ldots,t_r]$ is a domain, since products of nonzero polynomials have nonzero leading term; its zero prime is a generic point. The extracted lemma shows that $u_{P,A,B}$ is scalar multiplication and is invertible because its image under the $B$-linear $F_{P,B}$ is invertible and the top-trace identification gives $F_{P,B}L\cong B_s$. For $r=0$, the structure morphism is the identity; its identity adjunction and tensor-unit comparison make the defining adjunct equal to $1_{B_s}$, hence $u_{s,A,B}=1_{B_s}$.

### lem-coef-dualizing-closed-chart

Original steps: 7, 8.

Retained step 7; cited statements: def-weil-finite-type-morphism, def-weil-closed-immersion, lem-weil-pbc-closed-immersion-integral-separated-uc, lemma-weil-pbc-finite-direct-image-exact, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-exact-functor-derived-functor, lem-weil-pbc-exact-functor-complex-cohomology.

Choose an affine open chart $U=\operatorname{Spec}R$ from the finite-type affine cover of $X$. By [def-weil-finite-type-morphism], choose finitely many $k$-algebra generators $x_1,\ldots,x_r$ of $R$. The surjection $k[t_1,\ldots,t_r]\to R$, $t_j\mapsto x_j$, induces a closed immersion $i:U\hookrightarrow P=\mathbf A^r_k$ by the affine characterization in [def-weil-closed-immersion]; its composite with $p$ is $a_U$. This is a choice on one affine chart, not a claim that $X$ embeds globally into affine space. The closed immersion is finite, separated and universally closed by [lem-weil-pbc-closed-immersion-integral-separated-uc], and its affine quotient-ring description makes it of finite type. Thus it is proper, and its compact-support candidate can be taken to have identity open part, so $Ri_!=Ri_*$. Since $i$ is finite, [lemma-weil-pbc-finite-direct-image-exact] makes its sheaf direct image exact; this also holds for coefficient modules, whose kernels and cokernels have the underlying abelian-sheaf kernels and cokernels.  By [lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-exact-functor-derived-functor], the unbounded derived functor is termwise $i_*$. By [lem-weil-pbc-exact-functor-complex-cohomology], $H^q(i_*L)=i_*H^q(L)$ for every complex, so it preserves all cohomological upper and lower bounds.

Retained step 8; cited statements: lem-exc-closed-ambient, lem-etale-upper-shriek-bounded-below-from-amplitude, lem-amb-etale-compact-comparisons.

The ordinary etale closed adjoint is [lem-exc-closed-ambient]. For the identity-open compactification, $Ri_!=i_*$ is the exact termwise functor established above. Hence $L\in D^{\le m}$ implies $Ri_!L\in D^{\le m}$ for every integer $m$. Apply [lem-etale-upper-shriek-bounded-below-from-amplitude] with amplitude bound $0$: the right adjoint carries bounded-below objects to bounded-below objects. Identify that chosen right adjoint with $Ri_R^!$ by their natural Hom bijections and counits, as in the composite-adjunction normalization. Thus $Ri_R^!\omega_{P,R}$ is bounded below. The other representing object $\omega_{U,R}$ is bounded by the construction and finite-Tor verification. The objectwise $D^+$ argument applied to the composite Hom bijections gives counit-compatible identifications
$$\omega_{U,R}\cong Ri_R^!\omega_{P,R},\qquad\varepsilon_{U,R}=\varepsilon_{P,R}\circ F_{P,R}(\varepsilon_{i,R}),\quad R=A,B.$$
All representing objects are bounded below, so the composition statement of [lem-amb-etale-compact-comparisons] suffices.

### lem-coef-dualizing-closed-site

Original steps: 9, 10, 11, 12.

Retained step 9; cited statements: .

Set $M=\omega_{P,A}\cong A_P(r)[2r]$, $N=Ri_{A,\mathrm{et}}^!M\cong\omega_{U,A}$, and $M_B=T_{A,B}M$. We first obtain the closed comparison on the ordinary etale site; the finite closed-shriek coefficient theorem itself is a pro-etale theorem. If $U$ is empty its module derived categories are zero, so the required closed comparison is the unique isomorphism of zero objects; both sides of its counit equation are the unique map from zero to $M_B$ on $P$. Assume henceforth that $U$ is nonempty.

Retained step 10; cited statements: def-weil-exceptional-inverse-image, lem-sf-comparison-pullback-exact, thm-weil-pbc-site-comparison, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

Write $S_{T,R}=\nu_{T,R}^*$, $I_R=Ri_{R,\mathrm{et}}^!$, and $J_R=Ri_{R,\mathrm{proet}}^!$ for $R=A,B$, where $J_R$ is the transported constructible functor of [def-weil-exceptional-inverse-image]. Write $T$ for etale coefficient extension and $T^{\mathrm{pro}}$ for its pro-etale counterpart, with the scheme understood. By [lem-sf-comparison-pullback-exact] comparison is exact and identifies the constant coefficient rings. By [thm-weil-pbc-site-comparison] $S_{T,R}$ is fully faithful on $D^+$ and its unit $1\to R\nu_{T,R,*}S_{T,R}$ is an isomorphism. By [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] there are natural $B$-linear identifications
$$t_{T,K}:S_{T,B}(TK)\xrightarrow{\sim}T^{\mathrm{pro}}S_{T,A}K.$$
This is an isomorphism in the derived category of actual $B$-module sheaves. To check its coefficient structure, represent $K$ by a K-flat complex $Q$ with flat $A$-module terms. Then $TK$ is represented by $Q\otimes_A B$, while $S_{T,A}Q$ is K-flat by the cited pullback theorem. Exact comparison identifies $S_{T,B}(Q\otimes_A B)$ with $(S_{T,A}Q)\otimes_A B$ termwise. The balancing maps and their inverses commute with $b\cdot(x\otimes b')=x\otimes bb'$ and with the differential. Hence they are $B$-linear chain isomorphisms and give the displayed comparison before localization. No inference from a mere action on an underlying derived $A$-object is needed. In the pro-etale formulas below, $i_*^{\mathrm{pro}}$ denotes the derived direct image $Ri_*^{\mathrm{pro}}$.

Retained step 11; cited statements: lem-kun-dimension-finite-type, thm-sf-ambient-adjoint-class, def-weil-exceptional-inverse-image.

The identity-open compactification of $i$ is available by the affine closed-adjoint identification. Its dimension is finite by [lem-kun-dimension-finite-type], so choose a finite nonnegative integer bound $d$ and apply [thm-sf-ambient-adjoint-class] at both coefficient stages. Its adjunction is relative to bounded-below etale-origin inputs, which suffices here. The defining formula for the finite functor in [def-weil-exceptional-inverse-image], the unit above, and the counit-preserving identification of the ordinary closed adjoint from the affine closed-adjoint identification give
$$\alpha_{R,H}:S_{U,R}I_RH\xrightarrow{\sim}J_RS_{P,R}H$$
for the bounded inputs $H=M$ at $R=A$ and $H=M_B$ at $R=B$. More explicitly, let $\eta_{R,H}:H\xrightarrow{\sim}R\nu_{P,R,*}S_{P,R}H$ be the specified comparison unit. After identifying the etale compact-support adjoint with $I_R$ by the counit-compatible comparison of the affine closed-adjoint identification, the map $\alpha_{R,H}$ is $S_{U,R}I_R(\eta_{R,H})$, with target $S_{U,R}I_RR\nu_{P,R,*}S_{P,R}H=J_RS_{P,R}H$. Thus it uses the actual functorial transport and its specified unit. Both ordinary representing objects are bounded below: $I_AM=N=\omega_{U,A}$ by the affine closed-adjoint identification, while $I_BM_B\cong I_B\omega_{P,B}=\omega_{U,B}$ by the Tate and affine closed-adjoint calculations. They are bounded constructible of finite Tor amplitude by the construction and finite-Tor verification. This does not assume the desired comparison for $I_A$ and $I_B$.

Retained step 12; cited statements: lem-coef-site-closed-counit-transport, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-sf-class-compact-support-comparison.

Apply [lem-coef-site-closed-counit-transport] with $H=M$ and $H=M_B$. Its $\alpha$ is precisely $S_{U,R}I_R(\eta_{R,H})$ constructed above; the bounded-below hypotheses were verified independently above. For $\delta_{R,L}:S_{P,R}i_*^{\mathrm{et}}L\xrightarrow{\sim}i_*^{\mathrm{pro}}S_{U,R}L$ use [lem-weil-pbc-comparison-direct-image-canonical-mate]. It also equals the inverse compact-support comparison for the identity-open compactification by [lem-sf-class-compact-support-comparison]. Write $e_{R,H}$ and $E_{R,S_{P,R}H}$ for the etale and pro-etale exceptional counits. The extracted theorem gives the actual normalization
$$E_{R,S_{P,R}H}\circ i_*^{\mathrm{pro}}(\alpha_{R,H})\circ\delta_{R,I_RH}=S_{P,R}(e_{R,H}).\tag{*}$$
Thus the counits used below belong to the specified transported Hom bijection, rather than an arbitrary adjunction on isomorphic objects.

### lem-coef-dualizing-closed-descent

Original steps: 13, 14, 15, 16.

Retained step 13; cited statements: lem-coef-finite-direct-image, lem-sp-et-proet-coefficient-compatibility, lem-fix-compact-support-coefficient-change.

Since $N$ is finite-Tor constructible, [lem-coef-finite-direct-image] supplies the ordinary coefficient isomorphisms $c^e_{i,N}$ and $c^p_{i,S_{U,A}N}$. The algebra $B$ is finite over $A$ because it is a quotient. Apply [lem-sp-et-proet-coefficient-compatibility] to $h=i$ and its identity-open compactification. Its site map $c_{h,R}^c$ is our $\delta_R$ and its tensor identification $\delta_{T,K}$ is our $t_{T,K}^{-1}$. Its coefficient maps $\beta_h^c,b_h^c$ are $c^e,c^p$, since the open factor is the identity. Postcompose its displayed square with $i_*^{\mathrm{pro}}(t_{U,N})$ and precompose with $t_{P,i_*^{\mathrm{et}}N}$ to obtain
$$c^p_{i,S_{U,A}N}\circ T^{\mathrm{pro}}(\delta_{A,N})\circ t_{P,i_*^{\mathrm{et}}N}
=i_*^{\mathrm{pro}}(t_{U,N})\circ\delta_{B,TN}\circ S_{P,B}(c^e_{i,N}).\tag{**}$$
The input $N$ is bounded constructible finite-Tor, and $i$ is separated finite type between separated finite-type $k$-schemes, as required there. For this compactification $c^e_{i,N}$ is also the compact-support comparison of [lem-fix-compact-support-coefficient-change]: its open tensor factor is the identity and its proper factor is the ordinary direct-image projection mate.

Retained step 14; cited statements: lem-sf-comparison-tor-amplitude, lem-coef-finite-direct-image, lem-coef-finite-closed-shriek.

By [lem-sf-comparison-tor-amplitude], both $S_{P,A}M$ and $S_{U,A}N$ are bounded finite-Tor constructible on the pro-etale site, since $M$ and $N$ have that property on the etale site by the finite-Tor verification and closed-adjoint identification. The isomorphism $\alpha_{A,M}$ already constructed identifies $J_AS_{P,A}M$ with $S_{U,A}N$; hence the former is finite-Tor constructible as well. In particular the canonical direct-image coefficient maps at both $S_{U,A}N$ and $J_AS_{P,A}M$ are invertible by the pro-etale clause of [lem-coef-finite-direct-image]. Its naturality applies to $\alpha_{A,M}$: this is a morphism between bounded-below etale-origin objects, and full faithfulness identifies it with a morphism between their etale representatives. This verifies the domains of the inverse coefficient maps and their naturality in the counit descent below, independently of the desired etale closed comparison. All schemes and rings have the hypotheses of [lem-coef-finite-closed-shriek]: $P,U$ are separated finite type over the fixed $k$, $\ell$ is invertible, $i$ is closed, and $A\to B$ is the allowed finite quotient map. Apply that theorem only on its stated pro-etale site, obtaining its counit-defined isomorphism
$$b^{\mathrm{pro}}:T^{\mathrm{pro}}J_AS_{P,A}M\xrightarrow{\sim}J_BT^{\mathrm{pro}}S_{P,A}M.$$


Retained step 15; cited statements: lem-coef-fully-faithful-counit-descent, thm-sf-ambient-adjoint-class, lem-weil-pbc-comparison-direct-image-canonical-mate.

Apply [lem-coef-fully-faithful-counit-descent] with $F_R=i_*^{\mathrm{et},R}$, $I_R=Ri_{\mathrm{et},R}^!$, $F'_R=i_*^{\mathrm{pro},R}$, $S_C=S_U$, $S_D=S_P$, and $T,T^{\mathrm{pro}}$ as coefficient functors on ambient module derived categories. Set its single object $Q_A=J_AS_{P,A}M$, and restrict $J_B$ to $\mathcal V_B=D^+(P_{\mathrm{proet}},B)$, which contains $S_{P,B}M_B$ and $T^{\mathrm{pro}}S_{P,A}M$ by the tensor identification. Thus no unbounded exceptional pro-etale functor is needed. Only the Hom sets specified in that lemma require full faithfulness; coefficient tensor need not preserve $D^+$ globally. The comparison-class counit is natural along $t_{P,M}$ by [thm-sf-ambient-adjoint-class]. The two counit hypotheses are (*); the coefficient square is (**). Its $b'$ is the counit-defined pro-etale isomorphism above. The components of $c'$ at $S_{U,A}N$ and $Q_A$ are invertible by the finite-Tor verification above. Its $\delta_{A,N}$ is the canonical comparison at the bounded object $N$, and its family $\delta_B$ is the canonical comparison on $\mathcal C^0_B=D^+(U_{\mathrm{et}},B)$, which contains $TN$ and $I_BM_B$; there it is natural and invertible by [lem-weil-pbc-comparison-direct-image-canonical-mate], so no site comparison on unbounded inputs is used. The next step verifies the exact fullness and faithfulness domains.

Retained step 16; cited statements: lem-coef-fully-faithful-counit-descent, thm-weil-pbc-site-comparison, lem-coef-finite-direct-image.

In this application $\kappa_1=T^{\mathrm{pro}}(\alpha_{A,M})t_{U,N}$ and $\kappa_2=J_B(t_{P,M})\alpha_{B,M_B}$ identify the images of $TN$ and $I_BM_B$ with the source and target of $b^{\mathrm{pro}}$. The inverses are $t_{U,N}^{-1}T^{\mathrm{pro}}(\alpha_{A,M}^{-1})$ and $\alpha_{B,M_B}^{-1}J_B(t_{P,M}^{-1})$. The formal descent theorem therefore gives an isomorphism $b_{i,M}:TI_AM\xrightarrow{\sim}I_BM_B$ with
$$e_{B,M_B}\circ i_*b_{i,M}=(Te_{A,M})\circ(c^e_{i,N})^{-1}.$$
Check the exact faithfulness domain: $TN$ is bounded because the finite Tor interval of $N$ bounds its tensor with the degree-zero $A$-module sheaf $B$; forgetting the $B$-action does not change cohomology. Also $I_BM_B\cong\omega_{U,B}$ is bounded independently. The displayed equation lies in $\operatorname{Hom}_{D^+(P_{\mathrm{et}},B)}(i_*TN,M_B)$. Its intermediate object $Ti_*N$ is bounded by the already established isomorphism $c^e_{i,N}:Ti_*N\cong i_*TN$. Thus fullness lifts both arrows and faithfulness descends the equation on precisely these bounded-below objects.

### lem-coef-dualizing-closed-assembly

Original steps: 17, 18, 19.

Retained step 17; cited statements: lem-exc-closed-ambient.

Form
$$v=Ri_B^!(u_{P,A,B})\circ b_{i,M}:T_{A,B}\omega_{U,A}\longrightarrow\omega_{U,B}.$$
The map $b_{i,M}$ is an isomorphism by the full-faithfulness argument above; $u_{P,A,B}$ is an isomorphism by the affine-space comparison, and the functor $Ri_B^!$ preserves isomorphisms. Hence $v$ is an isomorphism. It remains to identify it with the specified global construction at $U$. Under the composite adjunction, first transpose through $i_*\dashv Ri_B^!$. Naturality of its counit and the counit identity for $b_{i,M}$ give
$$\varepsilon_{i,B}\circ i_*v=u_{P,A,B}\circ(T_{A,B}\varepsilon_{i,A})\circ c_{i,\omega_{U,A}}^{-1}.$$


Retained step 18; cited statements: def-weil-pbc-composite-adjunction, lem-sf-compact-coefficient-composition.

Here is the final composite-adjunction check with the coefficient factors retained. Abbreviate $F_R=F_{P,R}$, $c_U=c_{a_U,N}$, and $c_{p,Q}=c_{P,A,B,Q}$. The compact-support composition identifications of the composite-adjunction normalization give
$$c_U=F_B(c_{i,N})\circ c_{p,i_{*,A}N}.$$
Use $e_A:i_{*,A}N\to M$ and $e_B:i_{*,B}I_BM_B\to M_B$ for the closed exceptional counits from the descent above. After identifying $I_B\omega_{P,B}$ with $\omega_{U,B}$, the closed counit at $\omega_{P,B}$ will be denoted $e'_B$. Naturality of the exceptional counit gives $e'_B\,i_*v=u_P(T e_A)c_{i,N}^{-1}$. Precompose the adjunct of $v$ with $c_U$ and compute
$$\begin{aligned}
(\varepsilon_{U,B}\circ F_{U,B}v)\circ c_U
&=\varepsilon_{P,B}\circ F_B(e'_B\circ i_*v)\circ F_B(c_{i,N})\circ c_{p,i_{*,A}N}\\
&=\varepsilon_{P,B}\circ F_B(u_P)\circ F_B(T e_A)\circ c_{p,i_{*,A}N}\\
&=(T\varepsilon_{P,A})\circ c_{p,M}^{-1}\circ F_B(T e_A)\circ c_{p,i_{*,A}N}\\
&=(T\varepsilon_{P,A})\circ T F_A(e_A)\\
&=T(\varepsilon_{P,A}\circ F_A(e_A))
=T\varepsilon_{U,A}.
\end{aligned}$$


Retained step 19; cited statements: lem-fix-compact-support-coefficient-change, def-weil-pbc-composite-adjunction.

The first line is the composite-counit formula and the normalized coefficient/composition square; the second uses the descended closed-counit identity and cancels $c_{i,N}^{-1}c_{i,N}$. The third is the defining counit equation for $u_P$. The fourth uses naturality $F_B(T e_A)c_{p,i_{*,A}N}=c_{p,M}T F_A(e_A)$, so it takes no inverse of $c_{p,i_{*,A}N}$. The last line is the composite counit from the affine closed-adjoint identification. The only inverse coefficient maps in this calculation are at $N$ and $M$, both independently finite-Tor constructible; $c_U$ is invertible at $N$ too. Cancelling $c_U$ therefore identifies the adjunct with $(T\varepsilon_{U,A})c_U^{-1}$, exactly the defining adjunct of $u_{U,A,B}$. Injectivity of the adjunction bijection proves $v=u_{U,A,B}$; consequently the canonical map is an isomorphism on every affine chart.

### lem-coef-dualizing-open-adjoint

Original steps: 20, 21.

Retained step 20; cited statements: lem-amb-etale-adjoint-locality, lem-weil-pbc-open-immersion-etale, lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-qc-open-immersion-finite-type, def-amb-etale-compact-support, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

For the affine open inclusion $j:U\hookrightarrow X$, [lem-amb-etale-adjoint-locality] identifies $j^*\omega_{X,R}$ with $\omega_{U,R}$ for $R=A,B$. Its hypotheses hold: $j$ is etale by [lem-weil-pbc-open-immersion-etale]; it is separated because its diagonal is an isomorphism. The intersections of its affine source with target affine opens are quasi-compact by [lem-weil-pbc-locally-noetherian-quasi-separated], so $j$ is quasi-compact, hence of finite type by [lem-weil-pbc-qc-open-immersion-finite-type]. The maps $a_X,a_U$ are compactifiable between Noetherian schemes by step 1. For this open immersion choose the compactification $U\xrightarrow{j}X\xrightarrow{1_X}X$ in [def-amb-etale-compact-support]. Its defining functor is $R(1_X)_*Dj_!=Dj_!$, since the identity direct image is the identity on complexes and preserves quasi-isomorphisms. Thus open compact support is exact termwise extension by zero. The open adjunction already stated in [lem-amb-etale-adjoint-locality] is $j_!\dashv j^*$; its Hom bijection sends a map to its restriction on $U$, so its counit is section evaluation. The unique counit-compatible comparison of the composite-adjunction normalization identifies any chosen right adjoint with this one. Combining this with the $D^+$ composition comparison of the composite-adjunction normalization gives $F_U\cong F_Xj_!$ on the inputs below; thus the subsequent Hom calculation uses the specified open counit. Ordinary inverse image commutes with coefficient tensor by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. 

Retained step 21; cited statements: lem-amb-etale-adjoint-locality, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-weil-pbc-composite-adjunction.

These identifications send $j^*u_{X,A,B}$ to $u_{U,A,B}$, as follows from the same counit calculation rather than from any coefficient compatibility of an exceptional functor: the locality isomorphism is the mate of $F_U\cong F_Xj_!$ and $j_!\dashv j^*$. Its counit is $\varepsilon_{U,R}=\varepsilon_{X,R}\circ F_{X,R}(\varepsilon_{j,R})$: the Hom bijections are $\operatorname{Hom}_U(L,j^*a_X^\times N)\cong\operatorname{Hom}_X(j_!L,a_X^\times N)\cong\operatorname{Hom}_s(F_Xj_!L,N)\cong\operatorname{Hom}_s(F_UL,N)$, so the counit formula follows by composing them as in the composite-adjunction normalization. 

### lem-coef-dualizing-open-tensor

Original steps: 22, 23.

Retained step 22; cited statements: lem-pur-etale-open-derived-tensor, lem-weil-pbc-extension-by-zero-stalks, lemma-weil-pbc-geometric-stalk-conservative.

Tensoring commutes with $j_!$ by the canonical derived comparison [lem-pur-etale-open-derived-tensor] (Stacks Tag 0GL1, lemma-j-shriek-and-tensor), applied to the constant coefficient object $B_X$. Put $W=\omega_{X,A}$, $L=j^*W=\omega_{U,A}$, $G_R=j_{!,R}$, and let $e_R:G_Rj^*\to1$ be the evaluation counit. Write $d_L:T_XG_AL\xrightarrow{\sim}G_BT_UL$ for this comparison. It is compatible with evaluation:
$$e_{B,T_XW}\circ d_L=T_X(e_{A,W}).$$
Indeed on stalks inside $U$ both maps evaluate the same section and outside $U$ their sources are zero by [lem-weil-pbc-extension-by-zero-stalks]. Equality is checked degreewise on these tensor models: the difference has zero image sheaf since every stalk of that image is zero, by [lemma-weil-pbc-geometric-stalk-conservative]. Thus the chain maps agree and descend to the displayed equation.

Retained step 23; cited statements: lem-pur-etale-open-derived-tensor, def-kun-tor-amplitude, def-weil-pbc-constructible-complexes, lem-amb-etale-adjoint-locality, lem-sf-compact-coefficient-composition, lem-weil-pbc-extension-by-zero-exact.

All inverses of compact-support coefficient maps below are in their finite-Tor constructible domain. Indeed $L$ is bounded finite-Tor constructible by the construction and finite-Tor verification and open restriction. Extension by zero keeps its cohomology constructible: extend its finite locally closed stratification from $U$ to $X$, adding the closed complement with the zero sheaf. Its Tor bound is unchanged because the derived projection identity computes tensor with any degree-zero module as $j_!$ of the corresponding tensor on $U$, and $j_!$ is exact by [lem-weil-pbc-extension-by-zero-exact], using [def-kun-tor-amplitude, def-weil-pbc-constructible-complexes]. In particular $G_AL$ and $T_XG_AL\cong G_BT_UL$ are bounded below, so the composition comparison is applicable. By the composite-adjunction normalization the coefficient comparison for $a_U$ is
$$c_{U,L}=F_{X,B}(d_L)\circ c_{X,G_AL}.$$


### lem-coef-dualizing-open-mate

Original steps: 24.

Retained step 24; cited statements: def-weil-pbc-composite-adjunction, lem-fix-compact-support-coefficient-change, lem-sf-compact-coefficient-composition.

Let $q=j^*u_{X,A,B}$, under the pullback/tensor identification. Its adjunct under $F_{U,B}\dashv a_{U,B}^{\times}$ is, with the composition identifications understood,
$$\begin{aligned}
\varepsilon_{U,B}F_{U,B}(q)
&=\varepsilon_{X,B}F_{X,B}(e_{B,\omega_{X,B}}\circ G_Bq)\\
&=\varepsilon_{X,B}F_{X,B}(u_X)F_{X,B}(e_{B,T_XW})\\
&=(T_s\varepsilon_{X,A})c_{X,W}^{-1}F_{X,B}(T_Xe_{A,W})F_{X,B}(d_L)^{-1}\\
&=T_s(\varepsilon_{X,A}\circ F_{X,A}e_{A,W})c_{X,G_AL}^{-1}F_{X,B}(d_L)^{-1}\\
&=(T_s\varepsilon_{U,A})c_{U,L}^{-1}.
\end{aligned}$$
Here the second line is naturality of $e_B$, the third is the defining identity of the construction and finite-Tor verification and the stalk evaluation identity, and the fourth is naturality of the compact-support coefficient comparison [lem-fix-compact-support-coefficient-change]. The last line uses the displayed composition and counit formulas. This is the defining adjunct of $u_U$, so injectivity of the adjunction bijection gives $q=u_U$. This proves that the restriction of the globally defined map is the canonical affine map proved invertible in the closed-support affine comparison.

### lem-coef-dualizing-quotient-mates

Original steps: 26.

Retained step 26; cited statements: lem-fix-compact-support-coefficient-change.

For the quotient cocycle write $T=T_{A,B}$, $S=T_{B,C}$, $F_R=F_{X,R}$, $c^{AB}=c_{X,A,B}$ and $c^{BC}=c_{X,B,C}$. The input $T\omega_A$ of $c^{BC}$ is in $D^b_{ctf}(X,B)$: the global invertibility conclusion identifies it with $\omega_B$, whose finite-Tor constructibility was proved in the construction and finite-Tor verification. Thus the displayed inverse comparisons all have the domain required by the cited coefficient theorem. To compare $u_{X,A,C}$ and $w=u_{X,B,C}\circ S(u_{X,A,B})$, transpose under $F_C\dashv a_{X,C}^{\times}$. By the defining counit identity at $B,C$, naturality of $c^{BC}$, and the defining identity at $A,B$, respectively, the adjunct of $w$ is
$$\begin{aligned}
\varepsilon_C F_C(w)
&=(S\varepsilon_B)(c^{BC}_{\omega_B})^{-1}F_CS(u_{A,B})\\
&=S(\varepsilon_B F_B(u_{A,B}))(c^{BC}_{T\omega_A})^{-1}\\
&=(ST\varepsilon_A)\,S((c^{AB}_{\omega_A})^{-1})(c^{BC}_{T\omega_A})^{-1}\\
&=(T_{A,C}\varepsilon_A)(c^{AC}_{\omega_A})^{-1}.
\end{aligned}$$
The last equality is precisely the successive-reduction compatibility in [lem-fix-compact-support-coefficient-change], with the tensor reassociation. The final expression is the defining adjunct of $u_{X,A,C}$, so the maps coincide. With $B=A$, the comparison is the tensor-unit identification and the adjunct is $\varepsilon_A$, whose adjoint is the identity. This proves the quotient cocycle and identity globally, not just chartwise. The counit assertion has already been proved at the moment of construction in the construction and finite-Tor verification.

### lem-coef-dualizing-site-mates

Original steps: 27.

Retained step 27; cited statements: lem-weil-finite-duality-site-comparison, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-weil-exceptional-inverse-image, lem-sf-class-compact-support-comparison.

Finally apply the current finite-stage statement [lem-weil-finite-duality-site-comparison] separately with $R=A_{E,n}$ and $R=B=A_{E,m}$. Its hypotheses are exactly the global finite-field datum, $\ell\ne p$, these finite DVR quotient rings and the separated finite-type $k$-scheme $X$. It supplies $\nu_X^*\omega_{X,R}\cong\omega_{X,R,\mathrm{proet}}$, with the latter explicitly defined using the comparison-class transport of the ordinary etale compact-support right adjoint. Thus this application does not require a site-comparison theorem for arbitrary finite rings or an ambient pro-etale adjoint. Applying the derived tensor pullback comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to $\nu_X$ and the constant ring map $A\to B$ identifies $\nu_X^*T_{A,B}\omega_{X,A}$ with $T_{A,B}\nu_X^*\omega_{X,A}$. Thus the pullback of $u_{X,A,B}$ gives the asserted isomorphism for the finite pro-etale realization. This is an identification on the constructible, etale-origin objects only: [def-weil-exceptional-inverse-image] defines the exceptional functor there by transporting the etale adjoint, and [lem-sf-class-compact-support-comparison] identifies its compact-support left functor with the pro-etale one. Consequently the transported Hom bijection sends the transported adjunct to exactly the transported map, and its counit is the image of the etale counit. Pulling back the actual identities in the construction and quotient calculation proves the same counit and quotient identities in this realization. No unbounded pro-etale exceptional adjoint or change to a condensed coefficient category has been introduced.

### Elementary covering detection retained in the parent

Now $u_{X,A,B}$ is an isomorphism. Indeed its restriction to each affine chart is an isomorphism by the affine and open-locality calculations. Restriction to an open is exact, so the kernel and cokernel of every cohomology-sheaf map vanish on the covering. A sheaf vanishing on a covering is zero by the sheaf axiom. Thus these cohomology maps are all isomorphisms, so $u_{X,A,B}$ is a quasi-isomorphism, hence an isomorphism in the derived category. This uses only the definition of cohomology sheaves [def-weil-derived-cohomology-sheaves] and exactness of inverse image [prop-weil-pbc-inverse-image-modules-exact]. No morphisms in a derived category are glued, and no equality of global morphisms is inferred merely from local equality.

