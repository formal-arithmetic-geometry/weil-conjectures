# Repair report: Q79 / lem-sfb-equivariant-resolution-bar-normalization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-resolution-bar-normalization.json: repaired split, statement unchanged.
- lem-sfb-homogeneous-injective-total-target: statement, unsplit, no Mathlib match; old steps 1-3.
- lem-sfb-homogeneous-bar-coordinate-normalization: statement, unsplit, no Mathlib match; old steps 4-6.
- citations.json: verbatim cited-statement excerpts for every citation in the five parent steps.

## Attachments

None. I searched the live WeilConjectures source for the item tag and normalization notions. The full theorem is instead in Sheaf/CategoryTheory/EquivariantResolutionBarNormalization.lean, ending in sorry. Its docstring reproduces the nine-step argument. No completed project declaration states this item or either new internal condensed-module statement. Generic exact-adjoint and resolution declarations do not include the new concrete constructions.

## WANTED

WANTED: an independent reference for the internal condensed derived bar normalization and homogeneous comparison, for the item and both new nodes. The available source is the main-20261015 direct-images blueprint paragraph (3), as agent-expanded in the existing split and Lean docstring; that blueprint provides the geometric context rather than this full formal argument. All expansions remain agent arguments. Stacks supplies only the individual flatness, adjoint, lifting and homotopy tools, not an unrecorded claim about continuous-cochain acyclicity.

## Return repaired and comparison with current repository

The sandbox initially contained only dispatcher brief markers: no retained node, report or search log. I copied the live item without a git command. It carries the returned nine-step, 6238-character proof and the existing Q10 review. I retained its statement, historical searches, pointers and all import/blueprint metadata. The return explicitly requires spreading the work, so two new unsplit statements now carry distinct arguments of comparable extent. Neither states the desired equality for an arbitrary equivariant resolution. The parent retains the independent lifting/homotopy/unit assembly. No Lean was written and no compiler or Lake tool was run. Delivery builds/rebases its own temporary worktree against current server state.

## Argument allocation, without shortening the returned argument

The following is the complete previous argument, retained verbatim as working material for the new workers, not proof fields on the unsplit nodes. Steps 1-3 belong to the injective-total-target task, steps 4-6 to the coordinate-normalization task, and steps 7-9 remain in the parent assembly.

### Returned step 1 -> lem-sfb-homogeneous-injective-total-target

Write $\mathcal E$ for internal $G$-equivariant modules, $\mathcal M$ for ordinary internal modules, $U$ for forgetting the action, and $F=\Gamma_G$. By the derived restriction calculus, both categories are Grothendieck abelian, $U$ is exact and detects exactness, and $F$ is additive and right adjoint to exact trivial inflation, hence left exact. Enough injectives gives a nonnegative equivariant injective resolution $s:N[0]\to I^\bullet$: embed $N$ in an injective, embed its cokernel in the next injective, and continue. These successive embeddings make the augmented sequence exact. The cited K-injective computation theorem says $I^\bullet$ is K-injective.

Cited statements: lem-sfb-condensed-derived-restriction-calculus, lem-sp-grothendieck-enough-injectives, def-sp-injective-resolutions, lem-sp-kinjective-computes.

### Returned step 2 -> lem-sfb-homogeneous-injective-total-target

For a profinite parameter $S$, the free module $A[S]$ is $j_{S!}A_S$: maps from the presheaf $V\mapsto\bigoplus_{V\to S}A(V)$ to a module sheaf are determined by the image of the identity generator at $S$, so its sheafification has exactly the free universal property. The internal/section-module equivalence allows application of the cited flatness theorem; thus $A[G]$ is flat. The functor $L(M)=A[\underline G]\otimes_A M$, with translation on the first factor, is left adjoint to $U$: $h:M\to UJ$ corresponds to $[g]\otimes m\mapsto g h(m)$, with inverse evaluation at $[1]$. These formulas hold after every base change. Since $U$ creates exactness and tensor with $A[G]$ is exact, $L$ is exact. The exact-left-adjoint injectivity theorem now implies that $UI^q$ is injective for every $q$. Exactness of $U$ makes $Us$ an ordinary internal-module injective resolution.

Cited statements: def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-pc-sites-modules-j-shriek-flat, lem-pc-sheaf-modules-tensor-closed, lem-sfb-condensed-derived-restriction-calculus, lem-sp-right-adjoint-preserves-injectives.

### Returned step 3 -> lem-sfb-homogeneous-injective-total-target

Form $T^{p,q}=\underline{\operatorname{Hom}}_A(A[\underline G^{p+1}],UI^q)$ for $p,q\geq0$, with homogeneous deletion differential horizontally and $d_I$ vertically. Give it the diagonal action on arguments AND the action on $I^q$ on values. These differentials are equivariant and commute. Put $T=\operatorname{Tot}T^{p,q}$ with $d_h+(-1)^p d_v$. The new homogeneous-function injectivity lemma applies to $I^q$, using step 2, so each $T^{p,q}$ is equivariantly injective. Each $T^n$ is a finite sum of these objects, hence injective: extend a map across a monomorphism separately after each of the finitely many projections, and take their sum into the finite biproduct. Thus $T$ is a bounded-below complex of equivariant injectives. There is an equivariant cochain map $\delta:I\to T$ placing the constant function with value $x\in I^q$ in bidegree $(0,q)$: its horizontal differential is zero and its vertical differential is the constant function with value $d_Ix$.

Cited statements: lem-sfb-internal-homogeneous-functions-injective, def-sp-double-complex-total, def-sp-injective-resolutions.

### Returned step 4 -> lem-sfb-homogeneous-bar-coordinate-normalization

There is a cochain isomorphism $\chi:F(T)\to V$, where
$$V=\operatorname{Tot}_{p,q\geq0}\underline{\operatorname{Hom}}_A(A[\underline G^p],UI^q)$$
has the inhomogeneous action differential. In bidegree $(p,q)$ take $f$ to $c(g_1,\ldots,g_p)=f(1,g_1,g_1g_2,\ldots,g_1\cdots g_p)$; its inverse is
$$f(h_0,\ldots,h_p)=h_0\cdot c(h_0^{-1}h_1,h_1^{-1}h_2,\ldots,h_{p-1}^{-1}h_p).$$
Cancellation of the common left factor proves equivariance and that the formulas are inverse after every profinite base change. Deleting the first homogeneous coordinate gives $g_1c(g_2,\ldots)$, deleting an interior one multiplies the adjacent arguments, and deleting the last drops the last argument, with their original alternating signs. Postcomposition with $d_I$ commutes with evaluation because $d_I$ is equivariant. This proves the cochain assertion with the total signs of step 3. Invariants commute with these finite biproducts: a tuple is fixed exactly when each coordinate is fixed. Write $v=\chi F(\delta):F(I)\to V$; it is the bar-degree-zero inclusion of invariants.

Cited statements: def-sfb-condensed-equivariant-bar-data, def-sp-double-complex-total.

### Returned step 5 -> lem-sfb-homogeneous-bar-coordinate-normalization

Use $Us$ as the single compatible resolution for every derived internal Hom term. Step 2 makes this legitimate. The bar theorem, with the augmentation normalization specified in the bar-data node, identifies $QV$ with $\mathscr B_A(G;N)$ and gives
$$\epsilon=Q(v)\circ c_s,\qquad c_s=u_I^{-1}\circ R F(Qs):R F(QN)\longrightarrow QF(I).$$
Here $u_I$ is invertible since $I$ is K-injective. The formula for $c_s$ is the normalized derived-functor comparison, not a choice of an isomorphism on cohomology. In this model the underived-to-derived bar map $j$ is postcomposition with $s$ into the resolution-degree-zero row of $V$.

Cited statements: lem-sfb-condensed-derived-invariant-bar, def-sfb-condensed-equivariant-bar-data, def-sfb-right-derived-functor.

### Returned step 6 -> lem-sfb-homogeneous-bar-coordinate-normalization

Define $t:R_N\to T$ in degree $p$ by postcomposing with $s^0:N\to UI^0$ and putting the result in bidegree $(p,0)$. It is a cochain map since $d_Is^0=0$, and is equivariant because $s$ is equivariant and $N$ is trivial. From the definition of $\rho$ and the coordinate formulas of step 4 one obtains the equality of cochain maps
$$\chi\circ F(t e)=j_{\mathrm{chain}}\circ\rho.$$
Indeed both send $x\in F(K^p)$ to the function $s^0(e^p(x)(1,g_1,g_1g_2,\ldots))$ in bidegree $(p,0)$ and have zero other bidegree components. Here $j_{\mathrm{chain}}$ is the model of $j$ fixed in step 5.

Cited statements: def-sfb-condensed-equivariant-bar-data.

### Returned step 7 -> parent assembly

The map $a$ is degreewise monic. In degree zero, since $K^{-1}=0$, its induced isomorphism $N=H^0(N[0])\to H^0(K)=\ker d_K^0$ shows that $a^0$ is a monomorphism; in other degrees the source is zero. Apply the cited lifting lemma to the monomorphic quasi-isomorphism $a:N[0]\to K$, the bounded-below injective complex $I$, and $s:N[0]\to I$. It gives an equivariant cochain map $b:K\to I$ with $ba=s$.

Cited statements: lem-weil-pbc-lift-along-injective-quasi-iso.

### Returned step 8 -> parent assembly

Both maps $te,\delta b:K\to T$ have the same composite with $a$. The first composite sends $n$ to the constant function with value $s^0(n)$ in bidegree $(0,0)$, because $ea$ is the given augmentation. The second is $\delta s$, the very same map. Since $a$ is a quasi-isomorphism and $T$ is bounded below with injective terms (step 3), the homotopy-uniqueness lemma gives $te\simeq\delta b$ equivariantly. Applying additive invariants to $te-\delta b=dH+Hd$ preserves this equation. Localization therefore gives
$$Q(\chi)\,QF(te)=Q(v)\,QF(b).$$

Cited statements: lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, def-weil-abstract-derived-category, lem-sfb-condensed-derived-restriction-calculus.

### Returned step 9 -> parent assembly

Naturality of the derived unit in [def-sfb-right-derived-functor] gives
$$QF(b)=u_I^{-1}\circ R F(Qb)\circ u_K.$$
Since $ba=s$ and $Qa$ is invertible, functoriality gives $R F(Qb)=R F(Qs)\circ(R F(Qa))^{-1}$. Substitute this in step 8, and then use steps 5 and 6:
$$j\circ Q(\rho)=Q(v)\circ c_s\circ(R F(Qa))^{-1}\circ u_K=\epsilon\circ(R F(Qa))^{-1}\circ u_K.$$
Only $I$ and the auxiliary $T$ were required to have injective terms. In particular, this argument imposed no acyclicity condition on the given $K^n$ or $R_N^n$.

Cited statements: def-sfb-right-derived-functor, def-weil-abstract-derived-category.

## Searches and source checks

Before creating the nodes I searched the whole DAG for homogeneous/injective/coordinate/normalization statements and Stacks 03EV, 015Z, 013P and 013S, and ran blueprint_refs.py ancestor plus searches for homogeneous, homogeneous functions, equivariant injective, bar normalization, inhomogeneous and injective resolution. The ancestor tool returns None for this existing imported chain; new nodes preserve that result and prepend the item to its via chain. The discrete continuous-cochain nodes lem-sc-homogeneous-inhomogeneous-continuous-cohomology and lem-sc-homogeneous-cochain-evaluation-differential assume discrete topological integer coefficients and do not state the internal condensed result. The internal homogeneous-function injectivity node is reused as source material, not recreated. The internal bar-roof, product-bar, and norm-algcl augmentation statements concern respectively derived adjunction signs, product groups, and a particular normed coefficient augmentation, not this target construction or its coordinate model.

Every new node has actual msearch searches in searches.jsonl: natural-language LeanSearch and LeanFinder, Loogle and source grep, with a second semantic phrasing. I read the hits and then Mathlib/CategoryTheory/Preadditive/Injective/Preserves.lean (generic exact adjoint theorem at 49), Mathlib/RepresentationTheory/Homological/Resolution.lean (Rep.barComplex.isoStandardComplex at 420), GroupCohomology/Basic.lean (inhomogeneousCochainsIso at 148), and Abelian/Injective/Resolution.lean. Ordinary representations over a fixed ring and their external Hom are not arbitrary internal modules over a condensed ring, so the Rep coordinate isomorphism is not a one-line specialization of either new statement. The exact-adjoint theorem is one existing generic ingredient, not the concrete induction construction, underlying-resolution comparison and homogeneous injective total. No new Mathlib leaf was justified.

I read Stacks sites-modules.tex Tag 03EV, lemma-j-shriek-flat: the sheafified representable free module is flat for any site object, matching profinite parameters without a projectivity assumption. I read homology.tex Tag 015Z, lemma-adjoint-preserve-injectives: a right adjoint of an exact functor preserves injectives, with the adjoint direction L left of U. I read derived.tex Tag 013P, lemma-morphisms-lift (2), requiring a degreewise monic quasi-isomorphism for strict equality ba=s, and Tag 013S, lemma-morphisms-equal-up-to-homotopy, requiring only a quasi-isomorphism and bounded-below injective target. Tag 070K, lemma-enough-K-injectives-implies, supplies the generic computation background; the actual natural unit is stated by def-sfb-right-derived-functor.

## Review by Q79

For the item and both new statements I read the current direct-images blueprint paragraph (3) and the full normalization Lean docstring. They retain the open-direct-image route and ordinary internal module coefficients; no SGA route or solid/completed coefficients enter. I also opened every statement cited by the new parent. In parent step 1 the first new statement provides s, K-injectivity, Us and injective T with delta; the restriction-calculus statement explicitly makes derived invariants additive and its underived invariants are right adjoint to exact trivial inflation. In step 2 the second new statement explicitly gives chi, v, t, the coefficient-row square and epsilon's formula, rather than a mere cohomology isomorphism. Step 3 uses exactly the strict extension assertion of lem-weil-pbc-lift-along-injective-quasi-iso: nonnegative K makes a degreewise monic because H0(K)=ker(d0), and both source and target complexes are bounded below. Step 4 uses precisely the uniqueness-up-to-homotopy assertion for T and a; equality after a is verified from ea=augmentation, t augmentation=delta s and ba=s. Additivity preserves the written homotopy equation, and the cited derived-category definition localizes the homotopy category. Step 5 uses the natural unit of def-sfb-right-derived-functor, invertible on K-injective I, and functorial inversion of Qa from the derived-category definition. Each needed formula occurs in the cited statement, as copied into citations.json.

The first new statement is self-contained for arbitrary equivariant N (the parent specializes to trivial N), with explicit homogeneous value action, both differentials, finite totals and constant map. Its proof task carries all three original arguments: constructing nonnegative injectives, proving U preserves them via flat free induction, and proving the homogeneous terms and finite totals injective. The source helper lem-sfb-internal-homogeneous-functions-injective requires underlying injectivity, which the free-induction part supplies; it does not give injectivity merely from equivariant injectivity. The second task assumes precisely an equivariant injective resolution with underlying injectives, so it can be tackled independently of the first existence proof. It carries the inverse coordinate formulas and both face/vertical sign checks, the specified derived augmentation and the coefficient-row equality. Its isomorphism is stated in the ordinary derived category with the actual cochain representative, not just on individual cohomology groups. Neither new statement has proof steps or proof dependencies.

Small cases checked: N=0 permits the zero resolution and all displayed arrows zero; G=1 reduces prefix coordinates to the identity on values and the unnormalized bar differential alternates zero/identity as deletion does; p=0 makes chi evaluation at 1 and inverse h0 acting on the value, so the first face is the action-dependent g1 c-c term, not incorrectly zero for I0. Finite totals in degree zero have the sole (0,0) summand and in degree one have (1,0),(0,1), with vertical signs -,+ respectively. For a general nontrivial action on I the inverse coordinate map includes h0's action; no discreteness or open-stabilizer condition is smuggled in. Strict monicity of a uses K^{-1}=0; it would fail for a general unbounded resolution, which is why this hypothesis is retained. No termwise acyclicity of the supplied K or R_N is introduced.

I checked delivery-errors B-E individually: statement-only new nodes, all objects/hypotheses and definitions explicit, source tags checked above, literal TeX and real searches, blueprint ancestry preserved; every non-elementary parent assertion is in a cited statement, all citation quotes copied, no parent-to-child cycle or geometric route substitution; the two new tasks divide construction and coordinate compatibility rather than restating target clauses; hypotheses for strict lifting and homotopy uniqueness checked as above. No parent step exceeds 2000 characters and its total is below 3000. The full old proof is retained above so this repair does not erase work. No mathematical change to the parent's statement was needed.

## Not duplicates

lem-sfb-homogeneous-injective-total-target vs lem-pe-injective-complex-slice-section-model: the existing statement is A single injective complex gives compatible derived section models on slice sites; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-sf-fixed-pair-derived-forget-comparison: the existing statement is Derived forgetting of fixed pairs and right derived functors; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-coef-module-flat-cotorsion-foundation: the existing statement is The module-level flat cotorsion pair on a small ringed site; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-coef-flat-complex-cotorsion-pairs: the existing statement is Small complete cotorsion pairs of flat sheaf complexes; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs def-trf-total-etale-augmentation-adjunction: the existing statement is Canonical adjunction of a total small etale augmentation; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-trf-total-site-component-restriction: the existing statement is Exact conservative component restriction on a total simplicial site; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-trf-finite-map-dualizing-transfer: the existing statement is Transfer of a dualizing complex along a finite ring map; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-pc-sites-modules-j-shriek-flat: the existing statement is Extension by zero of the unit module is flat; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-pc-kflat-bounded-flat-replacement: the existing statement is Bounded-above flat replacement on a ringed site; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-sp-right-adjoint-preserves-injectives: the existing statement is Right adjoints of exact functors preserve injectives; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-sfb-internal-homogeneous-functions-injective: the existing node proves injectivity of one homogeneous function object given underlying injectivity; the new task supplies compatible underlying injective resolutions and a signed total complex with constants, using that existing result.

lem-sfb-homogeneous-injective-total-target vs lem-sfb-condensed-derived-invariant-bar: the existing node identifies derived invariants with the derived inhomogeneous bar; the new statement constructs the distinct homogeneous equivariantly injective target and forgetful injective resolution, needed for chain-homotopy comparison.

lem-sfb-homogeneous-injective-total-target vs lem-sfb-relative-cyclic-restriction-model: the existing statement is Relative cyclic restriction model and forgetting the residual action; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs sk-lem-proper-heart-bound: the existing statement is A uniform bound for proper direct image; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-sfb-equivariant-resolution-bar-normalization: the parent asserts the final normalized arrow for arbitrary augmentation-preserving evaluation; this child constructs compatible injectives and an auxiliary homogeneous injective total, with no such arrow equality.

lem-sfb-homogeneous-injective-total-target vs lem-sfb-discrete-lattice-koszul-resolution: the existing statement is Discrete lattice derived invariants via a sheaf-module Koszul resolution; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-sfb-internal-bar-roof-adjunction: the existing statement is Internal bar cocycle roofs and the normalized derived adjunction; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs sk-def-sfb-module-derived-pushpull: the existing statement is Derived pushforward and pullback of module objects; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-sfb-condensed-product-bar-comparison: the existing statement is Product and iterated derived internal bars, with augmentation normalization; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-sc-field-scalar-restriction-injectives: the existing statement is Restriction of module sheaves to a field preserves injectives; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-per-etale-point-product-acyclic: the existing statement is Geometric-point product sheaves: adjunction, exactness and evaluation acyclicity; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-per-exact-comma-injectives: the existing statement is Injective objects in the comma category of an exact left adjoint; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-site-leray-degenerate: the existing statement is Vanishing higher direct images: cohomology of the direct image equals cohomology upstairs; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-injective-abelian-sheaf-injective-presheaf: the existing statement is An injective abelian sheaf on the small etale site is an injective abelian presheaf; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-derived-sections-pushforward: the existing statement is Derived global sections via comparison pushforward; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-module-injective-open-cover-cech-acyclic: the existing statement is An injective module has vanishing higher Cech cohomology for every open covering; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-scheme-modules-enough-injectives: the existing statement is Sheaves of modules on a scheme have enough injectives; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-colimit-of-sites-injective-system: the existing statement is Embedding a system of abelian sheaves on an inverse system of sites into a system of injectives; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-flat-module-pullback-exact-pushforward-injective: the existing statement is Flat module pullback is exact and direct image preserves injectives; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-sheaf-flat-separator: the existing statement is Sheaves on an essentially small site have a flat separator (Lean split); the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-free-yoneda-presheaf-module: the existing statement is Morphisms out of the free presheaf of modules on a representable are sections; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-direct-image-preserves-injectives: the existing statement is Direct image preserves injectives; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-zariski-open-restriction-injectives: the existing statement is Restriction of abelian Zariski sheaves to an open is exact and preserves injectives; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-free-sheaf-flat: the existing statement is The sheafified free presheaf on a representable with flat coefficients is flat (j_{X!} of a constant flat sheaf is flat); the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-equivalence-injective-resolutions: the existing statement is An additive equivalence of abelian categories carries injective resolutions to injective resolutions; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-exact-adjoint-tower-models: the existing statement is Simultaneous exact-adjoint K-injective tower and normalized Roos models; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-module-open-restriction-injectives: the existing statement is Restriction of modules to an open subscheme is exact and preserves injectives; direct image along the open immersion preserves injectives; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-scheme-modules-functorial-injective-embeddings: the existing statement is Sheaves of modules on a scheme have functorial injective embeddings (Stacks 01DI); the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-injective-module-injective-presheaf: the existing statement is An injective module sheaf is injective among presheaves of modules; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-exc-equivalence-derived-sections: the existing statement is Derived section functors under an additive equivalence; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs thm-exc-curve-open-dimension-general: the existing statement is Open direct-image dimension on arbitrary curves; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-cbc-etale-derived-direct-image-coherence: the existing statement is Ordinary etale derived direct-image composition and its coherence; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-pur-supported-bottom-gluing: the existing statement is Gluing supported cohomology in its lowest local degree; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-dg-etale-injective-finite-cech-rows: the existing statement is Split finite ordered Cech rows for injective etale module sheaves; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-pur-etale-support-map-compatibility: the existing statement is Etale proper-support normalization intertwines exchange and projection; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-ringed-site-injective-module-injective-presheaf: the existing statement is Injective module sheaves are injective as module presheaves; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs cohomology-site-equivalence-fixed-degree: the existing statement is Fixed-degree cohomology comparison for an equivalence of sites; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-weil-pbc-cohomology-over-object-localization: the existing statement is Cohomology over an object is cohomology on its localized site; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-exc-rg-adjoint-transfer-functorial-injectives: the existing statement is Adjunction transfer of functorial injective embeddings; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-injective-total-target vs lem-exc-rg-right-adjoint-preserves-injectives: the existing statement is A right adjoint of a monomorphism-preserving functor preserves injective objects; the new task is specifically the compatible internal profinite-action injective resolution and its homogeneous injective double-complex total. Shared flatness/adjoint tags are generic ingredients and do not assert this construction.

lem-sfb-homogeneous-bar-coordinate-normalization vs lem-sfb-condensed-derived-invariant-bar: the existing node identifies derived invariants with an inhomogeneous derived total; the new task specifies the homogeneous-to-inhomogeneous total coordinates and the strict coefficient-row square for an arbitrary cochain e. It uses the existing bar theorem for the normalized epsilon, not a duplicate existence theorem.

lem-sfb-homogeneous-bar-coordinate-normalization vs def-sfb-condensed-equivariant-bar-data: a definition/specification of normalized bar data does not establish the concrete homogeneous coordinate cochain isomorphism or its coefficient-row equality.

lem-sfb-homogeneous-bar-coordinate-normalization vs lem-sc-homogeneous-inhomogeneous-continuous-cohomology: discrete topological integer cochains versus internal module sheaves over any condensed ring, with a compatible-resolution derived total and augmentation square.

## Unfinished work

Only the proofs of the two deliberately unsplit new nodes remain for their future workers, as required by the return. The parent is completely assembled from their statements and existing lifting/unit tools. Validation and delivery results are recorded below after the remote dry run.

## Validation

The required deliver.py --no-push exited successfully with OK at dry-run commit 167278c8cd7; server preflight, including DAG and split checks, passed. The parent has five steps totaling 1747 characters; its largest step is 465 characters. The two new nodes have six actual logged searches each, empty proof fields, status unsplit, and no Mathlib match. The parent statement matches the current read repository byte for byte as a JSON string. No local checker, Lean compiler or Lake command was used.
