## Files written

- dag/nodes/sec-smooth-purity/lem-sp-tower-compact-support-projection-formula.json: unchanged statement; three-step assembly (1404 characters).
- dag/nodes/sec-smooth-purity/lem-sp-finite-level-projection-factors.json: statement-only unsplit lemma, finite proper/open factors plus exact coefficient presentation transport; no Mathlib match.
- dag/nodes/sec-smooth-purity/lem-sp-tower-projection-domain-evaluation.json: statement-only unsplit lemma, uniform tensor models and actual projection-map evaluation; no Mathlib match.
- citations.json: verbatim statements for every citation in the assembly.

## Attachments

None. Searching WeilConjectures for the blueprint tag gives no declaration of the item. The live Sheaf.Paper.TowerCompactSupportProjectionFormula main theorem at line 345 has sorry at line 365; its evaluation and naturality helpers are also unfinished. The pro-etale open projection theorem in WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/LowerShriek/Open/Projection.lean treats only one operation, not this tower theorem or the full new lemmas. No Lean was written or compiled.

## WANTED

None for this repair. The coefficient comparison source nodes already document their own provenance. In particular Bhatt–Scholze Proposition 5.3.2 is about the classical derived-category comparison, not a standalone condensed-constant-ring comparison theorem; the finite-discrete comparison is used through the existing explicit nodes, not attributed wholesale to that proposition.

## Returned order and repairs

The sandbox contained no node or report at dispatch, only dispatcher .brief files. I therefore copied the current live six-step returned node, including its maintainer metadata, to the sandbox. returned-node.json preserves that input. The released stage-1 repair note keeps the statement and proof route. The new statements divide the work into two comparable arguments: finite coefficient interpretation and finite proper/open invertibility (old steps 1,4,5); uniform tensor preparation and coherent tower-map construction/evaluation (old steps 2,3). Old step 6 stays as the parent's assembly. Neither node asserts the parent's two tower maps are invertible: the finite node has no towers, and the tower node asserts no projection invertibility. Both are delivered unsplit with empty proof and proof_deps and null proof_origin. No target statement, unit, chapter, Lean record or maintainer metadata is changed. There is no source statement dispute.

The complete old arguments are retained below, not shortened. Their statements have become independently claimable work; the report supplies all their original proof steps and citations to the future workers. The parent is below 3000 characters and has no step above 2000. The new nodes are not split in this delivery.

## Review by Q59

I read the chapter and sk-prop-sp-integral-adjunction unit, the main-20261015 integral-direct-image-tower proof paragraph (3), the current item including its previous review, and every statement cited by the six returned steps. Paragraph (3) calls for a genuine tower projection formula from finite projection, which this repair preserves. I read the finite proper proof in main-20261015/sec-six-functors-basics/sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-finite.proof.md, its Stacks Tag 0F0G (etale-cohomology-lemma-projection-formula-proper-mod-n), and the open projection proof in main-20261015/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-extension-zero-projection-formula.proof.md. I also read Stacks 08G1 (sites-cohomology-lemma-tor-amplitude), 0G7E (sites-cohomology-lemma-pullback-K-flat), and the derived-tensor construction 06YU. The new nodes state precise derived maps and model conclusions, not per-degree substitutes for derived isomorphisms.

For assembly step 1, sk-def-sp-normalized-towers explicitly supplies uniform cohomology and Tor intervals without normalization. The new tower-domain node explicitly supplies boundedness of both tensor inputs, canonical natural tower arrows, and evaluation of the specified counit/unit transposes and their direct-image composite. Thus no existence of lifts of arbitrary finite maps is inferred. Step 2 uses the coefficient-extension node's finite uniformizer quotients and factorization of a nonzero field element, with ell=u varpi^e and positive e. The standing-setting node says compactifications stay separated finite type over the same field. The normalized-towers definition supplies intrinsic finite constructibility and finite Tor, while the new finite-factors node expressly states coefficient interpretation, finite proper/open invertibility and their directions. Applying a functor to an inverse is elementary. Step 3 uses precisely clause 3 of det-sp-tower-shriek-levels, which detects isomorphisms in the ordinary unbounded tower category. It never uses clause 2(a), whose field and origin hypotheses are stronger. Composition of natural isomorphisms and inversion are elementary. All step uses have verbatim quotes in citations.json, and proof_deps equals their union.

The finite new node introduces A, k, all schemes and arrows and both adjunction transposes. The bounded constructible finite-Tor hypotheses of finite proper projection hold for j_!C because det-proper-image-localizing-open states that preservation. Its input category is the internal-module one, so the statement includes the full derived presentation comparison and units/counits required to transfer actual maps. The open map has source j_!(C tensor j^{-1}L); its inverse is the displayed canonical comparison, as checked with the source's Yoneda/unit-counit construction. No arbitrary inverse is called the projection map. Every non-elementary piece of the inherited handoff names an existing node below.

The tower new node introduces all its categories, bounds and maps and deliberately requires only uniform cohomology of C and uniform Tor of B. Testing B_n against the coefficient sheaf itself gives uniform cohomology of B. Good truncation and exact j_! supply bounded T and j_!T. Stacks 08G1 gives bounded flat P; bounded-above flat implies K-flat, and the K-flat pullback lemma retains flat terms. The inherited cone argument and signed total tensor identify the model, so the asserted interval is [a+u,b+v] on both schemes. Exact level evaluations with componentwise kernels/cokernels then give the tower interval. Independently chosen level models are not asserted to be a strict tower. The coherent section lemma constructs the actual tower adjunction maps before evaluation and states that transposes evaluate to finite ones. Bounded-below F comparisons apply to C and its tensor, now proved bounded below. These hypotheses require neither normalization nor etale-origin witnesses.

I tested zero complexes, empty X or Y (when the morphisms exist), j=id, p=id, and intervals with equal endpoints. The maps reduce to the appropriate unit/tensor identities, the interval sum stays correct for shifted coefficient sheaves, and all zero cases give zero complexes. Singular finite rings such as Z/ell^2 are allowed: the node retains finite Tor for B rather than incorrectly using an arbitrary nonflat module as its bounded flat model. The finite node includes the zero ring; its module categories are zero. The general field k is never replaced by an algebraic closure of a finite field. The finite coefficients O_E/ell^n remain admissible even for ramified E. None of these checks exposes a statement error.

Before creating the nodes I searched the whole DAG by titles, statements, tags and keywords and the whole blueprint with blueprint_refs.py (projection finite condensed; tower tensor bounds; projection tower, saved in the sandbox). I read the closest candidates, especially the existing finite proper theorem, finite open theorem, coefficient-equivalence and operations-transport lemmas, the semilinear-section lemma, lem-sp-ringed-site-tor-flat-model, lem-sf-proetale-pf-admissible-models, lem-sf-boundary-bounded-tensor-comparison and the ringed tensor cohomological-bounds lemma. The specific distinctions are below. Existing nodes are used in the handoff, not recreated. The human's explicit re-split order calls for new intermediate statements whose independent proofs can be assigned separately; these statements combine different operations and no existing node states either complete result.

All new Mathlib searches were actually run by msearch.py and read, twice with distinct semantic phrasings for each statement. LeanSearch's finite query returned sheaf equivalences, sheafification counits and scheme-module restriction counits, none of which asserts derived pro-etale projection or coefficient transport. Its tower query returned HomologicalComplex.tensorObj/tensorHom and group-homology Tor computations, which construct tensors without the required derived system bounds and adjunction evaluation. LeanFinder returned condensed module and light-condensed monoidal structures, not these derived scheme and system statements; the second tower query also returned localCohomology.diagram. The grep finite hits are comments in Monad/Algebra about generated projection lemmas; the tower hits concern semilinear subsets in Presburger arithmetic. Loogle returned no hits for either requested pair of names. Exact queries, available status and actual top hits are in searches.jsonl and in each node. No match is a one-line specialization, and no unavailable search is called empty.

## Not duplicates

lem-sp-finite-level-projection-factors vs det-thm-sf-pf-adic-projection: uses integral O_E condensed coefficients and proves proper projection only; the new finite-A statement also specifies open factors and their coefficient presentation transport.

lem-sp-finite-level-projection-factors vs sk-thm-sf-pf-adic: uses integral O_E localizing categories; it does not give the finite constant-ring factor maps or their internal/ordinary identification.

lem-sp-finite-level-projection-factors vs lem-etale-proper-projection-formula-finite: is an etale proper projection theorem only; the new node concerns pro-etale finite constructible inputs, open factors and internal/ordinary derived transport.

lem-sp-finite-level-projection-factors vs lem-fix-proper-etale-origin-scalar-isomorphism: compares proper direct image under A-to-B scalar extension for specified etale-origin inputs, not the two-factor projection with arbitrary finite-Tor B.

lem-sp-finite-level-projection-factors vs lem-etale-proper-projection-formula-finite-objectwise: states only etale proper projection component invertibility, not pro-etale open projection and coefficient presentation transport.

lem-sp-finite-level-projection-factors vs lem-etale-projection-formula-finite-geometric-point: assumes a geometric-point base and concerns an etale proper projection; the new node has arbitrary standing base Y and includes the open/unit comparison.

lem-sp-finite-level-projection-factors vs lem-sp-finite-ring-compact-support-projection: assumes the algebraic closure of a finite field and states the combined compact-support arrow; the new node uses an arbitrary standing field and identifies the two individual factors and coefficient transport.

lem-sp-finite-level-projection-factors vs lem-fix-etale-proper-coefficient-tensor-unit: is an etale scalar-extension universal-property theorem, not a pro-etale projection factor theorem or internal/ordinary coefficient comparison.

lem-sp-finite-level-projection-factors vs lem-kun-proper-base-change-torsion-ring: is proper base change across a cartesian square, with no assertion of either projection factor or coefficient presentation transport.

lem-sp-tower-projection-domain-evaluation vs lem-pe-coefficient-tor-flat-model: gives a single ringed-site Tor/flat-model equivalence, not sum-of-interval tensor bounds for varying-ring systems or evaluation of projection transposes.

lem-sp-tower-projection-domain-evaluation vs lem-sf-proetale-pf-admissible-models: assumes finite-field geometry and etale-origin models at one coefficient stage; the new node handles ordinary varying-ring towers on arbitrary schemes with no origin witnesses and also evaluates actual tower adjunction maps.

lem-sp-tower-projection-domain-evaluation vs lem-sfb-split-perfect-dual-tor-window: concerns the dual of a bounded degreewise split finite-projective complex; it has no varying-ring system, second tensor input, open extension or projection-map evaluation.

lem-sp-tower-projection-domain-evaluation vs lem-sp-bounded-flat-coefficient-site-square: compares scalar/site changes of a supplied bounded flat complex at one coefficient stage, not uniform tensor bounds for two towers or actual proper/open map evaluation.

lem-sp-tower-projection-domain-evaluation vs lem-sp-ringed-site-tor-flat-model: is the single-object bounded flat representative equivalence; the new node further calculates both compactification tensors uniformly and constructs/evaluates their projection maps.

lem-sp-finite-level-projection-factors vs det-thm-sfb-proper-base-change-finite: that node gives the internal-module proper factor only; the new node retains open/unit factor, finite intrinsic constructibility interpretation, and actual adjunction-mate transport. It is a separate finite-level comparison task, not a renaming of proper projection.

lem-sp-finite-level-projection-factors vs lem-sf-module-object-ordinary-coefficient-equivalence: that node preserves derived categories, tensor and Dctf, and the Rp_*j_! composite; it does not identify both derived projection transposes or assert their individual invertibility.

lem-sp-finite-level-projection-factors vs lem-sfb-internal-module-operations-transport: that node identifies underived operations and adjunctions; the new node also states derived adjunction and projection-factor normalization with finite proper/open invertibility.

lem-sp-tower-projection-domain-evaluation vs lem-coef-semilinear-derived-sections: that node constructs and evaluates operations in generality but does not assert uniform interval-sum bounds or the independent finite flat representatives needed here.

lem-sp-tower-projection-domain-evaluation vs det-sp-tower-shriek-levels: only bounded-below evaluation and conservativity are generic there; its projection invertibility clause requires a finite-field setting and etale-origin witnesses. The new node proves the tensor domain and evaluates the individual transposes without such hypotheses, and claims no invertibility.

lem-sp-tower-projection-domain-evaluation vs lem-sf-boundary-bounded-tensor-comparison: that single-stage etale closed-immersion comparison has finite-field and constructibility hypotheses; the new statement handles arbitrary-scheme varying-ring towers, an open/proper compactification and evaluation of both transposes.

lem-sp-tower-projection-domain-evaluation vs lem-weil-pbc-ringed-tensor-cohomological-bounds: that node bounds extension of scalars R-to-S from Tor-vanishing assumptions on cohomology; it gives neither two-input finite-interval tower bounds nor proper/open mate evaluation.

## Complete inherited arguments for the new workers

The following is source material for later splits, not proof fields of the new statement-only nodes. All six old arguments are copied verbatim, with every uses-list. Steps 1,4,5 belong to lem-sp-finite-level-projection-factors; steps 2,3 belong to lem-sp-tower-projection-domain-evaluation; step 6 stays in the parent assembly.

### Returned step 1

At level $n$ the coefficient ring $A_n=\mathcal O_E/\ell^n$ is finite and killed by a power of $\ell$: writing $\ell=u\varpi_E^e$ identifies it with $A_{E,en}$ [def-weil-l-adic-coefficient-extension]. The two finite-discrete coefficient identifications [lem-weil-pbc-finite-discrete-condensed-ring-constant, lem-weil-pbc-finite-discrete-scheme-ring-constant], followed by [def-weil-pbc-internal-abelian-sheaf-module-equivalence], identify module objects over the pulled-back condensed $A_n$ with ordinary module sheaves over the constant ring $A_{n,T}$. The equivalence preserves underlying sheaves. By [lem-sf-module-object-ordinary-coefficient-equivalence] its termwise extension is an equivalence of unbounded derived categories preserving derived tensor, Tor intervals and the $\Dctf$ subcategories of [sk-def-sfb-constructible], and identifying the module-object $Rp_*D(j_!)$ with the ordinary $Rp_*j_!$. By [lem-sfb-internal-module-operations-transport] it identifies inverse image, direct image and open extension by zero with the ordinary ones, together with their adjunction units and counits. Since the equivalence is exact, the derived direct images, being derived functors of identified functors, also correspond, with their derived adjunctions. Hence the finite projection maps, formed from these tensors, pullbacks, direct images and units/counits, correspond as well. For finite $A_n$, finite constant local models in [sk-def-sfb-constructible] are exactly locally constant finite $A_n$-modules: a finitely presented module is finite, and a finite module has a presentation by finitely many generators whose relation module is finite, hence finitely generated. Thus the intrinsic finite constructibility and Tor tests in [sk-def-sp-normalized-towers] are those of the finite-coefficient statements used below. The compactification stays in the standing separated finite-type setting [sk-def-sfb-dc-setting].

Cited node statements to use: def-weil-l-adic-coefficient-extension, lem-weil-pbc-finite-discrete-condensed-ring-constant, lem-weil-pbc-finite-discrete-scheme-ring-constant, def-weil-pbc-internal-abelian-sheaf-module-equivalence, sk-def-sfb-constructible, sk-def-sp-normalized-towers, sk-def-sfb-dc-setting, lem-sf-module-object-ordinary-coefficient-equivalence, lem-sfb-internal-module-operations-transport

### Returned step 2

Choose uniform cohomological bounds $[a,b]$ for $C_n$ and a Tor interval $[u,v]$ for $B_n$ [sk-def-sp-normalized-towers]. By [lem-sp-ringed-site-tor-flat-model], represent $B_n$ by a flat complex $P_n$ supported in $[u,v]$. It is K-flat by [lem-pc-bounded-above-flat-kflat-site]; its inverse images are K-flat with flat terms [lem-weil-pbc-ringed-topos-kflat-pullback]. Good truncation represents $C_n$ by $T_n$ supported in $[a,b]$ [def-kun-truncations]; exact degreewise open extension gives the same bounds for $j_!T_n$ [lem-cbc-proetale-extension-zero]. For either bounded representative $T$ and the corresponding pulled-back $P_n$, choose a flat-term K-flat resolution $Q\to T$ [lem-pc-kflat-resolution]. Its acyclic cone stays acyclic after tensoring with the K-flat $P_n$ [def-pc-kflat-complex]; the total tensor of that cone is the cone of the tensored map, directly from the signed total differential. Thus $Q\otimes P_n\to T\otimes P_n$ is a quasi-isomorphism. The two-K-flat comparison [lem-weil-pbc-site-derived-tensor-descent] now shows that $T\otimes P_n$ computes the derived tensor. Its terms have degrees $r+s$ with $a\le r\le b$ and $u\le s\le v$, hence vanish outside $[a+u,b+v]$. Evaluation/tensor compatibility [lem-coef-semilinear-derived-sections] and levelwise kernels and cokernels [det-sp-coefficient-towers-abelian] give this bound for both tower tensors. The same levelwise cohomology test puts $C_\bullet$, $B_\bullet$, and $j_{!,\bullet}C_\bullet$ in $D^+$. These separate flat representatives only test bounds; they need not form a strict tower.

Cited node statements to use: sk-def-sp-normalized-towers, lem-sp-ringed-site-tor-flat-model, lem-weil-pbc-ringed-topos-kflat-pullback, def-kun-truncations, lem-cbc-proetale-extension-zero, lem-weil-pbc-site-derived-tensor-descent, lem-coef-semilinear-derived-sections, det-sp-coefficient-towers-abelian, lem-pc-bounded-above-flat-kflat-site, lem-pc-kflat-resolution, def-pc-kflat-complex

### Returned step 3

Use the simultaneous section models of [lem-coef-semilinear-derived-sections] for the ring system $(A_{n,T})_n$. Its clause on the coefficient projection comparison constructs $\pi_p$ as the counit transpose specified in the statement, and its clause on open localization and transposes constructs $\pi_j$ from the open unit. These are actual morphisms of derived towers, natural in both inputs. Evaluation preserves tensor, composition, units/counits and taking these transposes by that same lemma; therefore $(\pi_p)_n$ and $(\pi_j)_n$ are exactly the corresponding finite proper and open projection maps, not arbitrary choices of levelwise isomorphisms. The comparison of clause 1 of [det-sp-tower-shriek-levels] identifies $(F_fD)_n$ with $Rp_*j_!D_n$ for each of the bounded-below inputs $D=C$ and $D=C\otimes^Lf^{-1}B$ obtained in step 2. These identifications also identify the evaluated map $Rp_{*,\bullet}(\pi_j)$ with $Rp_*((\pi_j)_n)$.

Cited node statements to use: lem-coef-semilinear-derived-sections, det-sp-tower-shriek-levels

### Returned step 4

For every $n$, step 1 places $C_n$ and $B_n$ in the finite-coefficient $\Dctf$ categories. Since $j$ is an open immersion in the standing setting and $A_n$ is an admissible finite coefficient ring, [det-proper-image-localizing-open] gives $j_!C_n\in\Dctf(\overline X,A_n)$. Apply clause 3 of [det-thm-sfb-proper-base-change-finite] to the proper morphism $p$, the input $K=j_!C_n$, and $M=B_n$. It says that the proper projection map $Rp_*j_!C_n\otimes^LB_n\to Rp_*(j_!C_n\otimes^Lp^{-1}B_n)$ is invertible. This is $(\pi_p)_n$ by step 3. Neither finite-coefficient theorem assumes that the standing field is algebraically closed or finite.

Cited node statements to use: det-proper-image-localizing-open, det-thm-sfb-proper-base-change-finite

### Returned step 5

Apply [lem-cbc-extension-zero-projection-formula] with $K=C_n$ and $L=p^{-1}B_n$. Its canonical finite open projection isomorphism is written in the direction $j_!C_n\otimes^LL\to j_!(C_n\otimes^Lj^{-1}L)$. Its inverse is the open-unit transpose $(\pi_j)_n$ of step 3: under $j_!\dashv j^{-1}$ the latter map corresponds to $\eta_{C_n}\otimes1$, using the tensor/pullback identification, and composing with the displayed canonical comparison gives the adjunct of the identity by the unit/counit triangle identities. Thus $(\pi_j)_n$ is invertible. Applying the functor $Rp_*$ preserves its inverse, so every evaluation of $Rp_{*,\bullet}(\pi_j)$ is invertible as well.

Cited node statements to use: lem-cbc-extension-zero-projection-formula, lem-coef-semilinear-derived-sections

### Returned step 6

Clause 3 of [det-sp-tower-shriek-levels] detects isomorphisms in the unbounded ordinary derived category of towers. Steps 4 and 5 therefore make both $\pi_p$ and $Rp_{*,\bullet}(\pi_j)$ isomorphisms. Compose $\pi_p$ with the inverse of $Rp_{*,\bullet}(\pi_j)$ to obtain the asserted natural isomorphism $F_fC_\bullet\otimes^LB_\bullet\simeq F_f(C_\bullet\otimes^Lf^{-1}B_\bullet)$. The maps were natural before testing invertibility, so their composite with the inverse is natural too. No normalization or compatibility of independently chosen finite flat representatives is needed.

Cited node statements to use: det-sp-tower-shriek-levels

## What remains

No part of this stage-1 repair is intentionally left unfinished. The two new statements remain unsplit by the explicit repair order; their proofs are separate queue items. Delivery checks follow this report.
