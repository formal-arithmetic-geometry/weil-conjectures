# Stage-1 repair: prop-weil-pbc-direct-image-limits

1. Files written: the item JSON, citations.json, and the following five new statement-only nodes, each status `unsplit`, with no proof steps, no proof dependencies, and no Mathlib match:
   - lem-weil-pbc-reduction-pullback-derived-tower: normalized derived tensor/pullback of an augmented coefficient tower.
   - lem-weil-pbc-constant-tower-pushforward-normalization: constant-tower and inverse-limit normalization for arbitrary identified ring sheaves.
   - lem-weil-pbc-augmented-diagram-projection-mate: strict diagram projection mate, its evaluations and its augmentation identity.
   - lem-weil-pbc-direct-image-roos-normalization: the prescribed inverse-limit comparison as a morphism of the canonical Roos triangles, including the boundary.
   - lem-weil-pbc-tower-derived-evaluation-normalization: evaluation comparison normalized by universal derived units, with the derived counit equation.
   The item has four assembly steps totaling 2097 characters, individually 429, 291, 651 and 726 characters. Its statement is identical to current main. Existing imported, Lean, and maintainer metadata is retained.
2. Attachments: none. Searches of lean/WeilConjectures for the blueprint tag, direct-image/limit notions and recorded completed-coefficient declaration names yielded no exact whole-item proof. The Sheaf implementation is reference material and still has sorry at lines 379 and 1348; its historical proof-landing record is not evidence that all clauses are closed.
3. WANTED: none. All sources below are present locally.
4. The earlier sandbox refinement had already isolated five useful lemmas but delivered them as split nodes. The explicit route note requires NEW statement-only nodes, not recursively completed splits. This repair empties their proof fields and records the retained arguments below for their later stage-1 workers. The parent statement stays unchanged. The old constant-coefficient specialization is replaced by the new arbitrary-ring-sheaf normalization; the existing generic ringed tower limit theorem is reused.
5. Mathematical work remaining: future stage-1 workers split the five new statements. No Lean was written and no compiler, Lake, or build tool was run. Delivery validation is recorded at the end when available.

## Review by NI

I read the returned human granularity decision and its route note, coord/brief-stage1.md, delivery-errors B through E, GOAL.md, the three blueprint levels of SETUP.md, and the chapter and unit records. I compared the retained item against current main: the statement is identical, and only proof, proof_deps, proof_origin and split_report differ. The four-step assembly follows the current main-20261015 proof in sk-prop-pbc-complete. This is an explicitly authorized re-split of the live reviewed item, below the unchanged unit route. The initial required dry-run attempt returned DELIVERY ALREADY RUNNING (exit 75); no duplicate entered the queue.

For the item and the new constant, evaluation and Roos normalization statements I read sites-cohomology.tex, Tag 0A07, lemma-Rf-commutes-with-Rlim, including its diagram-topos argument and its warning that Rlim is not an ordinary derived-category limit. For the Roos statement I also read derived.tex, Tag 0BK6, lemma-product-K-injective: the product is both K-injective and the product in the derived category. For the reduction statement I read sites-modules.tex, Tag 03EL, lemma-tensor-product-pullback, and sites-cohomology.tex, Tags 06YS, 06YY and 07A4, respectively lemma-K-flat-resolution, lemma-derived-base-change and lemma-pullback-tensor-product. For the augmented mate I read section-projection-formula (0943), Equation 0B56, and 07A4. The new statements make normalization and strict-diagram coherence explicit; they are refinements to be proved, not quotations claiming that Stacks prints their extra equations verbatim.

Assembly step 1 uses the statement of lem-weil-pbc-profinite-coefficient-inverse-image for the ring isomorphism and its compatible quotient maps. The operations definition explicitly supplies exact module pullback and its module adjunction, and lem-weil-ringed-tower-pushforward-limit-comparison explicitly supplies the total derived tower image, natural evaluated identifications and a_M induced by the common underived composite. Its small-site and module-sheaf hypotheses apply to the pro-etale presentations in the item; it imposes no properness or boundedness.

Step 2 uses lem-weil-proetale-countable-products-exact, whose statement allows every sheaf of commutative rings, so it applies to completed A_X and A_Y. This supplies exactly the extra hypotheses of the new Roos normalization statement. That statement includes invertibility, the 1-s square, the triangle boundary and identification of the first component with the specified a_M. Thus the assembly does not choose an unspecified cone isomorphism.

Step 3 uses the reduction/pullback statement to identify the entire quotient algebra tower, then the augmented-diagram statement to construct h_K as ONE morphism in the derived category of strict towers with evaluations the counit-tensor projection maps. The coefficient equations needed here were supplied in step 1. The existing perfect-projection-formula statement explicitly gives invertibility for the same finite perfect P_n and compatibility with quotient maps. The levelwise-abelian statement explicitly computes kernels and cokernels levelwise. Applied degree by degree to the cone, this makes its cohomology levelwise, so zero evaluated cohomology means zero tower cohomology. This is the elementary cone criterion for invertibility; it does not assume evaluations are faithful on derived morphisms.

Step 4 uses the augmentation identity from the new diagram-mate statement in the strict derived-tower category BEFORE taking Rlim. Constant normalization identifies a on Delta K with the identity. Applying Rlim and naturality of the existing a gives the displayed completion-map equality. I checked prop-weil-pbc-koszul-reconstruction supplies exactly an invertible c_K and c_K composed with kappa_K equal to comp_K; the intrinsic-completion definition names invertibility of that same kappa. Hence the isomorphisms established in steps 1 and 3 transport completeness and identify the claimed canonical composite. citations.json contains verbatim statement quotations for all citations of these four steps.

Each new statement introduces its ambient categories, objects and hypotheses. The reduction and augmented-mate statements permit arbitrary algebra-sheaf towers and do not assume flat quotients, perfectness or completeness. The constant statement allows arbitrary identified ring sheaves, unlike the old constant-Noetherian-coefficient lemma. The Roos statement assumes exact countable products on BOTH sites. The evaluation statement assumes Grothendieck abelian categories, an additive adjunction with exact left adjoint, and fixes its comparison by universal units; its counit clause specifies the adjunction, rather than a family of unnamed isomorphisms. The fifth lemma is used in the statements of the constant and augmented nodes, so remains reachable even though it is not a separate assembly step.

Small cases checked: zero complexes and coefficient rings, identity f, constant towers, I=A (all coefficients and categories are zero), and I=0 including the empty generator list. For I=0 the datum still requires A finite, since every P_n=A is finite. Z_p with I=(p) is the familiar nontrivial test. The generic lemmas require neither properness nor boundedness. New nodes do not repeat an item clause: they isolate strict-model descent, derived-unit normalization, cone normalization and augmentation coherence in more general settings; the parent still proves projection invertibility and completeness using existing statements.

I read the retained searches.jsonl results and matched every query in each new node to an actual logged search, retaining query texts unchanged. SheafOfModules.pullbackComp and pullbackPushforwardAdjunction concern ordinary module operations; mapping-cone comparison APIs do not identify the prescribed derived-limit comparison; abstract derived comparison APIs alone do not give these strict tower, tensor-unit and counit normalizations. No Mathlib leaf is claimed. Searches of the whole DAG by tag and notion and tools/blueprint_refs.py searches for constant tower, Roos, reduction pullback and evaluation normalization found no blueprint replacement for these refinements. The existing general ringed tower comparison is cited directly rather than recreated. Same-tag distinctions are retained below. No SGA source is used.

The numbered repair request is answered by five NEW unsplit statements and a short assembly, not an unchanged re-push. The retained proof sketches below are report material only, as the route note requires. Every new node has empty proof/proof_deps and null proof_origin. No recursive new-node proof is delivered.

## Not duplicates


lem-weil-pbc-augmented-diagram-projection-mate vs def-pd-section-derived-realization: defines transport of section-module operations and tensors; it does not construct the strict coefficient-tower projection or its augmentation equation.

lem-weil-pbc-augmented-diagram-projection-mate vs def-pd-section-derived-tensor-data: defines conjugate section tensors and localizations; it gives no projection mate on an augmented inverse sequence.

lem-weil-pbc-augmented-diagram-projection-mate vs lem-pd-module-ringed-topos-derived-comparison: compares internal condensed module operations with ringed operations for the fixed field setting; it has no arbitrary augmented coefficient tower.

lem-weil-pbc-augmented-diagram-projection-mate vs lem-pe-constructible-comparison-tensor-test-reflection: reflects tensor-homology vanishing along etale/pro-etale comparison; it has no direct-image projection or augmentation statement.

lem-weil-pbc-augmented-diagram-projection-mate vs def-weil-pbc-normalized-origin-scalar-comparisons: defines scalar restriction conjugates and quotient associators; it gives no ringed diagram projection mate.

lem-weil-pbc-augmented-diagram-projection-mate vs def-weil-pbc-ringed-tensor-square-presentation: defines data for a ringed square and tensor comparison; it is not a theorem constructing the diagram projection and unit identity.

lem-weil-pbc-augmented-diagram-projection-mate vs lem-weil-pbc-augmented-cech-tensor-pullback: concerns extended Cech complexes augmented towards the ring; ours concerns arbitrary inverse algebra towers with augmentation from the ring and the direct-image mate.

lem-weil-pbc-augmented-diagram-projection-mate vs lem-weil-pbc-constant-derived-normalization-universal: proves universality of one exact scalar restriction arrow; it has no geometric direct-image coefficient-tower mate.

lem-weil-pbc-augmented-diagram-projection-mate vs lem-weil-pbc-derived-adjunction-shift: gives shift compatibility of an ambient derived adjunction; it does not evaluate a tower projection or prove its augmentation equation.

lem-weil-pbc-augmented-diagram-projection-mate vs lem-weil-pbc-derived-scalar-extension-local-systems: constructs scalar-extension functors and etale/pro-etale local comparisons; it does not provide a geometric tower projection.

lem-weil-pbc-augmented-diagram-projection-mate vs lem-weil-pbc-finite-reduction-pullback-coherence: compares the two pullback paths around a Cartesian square at a finite coefficient; it has no direct-image projection for one whole augmented tower.

lem-weil-pbc-augmented-diagram-projection-mate vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: computes derived pullback on flat-term K-flat objects; it does not construct an augmented tower projection or its counit equation.

lem-weil-pbc-constant-tower-pushforward-normalization vs lem-weil-pbc-ordered-exchange-coefficient-comparison: requires a Cartesian scheme square and a complete adic input and compares ordered exchange after scalar restriction; it does not give this generic normalization for arbitrary ringed-topos objects.

lem-weil-pbc-constant-tower-pushforward-normalization vs lem-weil-pbc-ringed-strict-tower-projection-morphism: constructs projection for towers of bounded finite free complexes with augmentations; it does not assert this standalone constant-tower normalization for arbitrary ring sheaves.

lem-weil-pbc-constant-tower-pushforward-normalization vs lem-pur-compact-support-completed-projection-coherence: uses constant Noetherian coefficients, complete inputs and completion reflectors; it does not apply to arbitrary ring sheaves and arbitrary inputs here.

lem-weil-pbc-constant-tower-pushforward-normalization vs lem-pur-completed-coefficient-pushforward-comparison: uses finite extensions of Q_l and complete inputs and scalar restriction; it does not state the arbitrary-ring constant-tower normalization.

lem-weil-pbc-constant-tower-pushforward-normalization vs lem-sp-constant-direct-image-preserves-complete: asserts local completeness for constant Noetherian coefficients; it gives no normalized constant-tower comparison.

lem-weil-pbc-constant-tower-pushforward-normalization vs lem-sp-constant-scalar-direct-image-completeness: asserts vanishing of localized internal Homs under a constant-scalar direct image; it has no constant-tower comparison or normalization.

lem-weil-pbc-constant-tower-pushforward-normalization vs lem-weil-ringed-tower-pushforward-limit-acyclic: asserts limit acyclicity after pushing a K-injective tower; it does not give constant-tower or evaluation-unit normalization.

lem-weil-pbc-constant-tower-pushforward-normalization vs lem-weil-ringed-tower-pushforward-limit-comparison: supplies a_M and evaluation isomorphisms for general towers; it does not state the Delta comparison, its evaluated identity, or a_Delta normalization.

lem-weil-pbc-direct-image-roos-normalization vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing statement concerns complete-input exchange in a scheme square; it does not state the canonical a_M/product/connecting-arrow Roos triangle comparison for arbitrary ring sheaves.

lem-weil-pbc-direct-image-roos-normalization vs lem-weil-pbc-ringed-strict-tower-projection-morphism: the existing statement is about tensor projection for bounded finite free coefficient complexes; ours identifies the direct-image limit comparison on arbitrary tower Roos triangles.

lem-weil-pbc-direct-image-roos-normalization vs lem-pur-compact-support-completed-projection-coherence: the existing statement concerns completed projection for constant coefficients and complete inputs; it does not state the canonical a_M/product/connecting-arrow Roos triangle comparison for arbitrary ring sheaves.

lem-weil-pbc-direct-image-roos-normalization vs lem-pur-completed-coefficient-pushforward-comparison: the existing statement concerns adic Q_l coefficient restrictions and complete inputs; it does not state the canonical a_M/product/connecting-arrow Roos triangle comparison for arbitrary ring sheaves.

lem-weil-pbc-direct-image-roos-normalization vs lem-sp-constant-direct-image-preserves-complete: the existing statement concerns local completeness for a constant Noetherian ring; it does not state the canonical a_M/product/connecting-arrow Roos triangle comparison for arbitrary ring sheaves.

lem-weil-pbc-direct-image-roos-normalization vs lem-sp-constant-scalar-direct-image-completeness: the existing statement concerns localized Hom vanishing for constant scalars; it does not state the canonical a_M/product/connecting-arrow Roos triangle comparison for arbitrary ring sheaves.

lem-weil-pbc-direct-image-roos-normalization vs lem-weil-ringed-tower-pushforward-limit-acyclic: the existing statement concerns acyclicity of a limit applied to a pushed K-injective resolution; it does not state the canonical a_M/product/connecting-arrow Roos triangle comparison for arbitrary ring sheaves.

lem-weil-pbc-direct-image-roos-normalization vs lem-weil-ringed-tower-pushforward-limit-comparison: the existing node supplies canonical a_M but does not identify it with a map of the two canonical Roos triangles including the boundary; ours proves that additional normalization.

lem-weil-pbc-direct-image-roos-normalization vs lem-pc-ringed-space-product-kinjective: computes products of K-injectives only; it is cited, but gives no direct-image comparison or Roos boundary normalization.

lem-weil-pbc-direct-image-roos-normalization vs def-weil-pbc-common-stage-cones: defines finite-stage rational coefficient cone triangles; it has no inverse-sequence direct-image comparison.

lem-weil-pbc-direct-image-roos-normalization vs lem-weil-derived-limit-existence: asserts existence and models of derived limits; it does not specify the morphism of Roos triangles induced by direct image.

lem-weil-pbc-direct-image-roos-normalization vs lem-weil-derived-limit-roos-complex: gives the comparison lim J to a cone for one tower; ours identifies the map between two such triangles with the prescribed direct-image comparison.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-per-galois-descent-monodromy-tensor: concerns monodromy of modules descended along a finite Galois cover; no derived reduction tower or K-flat normalization is stated.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-per-local-system-tensor-monodromy: concerns tensor closure and monodromy of local systems; it does not compare derived coefficient towers with ringed pullback.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-pod-etale-stalk-tensor-scalar: compares ordinary tensor and scalar extension with geometric stalks; it has no derived tower or universal counit normalization.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-pod-lisse-tensor-and-scalar-extension: asserts stalk and lisse closure statements on the etale site; it does not treat arbitrary derived ringed coefficient diagrams.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-sfb-site-inverse-image-bilinear-adjunction: gives the ordinary additive bilinear adjunction; it does not derive strict tensor towers or retain their universal reduction counits.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-sfb-site-inverse-image-multimap-universal: gives an ordinary finite-family section-map universal property, not a derived coefficient-tower comparison.

lem-weil-pbc-reduction-pullback-derived-tower vs def-weil-pbc-canonical-ringed-tensor-comparison: defines normalized ordinary tensor data, not existence and descent of a whole derived reduction-tower isomorphism.

lem-weil-pbc-reduction-pullback-derived-tower vs def-weil-pbc-ringed-tensor-square-presentation: defines ordinary and derived edge/square data; it has no strict reduction-tower existence, augmentation or uniqueness conclusion.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-weil-pbc-algebraic-inverse-image-pairing-isIso: proves invertibility of a supplied ordinary tensor pairing; it does not construct or descend derived strict towers.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-weil-pbc-algebraic-inverse-image-pure-pairing: constructs the ordinary pure pairing only; it has no strict tower, resolutions or universal derived counit equation.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-weil-pbc-algebraic-inverse-image-tensor-comparison: constructs a natural ordinary inverse-image tensor comparison; ours derives and normalizes the whole augmented coefficient tower.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-weil-pbc-canonical-ringed-tensor-comparison-construction: constructs a normalized ordinary ringed tensor comparison, not its strict derived reduction-tower descent.

lem-weil-pbc-tower-derived-evaluation-normalization vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing statement concerns complete-input exchange in a Cartesian scheme square, not a general abelian-category evaluation comparison.

lem-weil-pbc-tower-derived-evaluation-normalization vs lem-weil-pbc-ringed-strict-tower-projection-morphism: the existing statement constructs projection on finite free complex towers, not universal-unit normalized evaluation for a general exact additive adjunction.

lem-weil-pbc-tower-derived-evaluation-normalization vs lem-pur-compact-support-completed-projection-coherence: the existing statement concerns constant-coefficient completed projection, not a general abelian-category evaluation comparison.

lem-weil-pbc-tower-derived-evaluation-normalization vs lem-pur-completed-coefficient-pushforward-comparison: the existing statement concerns DVR coefficient restriction, not arbitrary Grothendieck abelian categories.

lem-weil-pbc-tower-derived-evaluation-normalization vs lem-sp-constant-direct-image-preserves-complete: the existing statement concerns local constant-coefficient completeness, not the universal evaluation units and counits.

lem-weil-pbc-tower-derived-evaluation-normalization vs lem-sp-constant-scalar-direct-image-completeness: the existing statement concerns local Hom vanishing for constants, not evaluation of a derived adjunction.

lem-weil-pbc-tower-derived-evaluation-normalization vs lem-weil-ringed-tower-pushforward-limit-acyclic: the existing statement concerns inverse-limit acyclicity, not normalized derived evaluation.

lem-weil-pbc-tower-derived-evaluation-normalization vs lem-weil-ringed-tower-pushforward-limit-comparison: the existing statement gives evaluation isomorphisms but not their universal derived-unit equation or evaluated counit equation.

lem-weil-pbc-constant-tower-pushforward-normalization vs lem-sf-cbc-constant-tower-direct-image-normalization: the existing node assumes constant A coefficients and its adic quotient diagram; the new statement allows arbitrary identified ring sheaves and has no adic datum or completeness assumption.

lem-weil-pbc-augmented-diagram-projection-mate vs lem-weil-pbc-ringed-strict-tower-projection-morphism: the existing node requires bounded finite free coefficient complexes; Q_n here are arbitrary commutative algebra sheaves and need not be free or flat. It therefore cannot supply this quotient-diagram mate directly.

lem-weil-pbc-reduction-pullback-derived-tower vs lem-weil-isomorphism-derived-pullback-reduction-tower: the existing node requires a scheme isomorphism and DVR coefficients; ours handles an arbitrary geometric morphism with identified rings and an arbitrary strict algebra tower.

lem-weil-pbc-reduction-pullback-derived-tower vs lemma-weil-pbc-completed-pullback-reduction: the existing node concerns the completed pullback of complete inputs; ours concerns ordinary exact pullback on arbitrary inputs before completion.



## Retained arguments for future stage-1 workers

These are the earlier sandbox arguments, preserved as working notes; they are not proof steps in the new statement-only nodes.

### lem-weil-pbc-augmented-diagram-projection-mate

1. Realize towers on the small diagram sites [lem-weil-pbc-diagram-site-realization]. Componentwise inverse image and direct image form a geometric morphism: the adjunction is componentwise and finite limits are levelwise. Apply [lem-weil-pbc-ringed-projection-mate-exact] to $E=\Delta_XK$ and $Q_{Y,\bullet}$. The source is $B_Y(\mathcal GK)$ using $\chi$ of [lem-weil-pbc-constant-tower-pushforward-normalization], and its target is $\mathcal G^{\rm Tow}B_XK$ using [lem-weil-pbc-reduction-pullback-derived-tower]. These are the actual diagram tensors, so this constructs one tower morphism, natural in $K$ and in coefficient diagrams. The module and tower categories are Grothendieck by [lem-weil-pbc-small-module-diagrams-grothendieck], so the evaluation normalization hypotheses hold.

Cites: lem-weil-pbc-diagram-site-realization, lem-weil-pbc-ringed-projection-mate-exact, lem-weil-pbc-constant-tower-pushforward-normalization, lem-weil-pbc-reduction-pullback-derived-tower, lem-weil-pbc-small-module-diagrams-grothendieck.

2. Evaluate this adjunct on a flat-term K-flat representative. The comparison $\tau$ is ordinary tensor/pullback with the universal reduction counits [lem-weil-pbc-reduction-pullback-derived-tower]. Evaluation commutes with tensor by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] applied to the evaluation geometric morphism of [lem-weil-pbc-diagram-site-realization]. The normalized direct-image evaluations [lem-weil-ringed-tower-pushforward-limit-comparison] are computed on the same K-injective tower. Thus the evaluated transpose is exactly $f^*(\mathcal GK\otimes^LQ_{Y,n})\to f^*\mathcal GK\otimes^LQ_{X,n}\to K\otimes^LQ_{X,n}$; its adjunct is the stated projection map. The equality of the two adjunct descriptions follows by the same tensor-counit formula on diagram sites. The evaluation and counit normalizations used here are precisely [lem-weil-pbc-tower-derived-evaluation-normalization]. The strict constant-counit equation is supplied by [lem-weil-pbc-constant-tower-pushforward-normalization].

Cites: lem-weil-pbc-reduction-pullback-derived-tower, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-diagram-site-realization, lem-weil-ringed-tower-pushforward-limit-comparison, lem-weil-pbc-tower-derived-evaluation-normalization, lem-weil-pbc-constant-tower-pushforward-normalization.

3. In the coefficient variable apply naturality of the diagram projection mate to $\Delta_YR_Y\to Q_{Y,\bullet}$. Its value at the tensor unit is the identity [lem-weil-pbc-ringed-projection-mate-exact]. Hence its naturality square, after the $\chi$ identification, reads $h_K i_{Y,\mathcal GK}=\mathcal G^{\rm Tow}(i_{X,K})\chi_K$. The augmentation equation for $\tau$ [lem-weil-pbc-reduction-pullback-derived-tower] fixes the specified units on both sides. This derives the equality within the strict derived-tower category and uses no faithfulness of evaluations.

Cites: lem-weil-pbc-ringed-projection-mate-exact, lem-weil-pbc-reduction-pullback-derived-tower, lem-weil-pbc-constant-tower-pushforward-normalization.

### lem-weil-pbc-constant-tower-pushforward-normalization

1. The constant-tower functor $\Delta$ is exact by [lem-weil-tower-category-levelwise-abelian]. It is right adjoint to exact $\operatorname{ev}_1$: a map $N_\bullet\to\Delta V$ is determined by $N_1\to V$, its other components being precomposed with $N_n\to N_1$. Thus [lem-weil-pbc-right-adjoint-preserves-kinjective] implies that $\Delta J$ is K-injective whenever $J$ is. The same lemma applies to $G$ and $G^{\rm Tow}$, since their left adjoints $F,F^{\rm Tow}$ are exact.

Cites: lem-weil-tower-category-levelwise-abelian, lem-weil-pbc-right-adjoint-preserves-kinjective.

2. Choose $K\to J$ by [prop-pur-kinjective-resolutions-exist]. The equality $G^{\rm Tow}\Delta_XJ=\Delta_YGJ$ computes the two derived functors by [lem-weil-pbc-kinjective-total-derived]; [lem-weil-pbc-kinjective-hom-derived] makes it natural and independent of the resolution. Evaluation is the identity on this equality, including the derived units. The ordinary limit of $\Delta J$ is $J$, and the ordinary $G$-limit comparison on this tower is the identity of $GJ$. The normalization in [lem-weil-ringed-tower-pushforward-limit-comparison] therefore gives the asserted identity after $R\lim$. The evaluation and counit normalizations used here are precisely [lem-weil-pbc-tower-derived-evaluation-normalization]. The strict counit equation holds on the same representative $J$: both sides are the constant tower of the ordinary counit $FGJ\to J$, with identical derived-unit conjugations.

Cites: prop-pur-kinjective-resolutions-exist, lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-kinjective-hom-derived, lem-weil-ringed-tower-pushforward-limit-comparison, lem-weil-pbc-tower-derived-evaluation-normalization.

### lem-weil-pbc-direct-image-roos-normalization

1. The tower category is Grothendieck [lem-weil-pbc-small-module-diagrams-grothendieck], so take a K-injective tower resolution $M\to J$ [lem-weil-pbc-kinjective-functorial-existence]. Evaluation preserves K-injectives [lem-weil-tower-evaluation-kinjective]. Since $F,F^{\rm Tow}$ are exact, $G,G^{\rm Tow}$ preserve K-injectives [lem-weil-pbc-right-adjoint-preserves-kinjective]. Products of the $J_n$ and of $GJ_n$ are K-injective and compute derived products [lem-pc-ringed-space-product-kinjective]. The right-adjoint Hom calculation $\operatorname{Hom}(H,G\prod J_n)=\operatorname{Hom}(FH,\prod J_n)=\prod\operatorname{Hom}(H,GJ_n)$ proves that the ordinary product comparison is invertible and has components $G(p_n)$.

Cites: lem-weil-tower-evaluation-kinjective, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-pc-ringed-space-product-kinjective, lem-weil-pbc-small-module-diagrams-grothendieck, lem-weil-pbc-kinjective-functorial-existence.

2. Writing $t_n:J_{n+1}\to J_n$, both $s'\alpha$ and $\alpha G(s)$ have $n$-th component $G(t_n p_{n+1})$, hence are equal. Additivity gives the square for $1-s$. The explicit cone comparison of [lem-pur-roos-additive-comparison] therefore identifies the two shifted cones and their cone-triangle arrows, including the boundary. Its product-preservation hypothesis follows from the same adjunction calculation for any tower complex.

Cites: lem-pur-roos-additive-comparison.

3. The shifted cones here are K-injective: applying $\operatorname{Hom}^\bullet(N,-)$ for acyclic $N$ produces a shifted cone of acyclic Hom complexes; its degreewise split cone sequence makes it acyclic. This uses only the cone differential of [def-weil-abstract-derived-category]. Thus [lem-weil-pbc-kinjective-total-derived] computes $\mathcal G$ on this cone termwise. The normalized Roos comparison [lem-weil-strict-roos-comparison] identifies $\lim J$ with the cone by $(0,\iota)$. The cone comparison carries $G(0,\iota)$ to $(0,\iota')$ composed with the ordinary $G\lim$ comparison. Consequently its first derived-triangle component is exactly $a_M$ as normalized in [lem-weil-ringed-tower-pushforward-limit-comparison]. This proves the boundary square as well as the product square.

Cites: def-weil-abstract-derived-category, lem-weil-pbc-kinjective-total-derived, lem-weil-strict-roos-comparison, lem-weil-ringed-tower-pushforward-limit-comparison.

### lem-weil-pbc-reduction-pullback-derived-tower

1. Use [lem-weil-pbc-ringed-topoi-module-pullback-tensor] for the ordinary comparison. Its normalization follows by transposing its defining bilinear map under the module adjunction [lem-weil-pbc-ringed-topoi-module-adjunction]: a bilinear map to $G(H)$ transposes to the bilinear map of inverse images to $H$, hence $F(x\otimes q)$ goes to $F(x)\otimes F(q)$ [def-pur-sheaf-tensor-product, lem-sfb-site-inverse-image-bilinear-adjunction]. For $v:Q_b\to Q_a$, either path sends this generator to $F(x)\otimes F(v(q))$; for the algebra unit either sends $F(x)$ to $F(x)\otimes1$. These formulas commute with restrictions and differentials, giving one augmented tower comparison. Transposing its inverse by the scalar-extension adjunction gives the same map as restriction/pullback, since both send $x$ to $x\otimes1$; injectivity of the adjunction bijection proves the mate description.

Cites: lem-weil-pbc-ringed-topoi-module-pullback-tensor, lem-weil-pbc-ringed-topoi-module-adjunction, def-pur-sheaf-tensor-product, lem-sfb-site-inverse-image-bilinear-adjunction.

2. Choose flat-term K-flat resolutions [lem-pc-kflat-resolution]. Their pullbacks remain flat-term K-flat [lem-weil-pbc-ringed-topos-kflat-pullback]. The tower tensor functor inverts quasi-isomorphisms between K-flat complexes: at each algebra level this is [lem-pur-derived-change-of-rings], and tower cohomology is levelwise [lem-weil-tower-category-levelwise-abelian]. Thus [lem-pur-left-derived-from-kflat-class] constructs $B_T$. The constant tower of a K-flat complex is K-flat for diagram tensor, since its tensor with an acyclic diagram is acyclic at every level; hence this construction also computes the displayed diagram tensor.

Cites: lem-pc-kflat-resolution, lem-weil-pbc-ringed-topos-kflat-pullback, lem-pur-derived-change-of-rings, lem-weil-tower-category-levelwise-abelian, lem-pur-left-derived-from-kflat-class.

3. Quasi-isomorphisms in the homotopy category have right fractions [lem-pur-quasi-isos-saturated-triangulated]. Apply [lem-trf-right-fraction-dense-subcategory] to the full resolving subcategory of flat-term K-flat complexes. Its localization is the derived category. The ordinary comparison, conjugated by the two invertible resolution counits, is natural there. Full faithfulness of localization precomposition [lem-weil-pbc-localization-universal-property] descends it uniquely, together with the transition and augmentation equations. The derived tensor/pullback comparison [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] has exactly this representative formula, proving the evaluation identification.

Cites: lem-pur-quasi-isos-saturated-triangulated, lem-trf-right-fraction-dense-subcategory, lem-weil-pbc-localization-universal-property, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.

### lem-weil-pbc-tower-derived-evaluation-normalization

1. Choose a K-injective tower resolution [lem-weil-pbc-kinjective-functorial-existence]. Its evaluations are K-injective [lem-weil-tower-evaluation-kinjective] and evaluation preserves the resolution quasi-isomorphism by levelwise cohomology [lem-weil-tower-category-levelwise-abelian]. Thus both composites are computed by the same $G(J_n)$ [lem-weil-pbc-kinjective-total-derived]. Their universal units on $J$ are invertible, so the displayed equation uniquely defines $\beta_{n,QJ}$.

Cites: lem-weil-pbc-kinjective-functorial-existence, lem-weil-tower-evaluation-kinjective, lem-weil-tower-category-levelwise-abelian, lem-weil-pbc-kinjective-total-derived.

2. The bijection from homotopy maps into a K-injective to derived maps [lem-weil-pbc-kinjective-hom-derived] makes these components natural in all derived morphisms, independent of resolution and unique on all objects. The same equality of ordinary composites commutes with the transitions $J_{n+1}\to J_n$; hence their derived comparisons do too.

Cites: lem-weil-pbc-kinjective-hom-derived.

3. The functors $G,G^{\rm Tow}$ preserve K-injectives because $F,F^{\rm Tow}$ are exact [lem-weil-pbc-right-adjoint-preserves-kinjective]. The derived adjunction is given, for arbitrary $N$ and K-injective $J$, by $\operatorname{Hom}_D(FQN,QJ)=\operatorname{Hom}_K(FN,J)=\operatorname{Hom}_K(N,GJ)=\operatorname{Hom}_D(QN,QGJ)$ [lem-weil-pbc-kinjective-hom-derived]; the tower calculation is identical. Its counit at $QJ$ is therefore represented by $F^{\rm Tow}G^{\rm Tow}J\to J$, conjugated by the derived units. Evaluation gives $FG(J_n)\to J_n$. Substituting the defining equation for $\beta$ proves the counit equation. Transport along K-injective representatives proves it on every object.

Cites: lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-hom-derived.

## Retained history

The earlier full report is retained locally in retained-report-before-statement-only-repair.md. Its proofs and citations are retained above; its claim that the route note requested proved new nodes is superseded by this repair. The search log is unchanged.

## Validation

Server srvcheck.py check_dag exited 0: no finding introduced by the sandbox or on its nodes. Server srvcheck.py review_split exited 0: item PASS. The route advisory concerns an existing incoming citation from lem-fd-finite-etale-adic-cohomology, not a new delivery dependency. Local consistency inspection verified five statement-only nodes, unchanged parent statement, 2097 total parent proof characters, actual log entries for every recorded search, and verbatim quotes for all four assembly steps. The final deliver.py --no-push exited 0 and printed OK (not pushed) at 4e2d5334027: preflight passed. The earlier delivery admission cleared without any intervention; only one invocation was active. No node changes were needed after the successful dry run. The direct-delivery push is the final remaining action.
