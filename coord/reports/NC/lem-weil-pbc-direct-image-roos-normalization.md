# Worker report: lem-weil-pbc-direct-image-roos-normalization

1. Files written:
- dag/nodes/sec-proper-base-change/lem-weil-pbc-direct-image-roos-normalization.json: existing statement, re-split into four assembly steps; statement, Lean record and inherited metadata unchanged.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-exact-adjoint-tower-models.json: new statement, unsplit; no Mathlib match. Simultaneous resolution, products, inverse limits, comparisons, and unit-normalized Roos identification.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-kinjective-fiber-triangle-comparison.json: new statement, unsplit; no Mathlib match. General K-injective shifted-cone triangle comparison, including its derived-unit-normalized shift and boundary.
- citations.json and this report. Searches are recorded by msearch.py in searches.jsonl. Work notes retain the exact original item and its eight-step proof.

2. Attachments: none. Searches of lean/WeilConjectures for the blueprint tag and Roos normalization gave no finished declaration. lean/Sheaf/CategoryTheory/DirectImageRoosNormalization.lean states the parent theorem but its proof is `sorry`; it is not an attachment. Existing upstream K-injective, evaluation and triangulated-functor declarations cover only ingredients of the new statements.

3. WANTED: none. All sources used are present locally.

4. What was wrong: the parent was deliberately returned for granularity, not for a false statement. Its eight-step proof has 8116 characters of text and several independent arguments. The human's 2026-10-21 request takes precedence over the inherited prohibition on re-splitting a reviewed item. This delivery preserves the parent statement verbatim and gives two comparably substantial, independently assignable obligations. The old proof's claim that its long shift step was elementary was misleading; that argument is now an explicit obligation of the second new node. The new nodes have no proof steps or proof dependencies; the original complete argument is preserved below for future workers.

5. What remains: the two new statements await their own stage-1 splits. No Lean is written or compiled. No mathematical obligation was dropped.

## Allocation of the old proof

- New exact-adjoint-tower-models carries old steps 1-4: small module-diagram Grothendieck categories; injective-term K-injective resolutions; evaluation; the levelwise adjunction; preservation of K-injectives and injective terms; ordinary limit/product comparisons with explicit legs; derived products; transition and difference squares. It also carries old step 5's application of the exact-products comparison, its sign change, the quasi-isomorphisms j_I,j_J, and normalization by the universal derived-limit unit.
- New kinjective-fiber-triangle-comparison carries old step 5's K-injective closure of mapping fibres and old steps 6-7's diagonal cone comparison, its inverse, the two triangle-coordinate equations, the construction and uniqueness of the unit-compatible derived shift, and the interpretation of the coordinate boundary equation as the actual derived connecting square. Its statement concerns arbitrary endomorphisms of K-injective complexes; it does not assume the desired direct-image/Rlim comparison.
- The parent now assembles those two statements. Its remaining coordinate equality theta G(j_I)=j_J beta is a two-coordinate check. Its identification a_M=Q(beta) uses the existing common-underived-composite normalization, not an unproved identification of cones. The same final conjugation and localization argument as old step 8 proves the required first and connecting squares. No node restates the parent or postulates its conclusion.

The two new statements are independently meaningful: the first does not assert compatibility of derived connecting morphisms, and the second neither constructs inverse limit nor identifies the first component with a_M. They have no dependency on one another or on the parent.

## Sources and Mathlib searches

I read the current main-20261015 blueprint's prop-weil-pbc-direct-image-limits statement and complete proof, and the fixed chapter and unit records. The source's product/Roos/(1-s) paragraph is still the route. I read sites-cohomology.tex lemma-Rf-commutes-with-Rlim (0A07), including both proofs, and lemma-derived-limit-is-ok (0941), including the injective-term tower calculation. For the first new node these supply the simultaneous models; derived.tex lemma-product-K-injective (0BK6), lemma-adjoint-preserve-K-injectives (08BJ), and the existing exact-products-roos-comparison statement provide the product, preservation and normalized inclusion inputs. The universal-property and module generalizations are agent refinements already explicit in the old proof, not quotations claimed to be verbatim Stacks theorems.

For the second new node I read derived.tex lemma-triangle-K-injective (090X), lemma-K-injective-defined (070Y) and lemma-enough-K-injectives-implies, the old cone/shift argument, and the source declaration RightDerivedFunctor/Triangulated.lean. I also read Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean lines 418-463 (map_delta, mapTriangleIso, mapTrianglehIso). These are ordinary additive-functor cone comparisons, not the universal-unit-normalized comparison for a chosen unbounded RG. Mathlib's ExactFunctor descent assumes exactness of G, which is not available. The search hits for adjunctions and ordinary injective resolutions likewise do not give the first new statement's unbounded simultaneous tower/product/limit package. Both phrasings of each semantic search were read; all queries and actual results are retained without inventing a query or treating an unavailable service as a negative result. Searches for the first node's added Roos-normalization clause were run separately when that clause was assigned to it.

I searched the entire DAG by source tag and concepts, and the whole blueprint with blueprint_refs.py search for Roos, K-injective tower, shift comparison, cone comparison, simultaneous and mapping cone. ancestor gives prop-weil-pbc-direct-image-limits, with via [lem-weil-pbc-direct-image-roos-normalization]. No blueprint statement equals either new statement. Known overlapping nodes are distinguished below; none supplies the whole new conclusion with the available hypotheses.

## Review by NC

I reviewed delivery-errors B-E against the actual source, all old dependency statements and the new files. B: both new nodes introduce their categories, functors, units, indexing, resolutions, cones and maps, have real source labels, correct blueprint ancestry, actual logged searches, and empty proofs. Notions are defined inline or supplied by their statement dependencies. No new node assumes a construction available only inside another proof. C: I opened each statement cited by each parent step and generated citations.json from verbatim substrings, not paraphrases.

Step 1 uses exact-adjoint-tower-models: the small-site module categories, exact F left adjoint to G and strict positive-natural towers are exactly the parent's setting. The statement supplies I,J and every limit/product/K-injective model, product invertibility and both s and 1-s equalities. No epimorphic-transition, boundedness or commutative-ring assumption is introduced.

Step 2 uses kinjective-fiber-triangle-comparison and right-adjoint-preserves-kinjective. The latter states preservation by an additive right adjoint of an exact additive functor; it applies to this G. The first new node supplies K-injectivity of P_I,P_J and the commuting chain isomorphism c, and the new cone lemma supplies K-injectivity of the cones, actual diagonal theta, all three squares and the normalized sigma. K-injective resolutions of the source category exist by the small-module-diagram Grothendieck and resolution statements used in the first node's argument. The generic cone lemma requires no exactness of G. I checked the differential (-dy-ux,dx), the projection r(y,x)=x and boundary b(z)=(z,0). Additivity gives G(-d)=-G(d). The equation sigma eta_{K[1]}=eta_K[1] fixes the shift on every complex, and on K-injectives it is the termwise comparison; no assertion of that normalization is taken merely from a theorem that says RG is triangulated.

Step 3 uses the exact-products clause of exact-adjoint-tower-models. Exact countable products on both sites are assumptions of the parent. Both I and J have injective degree terms as required in the original source calculation. That node specifies j_T and kappa_T Q(j_T)=eta_lim,T, not just existence of an unspecified cone isomorphism. The sign map (y,x) to (-y,x) changes Fib(-(1-s)) into Fib(1-s), fixes the inclusion (0,lambda), and preserves the normalization.

Step 4 uses ringed-tower-pushforward-limit-comparison for exactly its stated common-underived-composite normalization, plus the derived localization and K-injective total-derived statements. It does not take a chain-level formula from that node's proof. Since both composites are computed without further resolutions, the stated normalization evaluates to Q(beta). The equality theta G(j_I)=j_J beta follows explicitly from zero first coordinate and the equal limit legs; the only remaining operation is conjugating the three squares already supplied in Step 2. This gives the specified a_M, not a freely chosen cone completion. The final localization is justified by naturality on K-injective models, which both new statements include.

D: the old long proof has been distributed into two substantial different statements, not renamed as one node. Neither is the parent conclusion, and neither relies on it. All old arguments are retained in the allocation and full text below. E: I checked zero complexes, zero towers, constant towers with identity transitions, zero transitions, f=id, u=0 and u=id. For u=0 the fibre is P[-1] plus P and the boundary still selects the first coordinate; for u=id the fibre is contractible, consistent with all equations. For zero tower transitions j is the usual inclusion into the contractible fibre of identity; for constant towers the limit comparisons and augmentation legs are identities. No hidden exactness of G, finite-product bound, enough-points hypothesis or coefficient commutativity is used. The inherited commutative-only homotopy-limit dependency advisory does not justify narrowing this statement; the new model proof uses the general module and abstract Roos inputs instead.

The parent's assembly is below 3000 characters; no non-elementary assembly step exceeds 2000 characters. New unsplit statements may be long because they specify the actual maps; they contain no proof sketch. The old complete proof below is historical proof material for those obligations, not a proof field on an unsplit node. This is my direct-delivery self-review as NC; there was no second worker.

## Not duplicates

- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-pbc-direct-image-roos-normalization: the parent proves compatibility of the specified derived-limit comparison with all Roos triangle arrows; the new node supplies simultaneous chain representatives and comparisons, without any derived connecting-square assertion.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-pbc-ringed-strict-tower-projection-morphism: the existing node constructs a projection-formula morphism for augmented finite-free coefficient towers; the new node handles simultaneous arbitrary-tower resolution/product/limit models for an exact adjunction.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing node compares the ordered exchange under completed/constant scalar change; the new node has no cartesian square or exchange mate and instead provides the underlying arbitrary-tower models.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-pbc-flat-scalar-koszul-tower-comparison: the existing node compares flat scalar restriction of particular Koszul towers; the new node applies to arbitrary module-sheaf towers and an exact adjunction, with simultaneous K-injective representatives.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-pbc-constant-tower-pushforward-normalization: the existing node controls only constant towers and their counits; the new node treats arbitrary strict towers and their products and inverse limits.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-pbc-tower-derived-evaluation-normalization: the existing node normalizes evaluation and the derived counit; it supplies neither the simultaneous product/ordinary-limit models nor the normalized Roos inclusions of the new node.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-ringed-tower-pushforward-limit-comparison: the existing node states the derived direct-image/limit isomorphism and projections without exact pullback; the new node proves a different, exact-adjoint simultaneous representative package, including products and strict Roos inclusions.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-sp-constant-scalar-direct-image-completeness: the existing node proves preservation of one-element local completeness with constant coefficients; it supplies none of the arbitrary-tower representative and product computations.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-ringed-tower-pushforward-limit-acyclic: the existing node states inverse-limit acyclicity of a resolved image tower and assumes commutative rings; it does not state that GI itself is K-injective, nor the simultaneous product comparisons or normalized Roos inclusions.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-sp-constant-direct-image-preserves-complete: the existing node proves preservation of local derived ideal completeness for constant coefficients; the new node concerns arbitrary module-sheaf towers and has no ideal.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-pur-compact-support-completed-projection-coherence: the existing node identifies completed projection mates and counits via finite quotients; the new node has no completed tensor or mate and gives simultaneous K-injective tower models.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-pur-completed-coefficient-pushforward-comparison: the existing node compares completed and constant coefficient pushforwards and completeness; the new node has arbitrary ring sheaves and an exact adjunction, without coefficient reduction or completeness.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-pbc-exact-products-roos-comparison: the latter supplies the normalized Roos fibre alone; it does not supply the simultaneous exact-adjoint source/image tower models, product comparison or transition squares.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-weil-derived-limit-roos-complex: the latter gives the ordinary-limit inclusion for a single K-injective tower; it does not compare an exact-adjoint image or its product and inverse-limit models.
- lem-weil-pbc-exact-adjoint-tower-models vs lem-sp-levelwise-kinjective-tower-image: the latter computes levelwise images using evaluationwise K-injectivity, but does not give simultaneous K-injective image towers, inverse-limit models or products.
- lem-weil-pbc-kinjective-fiber-triangle-comparison vs lem-pur-roos-additive-comparison: the latter is a chain-level Roos comparison and includes no derived-functor unit, K-injective closure or canonical derived connecting square; the new node treats arbitrary K-injective endomorphisms and proves the unit-compatible derived triangle assertion.
- lem-weil-pbc-kinjective-fiber-triangle-comparison vs lem-pc-right-derived-functor-triangulated: the existing theorem asserts some natural shift commutation and triangulatedness, without its universal-unit normalization or explicit diagonal cone boundary comparison.
- lem-weil-pbc-kinjective-fiber-triangle-comparison vs lem-weil-pbc-kinjective-total-derived: the existing theorem gives universal right derivation and computation, not its normalized shift or explicit morphism of rotated cone triangles.
- lem-weil-pbc-kinjective-fiber-triangle-comparison vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the existing statement concerns internal Hom and slice restriction on a commutative ringed site; the new statement concerns an arbitrary additive G and specified chain cone comparisons.
- lem-weil-pbc-kinjective-fiber-triangle-comparison vs lem-cbc-exact-product-functor-roos-resolution: that statement requires an exact G and a pre-supplied descended comparison; the new node constructs the cone-triangle comparison for a potentially nonexact G with unit-normalized right derivation.

## Original complete proof retained for the new obligations

### Former step 1

Put $\mathcal A=\operatorname{Mod}(R_X)$ and $\mathcal B=\operatorname{Mod}(R_Y)$. Their strict tower categories are Grothendieck by [lem-weil-pbc-small-module-diagrams-grothendieck], with small index $\mathbf N_{\geq1}^{\mathrm{op}}$. Apply [lem-pur-kinjective-degreewise-existence] in $\operatorname{Tow}(\mathcal A)$ to choose a representative $q:X\to I$ of $M$, where $I$ is K-injective and every tower $I^r$ is injective. Write $I_n=\operatorname{ev}_n I$, $J=G^{\rm Tow}I$, $P_I=\prod_n I_n$ termwise, $P_J=\prod_n GI_n$, and $L_I=\lim_n I_n$, $L_J=\lim_n GI_n$ termwise. The evaluations $I_n$ are K-injective by [lem-weil-tower-evaluation-kinjective].

Cited nodes: lem-weil-pbc-small-module-diagrams-grothendieck, lem-pur-kinjective-degreewise-existence, lem-weil-tower-evaluation-kinjective.

### Former step 2

The adjunction $F\dashv G$ extends levelwise to $F^{\rm Tow}\dashv G^{\rm Tow}$: the componentwise adjunct of a natural transformation is natural by naturality of the adjunction bijection. Since exactness of towers is levelwise [lem-weil-tower-category-levelwise-abelian], $F^{\rm Tow}$ is exact. Thus [lem-weil-pbc-right-adjoint-preserves-kinjective] makes $J$ K-injective and makes each $GI_n$ K-injective. The same lemma applied to the exact constant-tower functor $\Delta$ left adjoint to $\lim$ makes $L_I$ and $L_J$ K-injective. Moreover $G^{\rm Tow}$ preserves the injective degree terms: a map $U\to G^{\rm Tow}I^r$ across a monomorphism $U\hookrightarrow V$ is adjoint to $F^{\rm Tow}U\to I^r$, which extends across the monomorphism $F^{\rm Tow}U\hookrightarrow F^{\rm Tow}V$ by injectivity [def-sp-injective-resolutions]. Hence $J$ has injective degree terms too. The K-injective total-derived-functor computation [lem-weil-pbc-kinjective-total-derived] now represents $\mathcal G^{\rm Tow}M$ by $J$, $R\lim_X M$ by $L_I$, and $R\lim_Y(\mathcal G^{\rm Tow}M)$ by $L_J$.

Cited nodes: lem-weil-tower-category-levelwise-abelian, lem-weil-pbc-right-adjoint-preserves-kinjective, def-sp-injective-resolutions, lem-weil-pbc-kinjective-total-derived.

### Former step 3

There are canonical chain isomorphisms $c:G(P_I)\xrightarrow{\sim}P_J$ and $\beta:G(L_I)\xrightarrow{\sim}L_J$. For example, for any $B\in\mathcal B$, the adjunction and the product universal property [def-weil-category-product] identify $\operatorname{Hom}(B,G(\prod I_n^r))$ with $\operatorname{Hom}(FB,\prod I_n^r)=\prod\operatorname{Hom}(FB,I_n^r)=\prod\operatorname{Hom}(B,GI_n^r)$; thus $G(\prod I_n^r)$, with legs $G(\pi_n)$, is a product. With compatible families in place of all families, the same bijections show $G(\lim I_n^r)$ is a limit of $GI_n^r$. Uniqueness of maps with these legs makes the degreewise comparisons commute with differentials, and supplies their inverses. In particular $\pi_n c=G(\pi_n)$ and $\lambda_n\beta=G(\lambda_n)$, with $\lambda_n$ the limit legs.

Cited nodes: def-weil-category-product.

### Former step 4

By [lem-pc-ringed-space-product-kinjective], $P_I$ and $P_J$ are K-injective and represent the respective products in the derived categories. Also $G(P_I)$ is K-injective by [lem-weil-pbc-right-adjoint-preserves-kinjective]. The identity-resolution identifications of [lem-weil-pbc-kinjective-total-derived] therefore identify $Q(c)$ with the statement's $\alpha_M$: its $n$th component is exactly $\mathcal G(p_n)$. Let $u_I=1-s_I$ and $u_J=1-s_J$. Projection to the $n$th factor gives
$\pi_n cG(u_I)=G(\pi_n)-G(t_n)G(\pi_{n+1})=\pi_n u_Jc$,
where $t_n:I_{n+1}\to I_n$. Product uniqueness proves $cG(u_I)=u_Jc$, and hence the claimed transition-endomorphism square as well.

Cited nodes: lem-pc-ringed-space-product-kinjective, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-total-derived, def-weil-tower-transition-endomorphism, def-weil-category-product.

### Former step 5

Use the explicit model [def-weil-strict-roos-model]: $H_I=\operatorname{Cone}(u_I)[-1]$, with $H_I^r=P_I^{r-1}\oplus P_I^r$ and differential $(y,x)\mapsto(-dy-u_Ix,dx)$, and similarly $H_J$. These are K-injective. Indeed the cone triangle and its rotations in the homotopy category, with [lem-weil-pbc-hom-into-triangle-exact], imply $\operatorname{Hom}_{K}(A,H_I[k])=0$ for every acyclic $A$ and integer $k$: the adjacent terms are Hom groups into shifts of $P_I$ and are zero by K-injectivity. This proves the defining null-homotopy condition; it also proves the assertion for $H_J$. Apply [lem-weil-pbc-exact-products-roos-comparison] in each module category: their tower categories are Grothendieck by Step 1 and countable products are exact by hypothesis. This gives the unit-normalized cone comparison with total derived limit. Its convention uses $-u$; the chain isomorphism $(y,x)\mapsto(-y,x)$ to our $u$-cone preserves the zero-first-coordinate inclusion. On the K-injective towers $I,J$, the derived units are invertible, so the inclusions $j_I:L_I\to H_I$, $z\mapsto(0,(\lambda_nz)_n)$, and $j_J:L_J\to H_J$ are quasi-isomorphisms. Hence, by the statement's convention, the canonical Roos triangles of $M$ and of $\mathcal G^{\rm Tow}M$ are the rotated cone triangles of $u_I$ and $u_J$, transported along $Q(j_I)$ and $Q(j_J)$. Indeed, the normalized comparison composed with the sign isomorphism sends $Q(j_I)$ to the unit $\eta_I$. That unit is the identification of $R\lim_XM$ with $Q(L_I)$ from Step 2, and likewise for $J$.

Cited nodes: def-weil-strict-roos-model, lem-weil-pbc-hom-into-triangle-exact, def-weil-abstract-derived-category, lem-weil-pbc-exact-products-roos-comparison.

### Former step 6

Apply [lem-pur-roos-additive-comparison] with the additive functor $G$; its product-comparison hypothesis holds for every tower complex by the adjunction calculation in Step 3. It gives the natural chain isomorphism $\theta:G(H_I)\xrightarrow{\sim}H_J$, whose two coordinates are $c^{r-1}$ and $c^r$ after the canonical biproduct comparison. Directly,
$\theta d(y,x)=(-c\,dy-c\,u_Ix,c\,dx)=(-d\,cy-u_Jcx,d\,cx)=d\theta(y,x)$.
Its inverse uses $c^{-1}$ on both coordinates. In particular, the limit-leg equalities of Step 3 give the equality of actual chain maps
$\theta\,G(j_I)=j_J\beta$:
both have zero first coordinate and second coordinate with $n$th leg $G(\lambda_n)$. This verifies the augmentation normalization as well as the cone comparison.

Cited nodes: lem-pur-roos-additive-comparison, def-weil-strict-roos-model.

### Former step 7

The rotated cone triangle has first map $r_I:H_I\to P_I$, $(y,x)\mapsto x$, second map $u_I$, and last map $b_I:P_I\to H_I[1]$, $z\mapsto(z,0)$, with the cone/rotation signs of [def-weil-abstract-derived-category, def-weil-triangulated-category]; likewise for $J$. The diagonal coordinates in Step 6 give $cG(r_I)=r_J\theta$ and $\theta[1]G(b_I)=b_Jc$ after the termwise shift identification; the second equality has coordinates $(cz,0)=(cz,0)$. Since $L_I,P_I,H_I$ are K-injective, their identity-resolution comparisons compute the derived functor, including these maps [lem-weil-pbc-kinjective-total-derived]. The shift $[1]$ is an automorphism of complexes that commutes with $Q$ and preserves quasi-isomorphisms. So $(\mathcal G\circ[1],\eta_{-[1]})$ is a total derived functor of $G\circ[1]=[1]\circ G$, and the universal property in [lem-weil-pbc-kinjective-total-derived] yields the unique shift comparison $\sigma$ with $\sigma_{QK}\eta_{K[1]}=\eta_K[1]$. This is the shift commutation of [lem-pc-right-derived-functor-triangulated], with the normalization fixed in the statement. On the K-injectives $L_I,P_I,H_I$, and on their shifts, both units are the identity-resolution identifications. Hence $\sigma$ is induced there by the termwise equality $G(K[1])=G(K)[1]$, using additivity, $G(-d)=-G(d)$. Consequently the displayed boundary equation is precisely the connecting square after applying $\mathcal G$, with its canonical shift comparison, and not just a commutative square on the first two arrows.

Cited nodes: def-weil-abstract-derived-category, def-weil-triangulated-category, lem-weil-pbc-kinjective-total-derived, lem-pc-right-derived-functor-triangulated.

### Former step 8

It remains to identify the first vertex after transporting the cone triangles to $R\lim$. In the chosen model, both derived composites in [lem-weil-ringed-tower-pushforward-limit-comparison] are computed without another resolution: $L_I$ is K-injective for $G$, and $J$ is K-injective for inverse limit. That node normalizes $a_M$ by the underived equality $G\lim=\lim G^{\rm Tow}$; hence $a_M$ is represented exactly by $\beta:G(L_I)\to L_J$. Step 6 yields
$Q(j_J)^{-1}\,Q(\theta)\,\mathcal G(Q(j_I))=Q(\beta)=a_M$.
Transport the three squares of Steps 4 and 7 along $Q(j_I)$ and $Q(j_J)$. Their components become $(a_M,\alpha_M,\alpha_M)$, and the last square reads
$a_M[1]\,\sigma_{R\lim_X M}\,\mathcal G(\delta_M)=\delta_{\mathcal G^{\rm Tow}M}\,\alpha_M$,
where $\sigma$ is the canonical shift comparison. All maps used are natural for strict tower maps. Their computed equations therefore hold for every derived tower, by the localization and K-injective computation [def-weil-abstract-derived-category, lem-weil-pbc-kinjective-total-derived]. This gives the specified morphism of canonical Roos triangles.

Cited nodes: lem-weil-ringed-tower-pushforward-limit-comparison, lem-weil-pbc-kinjective-total-derived, def-weil-abstract-derived-category.

