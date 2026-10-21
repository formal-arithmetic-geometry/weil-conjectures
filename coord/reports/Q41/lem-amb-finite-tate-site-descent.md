# Stage-1 re-split: lem-amb-finite-tate-site-descent

## Worker report

Files written: the item's JSON in dag/nodes/sec-smooth-purity/, and the following two statement-only nodes in that directory.

## New nodes

- lem-amb-tate-root-projection-reduction — statement, unsplit, no Mathlib match. Canonical projection reduction with arbitrary ramified finite coefficients, its power-transition equations, and the root-limit pullback map with its finite projection equation.
- lem-amb-finite-root-site-comparison — statement, unsplit, no Mathlib match. Finite roots and their scalar extensions on the two sites, normalized on actual units and comparison-unit tensors, with scheme and exponent coherence.

The statements have respectively 2334 and 2684 characters; they expose two different arguments with different inputs, not two clauses restating the descent theorem. The first never mentions the etale/pro-etale comparison; the second never mentions an infinite root limit or a ramified coefficient field. Both can be studied from their own statements and the sources below. Neither contains proof steps or proof dependencies. The parent's proof has 2149 characters, below 3000; no non-elementary step exceeds 2000.

Attachments: none. The whole-project notion and blueprint-tag searches under lean/WeilConjectures found no finished declaration of this item. The published Sheaf.Paper.FiniteTateSiteDescent theorem, AlgebraicGeometry.Scheme.finite_tate_site_descent at line 264, ends in sorry at line 308. Its full docstring and normalization predicates were read. Existing etale Tate sheaf declarations do not give the pro-etale root-limit comparison. No Lean was written or compiled.

WANTED: none. The combined lemmas are agent combinations, not assertions attributed wholesale to a Stacks lemma. Their ingredients are already in the DAG and the literature. The original eight-step argument is retained verbatim below as work allocation for the future splitters.

What was wrong: the item was already split/reviewed but its 7608-character proof was deliberately returned by the human for workload distribution. Its statement is unchanged, as are all inherited blueprint/import/Lean/review records. No mathematical dispute was found. No new targets, notions, or stronger hypotheses were substituted. No argument has been discarded. Steps 7 and 8 were already short applications of generic tensor and comparison-unit nodes, and remain the short tensor induction and fully faithful lifting in the parent; introducing new lemmas for those few-line applications would violate the elementary-node rule.

Unfinished: precisely the two new statement-only proof tasks, as requested; their own proofs are for subsequent workers.

## Sources and route

I read the current main-20261015 thm-amb-vector-bundle-purity proof, paragraph 1's integration coefficient, and sk-prop-an's statement and all eight stored step paragraphs. The chapter stays fixed; this coefficient identification supports the existing integration route. New blueprint references use ancestor thm-amb-vector-bundle-purity, via lem-amb-finite-tate-site-descent, with exact places and empty same_as.

For the first node I read sites-modules.tex, Tag 093M, label lemma-completion-flat (lines 8261 onward), and the full statements of lem-pur-twist-sheaf-locally-free (especially clause 2), lem-weil-pbc-constant-completion-equivalence, def-weil-l-adic-numbers, def-coefficient-twists-detailed, and lem-pur-tate-inverse-limit-base-change. Completed Z_l is distinguished from constant Z_l. The projection identifies the root quotient, reassociation is the explicit two-sided pure-tensor formula, and annihilation makes quotient tensor well defined without flatness. The limit map is formed by its universal property from compatible root maps, not by commuting inverse image with an infinite limit.

For the second node I read proetale.tex Tag 0GLZ, label lemma-describe-pullback-from-etale (lines 3760 onward), and Tag 09A5, label section-morphism (lines 4675 onward); etale-cohomology.tex Tag 03PK, label section-kummer (lines 2819 onward); and sites-modules.tex Tag 03EL, label lemma-tensor-product-pullback (lines 3649 onward). I read lem-cbc-comparison-pullback-sections, lem-asd-etale-finite-twist-pullback, lem-sf-comparison-pullback-exact, lem-weil-pbc-left-exact-site-inverse-image-tensor and lem-weil-pbc-ringed-topoi-module-pullback-tensor. The section formula is for arbitrary weakly etale objects, including nonaffine tests. The mixed tensor is balanced over the finite constant ring; its comparison preserves the balancing coequalizer and the same scalar maps. The root map and the scheme square are normalized by pulling the actual unit back, rather than by choosing primitive roots.

For the final two assembly steps I read the full statements of the ordinary and derived ringed-topos tensor comparison nodes, lem-sf-comparison-pullback-exact, lem-weil-pbc-comparison-grothendieck-unit and lem-weil-pbc-ring-modules-grothendieck-abelian, and proetale.tex Tag 099T, label lemma-fully-faithful (lines 3828 onward). Exactness applies because A is finite. The derived theorem is for the ordinary unbounded module derived categories and the same K-flat tensor convention, not a completed tensor. The comparison-unit statement explicitly covers module sheaves; no set-valued-only fully faithful result is used for modules.

## Searches and existing-node review

Before creating either node, I searched the full DAG by titles, root/tower/projection/reduction and comparison statements, source tags 093M/0GLZ/03PK/03EL, and read the closest candidates. The blueprint searches run were: root projection; finite Tate; roots of unity; finite reduction; roots.*comparison; Tate.*reduction. None is an exact or more general statement of either proposed lemma. The ancestor command returned thm-amb-vector-bundle-purity. In particular:

- lem-pur-twist-root-local-models and lem-pur-twist-sheaf-locally-free give the completed local model and completed finite reduction, but not the ramified discrete-coefficient reassociation, normalized theta, all annihilators and finite-projection pullback equation.
- lem-pur-tate-inverse-limit-base-change supplies the generic limit-map argument assuming a compatible tower and finite reduction isomorphisms; it does not establish the root reduction or the named pro-etale twist identification. It is a reusable ingredient for the first new node, not another task to create.
- lem-pur-kummer-integral-root-comparison is a finite integral-basis/direct-sum computation, without a root tower or site comparison.
- lem-asd-finite-etale-tate-line-comparison and lem-asd-etale-finite-twist-pullback concern scheme pullback within the etale site; neither states the comparison to the pro-etale site.
- lem-pur-finite-smooth-site-realizations assumes a separated finite-type compactifiable smooth morphism between Noetherian schemes, and uses a particular double-lift encoding. Those hypotheses cannot specialize to arbitrary T in the new node.
- lem-sp-proetale-units-comparison concerns the counit on the full units sheaf. It is a possible ingredient, but does not state finite-root scalar-extension, tensor-unit normalization and both coherence squares.

For each new node I executed leanfinder with two different phrasings, loogle with a name/type pattern, grep in Mathlib/AlgebraicGeometry, and leansearch. Each exact query, service result and verdict is copied from this item's searches.jsonl into the node. I read all returned hits; none was unavailable. The first searches found PreTilt/Witt-vector residue formulas and cyclotomic-character projections in rings, ordinary rootsOfUnity, profinite inverse limits, or tensor direct limits. The second found etale algebra maps, cyclotomic characters and general presheaf pullback. None specializes in one line to these sheaf isomorphisms and their normalized equations. I opened Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean: it defines the continuous Z_l sheaf and cohomology, not root twists or either new comparison. The literal finite-root/comparison names have no Mathlib grep hits. There are zero new Mathlib leaves.

## Review by Q41

I checked the actual JSON statements against the sources just named, not just the dependency lists. The first lemma has ell prime, E finite, n positive, ell invertible on T, and ell^r A=0 before every reduction; it does not require n to be a multiple of e. Its finite quotient formula is for the prescribed root projection, so later assembly does not extract a normalization from a bare existence assertion. Its b_v is defined through the limit projections and is only a map at this stage. The second lemma assumes a positive invertible exponent and a finite ring it annihilates. Its c and sigma are specifically the maps of units and balanced scalar extension. Its scheme square includes the canonical comparison-square isomorphism, and its power maps compare coefficient rings by reduction. These two statements name all their objects and notions and cite definitions in stmt_deps; sources give tags and labels, and the statements do not define themselves by a tag.

Parent step 1 cites precisely the two new statements. The first explicitly supplies theta from the prescribed pro-etale twist; the second supplies sigma with the same finite-root tensor target and the comparison-unit normalization. Their composition is therefore the claimed beta, with every scalar action and direction matching. This use needs both statements and cannot follow from a definition alone.

Parent step 2 cites both new statements and lem-asd-etale-finite-twist-pullback. The latter explicitly supplies the etale exponent transition isomorphism for m dividing m', as well as arbitrary scheme pullback. The first supplies the theta transition and b_v projection equations; the second supplies the sigma transition and scheme equations and invertible d_v. Cancelling theta gives the beta square and invertibility of b_v; multiplication of exponents and a common upper exponent give the cocycle. Only cancellation/substitution is left inline. No infinite-limit preservation is assumed and no affine, quasi-compact or Noetherian assumption was used.

Parent step 3 cites the actual tensor-power definitions in def-coefficient-twists-detailed and def-pur-sheaf-tensor-product, the ordinary tensor comparison, the exact finite coefficient comparison and the derived tensor comparison. I checked the ordinary theorem says u^*(M tensor N) = u^*M tensor u^*N for ringed topoi, and the derived theorem says the corresponding formula for Lu^* and derived tensor. Exactness identifies the comparison's derived inverse image with its termwise version. The finite coefficient hypothesis holds. Induction starts at the coefficient identity for a=0 and at beta for a=1; the recursive tensor formula proves the rest. There is no new non-elementary lemma hidden in that induction.

Parent step 4 cites the Grothendieck comparison unit and the ring-module Grothendieck category statement. I checked the former says the unit is invertible for module sheaves, and the latter verifies the coefficient category requirement. Full faithfulness then lifts alpha^{-1} beta and its inverse; faithfulness forces the inverse equations. This elementary adjunction consequence gives uniqueness for every power, rather than uniqueness up to an unspecified scalar.

I tested the empty scheme (all module sheaves zero), a=0 (coefficient identity), a=1 (the specified first comparison), r'=r (identity power), three exponents (powers multiply), v=id and two composed v's (the same root projection equations), E=Q_l with n=r=1, and a ramified extension with e=2,n=1 with r=1 and r=2 (the same residue coefficients are allowed and need not be flat over Z/l^2). For the general finite-root lemma m=1 forces A=0, and both scalar-extended sides are zero. Larger annihilating powers and disconnected/nonaffine schemes introduce no sectionwise lift assertion: pure tensors are local generators after sheafification. A local tower lift need only be pro-etale local. All these tests preserve the intended formula.

Corrections during this re-split: separated completed and constant scalar rings; made the canonical root-unit normalization and scheme square part of the new statements; retained b_v only as a map in the first statement so its invertibility follows in assembly from finite-root comparison; kept tensor induction and fully faithful uniqueness inline because their generic non-elementary inputs already have nodes. I checked delivery-errors B1-B10, C1-C8, D1-D5, E1-E7: no proof in new unsplit nodes, no duplicate statement or clause-only restatement, no uncited non-elementary fact in the parent, no argument taken from a cited proof, and no altered hypotheses. The inherited off-unit tools still used by the short assembly are declared in split_report.tool_uses; the new nodes are in the item's own unit. No maintainer tool_uses field was changed.

## Original argument allocation (verbatim preservation)

The following is the old detailed argument, preserved for future workers. New statement-only nodes have no proof skeletons. Steps 1,2 and the pro-etale portion of 5 plus the limit/projection portion of 6 belong to lem-amb-tate-root-projection-reduction. Steps 3,4 and the comparison-square/finite-unit portion of 6 belong to lem-amb-finite-root-site-comparison. Their statements include the exact normalization, transition and scheme equations these arguments establish. The concluding short tensor/uniqueness arguments 7,8 remain in assembly steps 3,4, with their existing generic lemmas.


### Original step 1

Put $Z=(\mathbf Z_\ell)_{T_{\mathrm{proet}}}$, $C=\widehat{\mathbf Z}_{\ell,T}$, $R_r=(\mathbf Z/\ell^r)_{T_{\mathrm{proet}}}$ and $L=\varprojlim_s\mu_{\ell^s,T}^{\mathrm{pro}}$. The root projections are $p_r:L\to\mu_{\ell^r,T}^{\mathrm{pro}}$. Clause (2) of lem-pur-twist-sheaf-locally-free supplies the $C$-module structure of $L$ and its finite reduction $L\otimes_C R_r\cong\mu_{\ell^r,T}^{\mathrm{pro}}$. The completed coefficient quotient theorem gives $C/\ell^rC\cong R_r$. Apply it to the Noetherian DVR $\mathbf Z_\ell$ and $(\ell)$; these ring properties and $\mathbf Z_\ell/(\ell^r)=\mathbf Z/\ell^r$ are in def-weil-l-adic-numbers. The finite reduction is the one belonging to the specified roots tower, induced by $p_r$. Thus it identifies $L/\ell^rL$ with $\mu_{\ell^r,T}^{\mathrm{pro}}$. All these constructions are on the pro-etale site, and only $\ell$ invertible on $T$ is needed.

Cited statements: lem-pur-twist-sheaf-locally-free, lem-weil-pbc-constant-completion-equivalence, def-weil-l-adic-numbers, def-pur-sheaf-inverse-limit.


### Original step 2

Reassociate the two coefficient tensors in def-coefficient-twists-detailed: $A_T^{\mathrm{pro}}(1)\cong L\otimes_Z A_T$. The maps on local pure tensors are $(x\otimes b)\otimes a\mapsto x\otimes ba$ and $x\otimes a\mapsto(x\otimes1)\otimes a$. Since $\ell^rA=0$, tensoring with $A_T$ factors through $L/\ell^rL$: the inverse maps are $x\otimes a\mapsto\bar x\otimes a$ and $\bar x\otimes a\mapsto x\otimes a$, independent of the lift because $(\ell^ry)\otimes a=y\otimes\ell^ra=0$. The sheaf tensor definition makes these sectionwise formulas descend after sheafification. Step 1 therefore gives the isomorphism
$$\theta_r:A_T^{\mathrm{pro}}(1)\xrightarrow{\sim}\mu_{\ell^r,T}^{\mathrm{pro}}\otimes_{R_r}A_T,\qquad x\otimes a\longmapsto p_r(x)\otimes a.$$
No flatness of $A$ over $\mathbf Z/\ell^r$ is used.

Cited statements: def-coefficient-twists-detailed, def-pur-sheaf-tensor-product.


### Original step 3

Apply lem-cbc-comparison-pullback-sections to the underlying etale root sheaf. For a weakly etale $f:W\to T$, lem-asd-etale-finite-twist-pullback identifies $f_{\mathrm{et}}^{-1}\mu_{\ell^r,T}^{\mathrm{et}}$ with $\mu_{\ell^r,W}^{\mathrm{et}}$. Sections at $W$ are exactly units $z\in\Gamma(W,\mathcal O_W)^\times$ satisfying $z^{\ell^r}=1$, which is the defining value of the pro-etale root sheaf. This gives
$$c_r:\nu_T^{-1}\mu_{\ell^r,T}^{\mathrm{et}}\xrightarrow{\sim}\mu_{\ell^r,T}^{\mathrm{pro}}.$$
Restriction is pullback of the same unit, so these objectwise bijections are natural. Powers give both the scalar actions and the transitions; hence $c_r$ is $R_r$-linear after the constant-ring identification of lem-sf-comparison-pullback-exact, and $c_r\nu_T^{-1}(z\mapsto z^{\ell^{r'-r}})=(z\mapsto z^{\ell^{r'-r}})c_{r'}$. This uses the section formula for all weakly etale $W$, without an affine or finite-type hypothesis on $T$.

Cited statements: lem-cbc-comparison-pullback-sections, lem-asd-etale-finite-twist-pullback, def-pur-roots-of-unity-sheaf, lem-sf-comparison-pullback-exact.


### Original step 4

The ringed-topos tensor comparison and the canonical identifications of the constant $\mathbf Z/\ell^r$ and $A$ sheaves give
$$\nu_T^*(\mu_{\ell^r,T}^{\mathrm{et}}\otimes_{\mathbf Z/\ell^r} A_T)\cong\mu_{\ell^r,T}^{\mathrm{pro}}\otimes_{R_r}A_T.$$
Here the mixed-coefficient tensor is the coequalizer imposing the $\mathbf Z/\ell^r$-balancing relations; the inverse image preserves this coequalizer and the integer tensor, and sends the scalar-action maps to the same scalar-action maps. Equivalently this is ordinary ringed pullback over $\mathbf Z/\ell^r$ followed by the $A$-action. Compose this comparison, denoted $c_r\otimes1$, with $\theta_r^{-1}$ from step 2. The resulting $A$-linear isomorphism $\beta_r=\theta_r^{-1}(c_r\otimes1)$ is the required $\nu_T^*A_T^{\mathrm{et}}(1)\cong A_T^{\mathrm{pro}}(1)$, normalized by the specified root projections and constant scalar maps.

Cited statements: lem-weil-pbc-ringed-topoi-module-pullback-tensor, lem-weil-pbc-left-exact-site-inverse-image-tensor, lem-sf-comparison-pullback-exact.


### Original step 5

For $r'\geq r$ let $P_{r',r}$ be the root power transition. The definition of the inverse limit gives $p_r=P_{r',r}p_{r'}$, so on every local generator $x\otimes a$ of $L\otimes_ZA_T$,
$$(P_{r',r}\otimes1)\theta_{r'}(x\otimes a)=p_r(x)\otimes a=\theta_r(x\otimes a).$$
Therefore $P_{r',r}\otimes1=\theta_r\theta_{r'}^{-1}$ is an isomorphism. On the etale site the corresponding transition is an isomorphism by the last assertion of lem-asd-etale-finite-twist-pullback. Step 3 identifies its pullback with $P_{r',r}\otimes1$, whence $\beta_r\nu_T^*(P_{r',r}\otimes1)=\beta_{r'}$. The power maps compose by multiplying their exponents; taking a common larger annihilating exponent compares any two choices and gives the cocycle identity. This proves canonical independence of $r$, including its comparison, rather than merely existence of an unspecified identification.

Cited statements: def-pur-sheaf-inverse-limit, lem-asd-etale-finite-twist-pullback.


### Original step 6

Let $v:T'\to T$. Use the comparison square $\nu_{T'}^*v_{\mathrm{et}}^{-1}\cong v_{\mathrm{proet}}^{-1}\nu_T^*$ and the etale root pullback of lem-asd-etale-finite-twist-pullback. The standard pro-etale root maps are compatible with the tower transitions by lem-pur-roots-of-unity-inverse-image-iso (1)-(2). They induce a map from $v^{-1}L_T$ to $L_{T'}$ by taking the family $c^v_{\mu_{\ell^s}}v^{-1}p_s$ of projections; this uses the limit universal property, without asserting that inverse image preserves this infinite limit. Extend scalars to define the usual finite-level map $b_v:v^*A_T^{\mathrm{pro}}(1)\to A_{T'}^{\mathrm{pro}}(1)$. By the tensor comparison and constant-scalar identification, its $r$-th projection satisfies
$$\theta_{r,T'}b_v=(c^v_{\mu_{\ell^r}}\otimes1)\,v^*\theta_{r,T}.$$
Step 3's section description identifies the root map on the right with the etale root pullback through the comparison square: both pull a unit back to the same unit. Substitute $\beta_r=\theta_r^{-1}(c_r\otimes1)$ in this equation. It says precisely that $b_v$ agrees with the pullback of $\beta_r$ and the etale twist pullback isomorphism, so $b_v$ is an isomorphism and the claimed square commutes. Identity and composition compatibility follow by the same equation at the finite root projection and the identity/composition compatibility of the two cited pullback comparisons.

Cited statements: lem-weil-pbc-comparison-pullback, lem-asd-etale-finite-twist-pullback, lem-pur-roots-of-unity-inverse-image-iso, def-pur-sheaf-inverse-limit, def-weil-proetale-inverse-image, lem-weil-pbc-ringed-topoi-module-pullback-tensor, lem-pe-constant-left-module-inverse-image.


### Original step 7

For $a=0$ use the constant-$A$ comparison, and define $\beta_{r,a}$ for $a>0$ by tensoring $a$ copies of $\beta_r$ and the canonical inverse-image tensor comparisons. Explicitly $\beta_{r,a+1}$ is $\beta_{r,a}\otimes_A\beta_r$ after that tensor comparison. This is induction on the tensor-power definition in def-coefficient-twists-detailed and def-pur-sheaf-tensor-product, so gives $\nu_T^*A_T^{\mathrm{et}}(a)\cong A_T^{\mathrm{pro}}(a)$. Steps 5 and 6 give the transition and scheme-pullback squares factor by factor; naturality of the tensor comparison gives their tensor powers. For derived tensors the ringed-topos derived tensor theorem supplies $L\nu_T^*(K\otimes_A^LM)\cong L\nu_T^*K\otimes_A^LL\nu_T^*M$, and exactness of the finite-coefficient comparison identifies $L\nu_T^*$ with the termwise $\nu_T^*$. Thus the same comparisons respect the specified derived tensor conventions.

Cited statements: def-coefficient-twists-detailed, def-pur-sheaf-tensor-product, lem-weil-pbc-ringed-topoi-module-pullback-tensor, lem-sf-comparison-pullback-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback.


### Original step 8

Finally the comparison adjunction unit is invertible on all module sheaves by lem-weil-pbc-comparison-grothendieck-unit, applied to $\operatorname{Mod}(A)$, which is Grothendieck abelian by lem-weil-pbc-ring-modules-grothendieck-abelian. Hence $\nu_T^*$ is fully faithful. If $G$ is another etale descent equipped with $\alpha:\nu_T^*G\cong A_T^{\mathrm{pro}}(1)$, the map $\alpha^{-1}\beta_r:\nu_T^*A_T^{\mathrm{et}}(1)\to\nu_T^*G$ lifts to exactly one etale map $h$. Its inverse lifts in the same way; faithfulness says their composites are identities. Thus $h$ is the unique comparison-preserving isomorphism. The argument applies to each tensor power as well. Throughout the finite reduction uses only $\ell^rA=0$, never $A$ flat over $\mathbf Z/\ell^r$ or $n$ a multiple of a ramification index. On the empty scheme all maps are the unique maps between zero module sheaves; at $a=0$ the comparison is the coefficient-ring identity.

Cited statements: lem-weil-pbc-comparison-grothendieck-unit, lem-weil-pbc-ring-modules-grothendieck-abelian.


## Not duplicates


lem-amb-tate-root-projection-reduction vs lem-trf-point-reduction-unit-normalization: existing result concerns Point coefficient-reduction comparisons are normalized by scalar-extension units; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-sfb-local-integral-perfect-model-cohomology: existing result concerns Cohomology of a local integral perfect scalar model; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs def-sfb-quotient-kernel-completeness: existing result concerns Local derived completeness for a ring-sheaf quotient kernel; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-sfb-finite-constant-model-two-term-free-resolution: existing result concerns Finite scalar local models have two-term finite-free sheaf resolutions; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-sfb-integral-quotient-direct-image-comparison: existing result concerns Unbounded quotient-scalar refinement of integral direct image; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-sfb-adic-perfect-model-complete-reduction: existing result concerns Completeness and residue calculation of a completed perfect coefficient model; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs def-weil-pbc-completed-constant-realization-data: existing result concerns Completed constant realization interfaces; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-weil-pbc-completed-constant-module-model: existing result concerns Scalar extension realizes finite completion modules; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-weil-pbc-completed-constant-algebra-flat-quotients: existing result concerns Ordinary flat algebra and quotients of a completed constant ring; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-weil-pbc-completed-constant-sheaf-reduction: existing result concerns Completed constant coefficients and finite reduction; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-weil-pbc-constant-completion-equivalence: existing result concerns Constant-to-completed coefficients on derived-complete categories; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-weil-pbc-finite-perfect-adic-canonical-comparison: existing result concerns Canonical derived quotients as explicit coefficient complexes with compatible finite-free retracts; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-cbc-finite-extension-reduction-cone-bound: existing result concerns Uniformizer cone comparison and uniform reduction bound; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-sp-constant-pullback-scalar: existing result concerns Module pullback transports scalar multiplication; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-sp-constant-inverse-image-section: existing result concerns Transported global sections and constant quotient kernels; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-weil-finite-free-completed-scalar-comparison: existing result concerns Finite free completed coefficient extension is ordinary derived scalar extension; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-pod-point-principal-reduction-coefficients: existing result concerns The completed principal coefficient sequence is short exact; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-pod-point-reduction-coefficient-ring: existing result concerns The normalized lifted coefficient quotient is a regular principal quotient; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-tate-root-projection-reduction vs lem-pod-completed-integral-scalar-regular: existing result concerns Powers of the uniformizer are regular on completed coefficient sections; the new statement is about the specified inverse system of roots, the ramified finite twist, all projection-normalized annihilator reductions and their scheme-pullback equation; the existing statement does not assert that root-tower package.


lem-amb-finite-root-site-comparison vs lem-pe-comparison-reflects-local-torsion: existing result concerns Etale/pro-etale comparison reflects local integer torsion; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-cbc-comparison-matching-transport: existing result concerns Matching families give the fpqc compatibility equation; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-exc-relative-adjoint-open-origin: existing result concerns Etale-origin witnesses for the two restricted relative-adjoint values; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs def-pur-finite-tate-site-comparison: existing result concerns Finite Tate tensor generators and root-normalized site comparison predicates; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-sf-comparison-pullback-exact: existing result concerns The comparison pullback is exact on sheaves of modules and commutes with cohomology sheaves; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-sp-proetale-units-comparison: existing result concerns The full units sheaf is preserved by etale/pro-etale comparison; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-cbc-comparison-section-descent: existing result concerns The terminal-section presheaf is a pro-etale sheaf; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs def-cbc-comparison-section-diagonal-unit: existing result concerns The explicit diagonal comparison unit; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-cbc-comparison-pullback-sections: existing result concerns Sections formula for the etale-to-pro-etale inverse image; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-cbc-comparison-section-adjunction: existing result concerns The section-valued functor is left adjoint to etale restriction; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-cbc-comparison-section-unit-universal: existing result concerns Unique extension along the concrete diagonal unit; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-cbc-comparison-section-functor: existing result concerns Construct the section-valued comparison sheaf functor; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-cbc-proetale-comparison-stalk: existing result concerns Geometric stalks commute with etale-to-pro-etale inverse image; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-finite-root-site-comparison vs lem-cbc-comparison-diagonal-section-naturality: existing result concerns Naturality of diagonal inverse-image sections; the new statement identifies finite root sheaves and balanced A-tensors on the two sites, with root-unit normalization and scheme/exponent equations; the existing statement does not assert that finite-root scalar/coherence package.


lem-amb-tate-root-projection-reduction vs lem-amb-finite-tate-site-descent: the new node never compares sites or asserts etale descent, tensor powers or uniqueness; it establishes the normalized pro-etale finite reduction and its finite-projection pullback equation.


lem-amb-finite-root-site-comparison vs lem-amb-finite-tate-site-descent: the new node has only finite roots and scalar tensors, for arbitrary finite A and exponent m; it has no inverse root limit, ramified coefficient extension, nonnegative powers or uniqueness of descent.
