# Stage-1 repair: det-sp-reduction-tower-normalized

## Files written

- dag/nodes/sec-smooth-purity/det-sp-reduction-tower-normalized.json: unchanged statement, statement dependencies, blueprint import data and Lean record; assembly of four new tasks and the existing generic results.
- dag/nodes/sec-smooth-purity/lem-sp-strict-coefficient-tensor-descent.json: statement, unsplit; no Mathlib match after logged LeanFinder, LeanSearch, Loogle and source grep; no proof steps.
- dag/nodes/sec-smooth-purity/lem-sp-mixed-derived-coefficient-cancellation.json: statement, unsplit; no Mathlib match after logged LeanFinder, LeanSearch, Loogle and source grep; no proof steps.
- dag/nodes/sec-smooth-purity/lem-sp-integral-local-model-finite-matrix-reduction.json: statement, unsplit; no Mathlib match after logged LeanFinder, LeanSearch, Loogle and source grep; no proof steps.
- dag/nodes/sec-smooth-purity/lem-sp-stratified-reduction-postnikov-comparison.json: statement, unsplit; no Mathlib match after logged LeanFinder, LeanSearch, Loogle and source grep; no proof steps.

## Attachments

None. The exact project theorem AlgebraicGeometry.ProEtale.sp_reduction_tower_normalized is still `by sorry` at lean/Sheaf/Paper/SmoothPurityReductionTowerNormalized.lean:338. Whole-project notion/tag searches under WeilConjectures did not give a declaration proving all the clauses. Strictification of already normalized towers and normalized-tower effectivity are different directions.

## WANTED

None. All sources used are present locally. No SGA is used.

## What was wrong and what changed

The released stage-1 repair note overrides the previous passing review: the old proof had 9765 characters and the instruction requires at least three comparable independent tasks. This delivery has four. Its assembly has 2007 characters. The statement and Lean record are exactly the live ones, including the previously reviewed qcqs hypothesis for the global constructibility conclusion. No new statement dispute is introduced and no previous correction is undone.

## Allocation of the retained arguments

- Old steps 1--2 belong to lem-sp-strict-coefficient-tensor-descent: strict complex and semilinear maps, differentials and chain homotopies; flat-term K-flat resolving-class localization; levelwise detection of quasi-isomorphisms; functor descent and roofs, with no functorial choice of resolutions.
- Old step 3 and step 5 belong to lem-sp-mixed-derived-coefficient-cancellation: coefficient pullback preserves flat-term K-flat complexes; one-factor computations on each side; explicit balanced maps and inverses; the actual adjoint of the transition, units and three-index product compatibility; preservation of every Tor interval without flatness. Old step 8's unit test is included in its cohomological-support conclusion.
- Old step 4 is the existing det-def-localizing-closure-ctf-equals-bc(2), applied on qcqs T itself. It is cited directly and is not duplicated.
- Old step 6's finite scalar resolution, exact constant inverse image, completed-coefficient flatness, bounded-flat K-flatness, cofinality proving finiteness of A/ell^n, and finite matrix kernels/cokernels belong to lem-sp-integral-local-model-finite-matrix-reduction. Existing lem-sfb-finite-constant-model-two-term-free-resolution already supplies the resolution component and will be reused by its worker.
- Old step 6's coefficient-preserving restriction and old step 7's finite truncation triangles, exact scalar change, Serre closure and finite stalks belong to lem-sp-stratified-reduction-postnikov-comparison. Common refinement itself already exists as lem-weil-pbc-constructible-stratification-intersection and stays a direct cited step. The full global-partition conclusion and coefficient comparison are separate from the purely local scalar matrix calculation.
- Old step 8's final packaging is the elementary last assembly step.

## Preserved proof material for the new workers

The following is the live pre-repair proof, retained verbatim (including all its prior citations); it is source material for future splitting of the four statement-only nodes, not an additional proof in those nodes.

### Former step 1

Use the chosen small skeleton throughout. Write $R=R_T$ and $R_n=R_{T,n}$. For a complex representing $M$, choose a K-flat resolution $P$ with flat terms by [lem-pc-kflat-resolution]. In each cochain degree put $F(P)^q_n=P^q\otimes_RR_n$, with differential $d_P\otimes1$ and transition $1\otimes(R_{n+1}\to R_n)$. The transitions are semilinear and commute with the differential because both composites send $x\otimes c$ to $d_Px\otimes\bar c$; quotient composition gives the tower identities. Thus this is a strict complex in the abelian category of [det-sp-coefficient-towers-abelian]. Chain maps and chain homotopies act componentwise by tensoring with $1$. Its evaluation at $n$ represents $M\otimes_R^{\mathbf L}R_n$ by [lem-pur-derived-change-of-rings], and evaluation is exact by [det-sp-coefficient-towers-abelian].

Uses: lem-pc-kflat-resolution, det-sp-coefficient-towers-abelian, lem-pur-derived-change-of-rings. Source: literature/stacks-project/sites-cohomology.tex, Tag 06YS (lemma-K-flat-resolution); Tags 06YT, 06YY; blueprint construction paragraph.

### Former step 2

This construction is functorial on the derived category, without requiring a functorial choice of $P$. Let $\mathcal P_R$ be the homotopy category of K-flat complexes with flat terms. Its localization at quasi-isomorphisms is $D(R)$ by [lem-weil-pbc-site-derived-tensor-descent]. A quasi-isomorphism $P\to P'$ in $\mathcal P_R$ induces a quasi-isomorphism at every level after tensoring with $R_n$ by [lem-pur-derived-change-of-rings]. Kernels and cokernels in the tower category are levelwise by [det-sp-coefficient-towers-abelian], so the cohomology tower of its cone is levelwise zero, hence zero. Thus $F$ inverts these quasi-isomorphisms in $D(\operatorname{Tow})$. The localization universal property [lem-weil-pbc-localization-universal-property] descends $F$ to $\operatorname{red}_T:D(R)\to D(\operatorname{Tow})$, unique up to the canonical natural isomorphism. A roof is sent to the corresponding roof of strict tower complexes; this proves functoriality of the object and its quotient-induced transitions simultaneously, rather than merely producing an inverse system in $D(R)$.

Uses: lem-weil-pbc-site-derived-tensor-descent, lem-pur-derived-change-of-rings, det-sp-coefficient-towers-abelian, lem-weil-pbc-localization-universal-property. Source: literature/stacks-project/sites-cohomology.tex, Tags 06YS, 0G7D, 06YT and 06YU; derived resolving-class localization.

### Former step 3

For every $n$, apply [lem-weil-pbc-ringed-topos-kflat-pullback] to the identity underlying topos and the ring map $R\to R_n$. It says that $P_n=P\otimes_RR_n$ is K-flat with flat terms over $R_n$. Therefore the source of the reduction map for $m\leq n$ is computed by the ordinary complex $P_n\otimes_{R_n}R_m$ by [lem-pur-derived-change-of-rings]. The reduction map is induced by the tower transition, as stated in [det-sp-coefficient-towers-abelian](3). The ordinary tensor adjunction here is the explicit bijection sending $f:P_n\otimes_{R_n}R_m\to P_m$ to $x\mapsto f(x\otimes1)$, with inverse sending $g:P_n\to\operatorname{Res}P_m$ to $(x\otimes d\mapsto d\,g(x))$; balancing verifies the two maps are inverse. Since $P_n$ is K-flat this computes the derived transition-adjoint map, whose formula is
$$ (x\otimes c)\otimes d\longmapsto x\otimes\bar c d.$$
It has inverse $x\otimes d\mapsto(x\otimes1)\otimes d$. Both are well-defined by the balancing relations of [def-pur-sheaf-tensor-product], and commute with differentials; these formulas define mutually inverse maps first locally in the tensor presheaves and then in their sheafifications. This identifies the actual reduction map, not just its two endpoints, with an isomorphism. For $m=n$ the formulas are the tensor unit map; for three indices both composites send a pure tensor to $x\otimes\bar c\bar d e$, proving compatibility.

Uses: lem-weil-pbc-ringed-topos-kflat-pullback, lem-pur-derived-change-of-rings, det-sp-coefficient-towers-abelian, def-pur-sheaf-tensor-product. Source: literature/stacks-project/sites-cohomology.tex, Tag 0G7E (lemma-pullback-K-flat), Tag 06YY (lemma-derived-base-change); blueprint normalization paragraph.

### Former step 4

For the constructibility conclusion assume from now on that $T$ is qcqs and $M\in\Dbc(T,\mathcal O_E)$. Choose integers $r\leq s$ containing its cohomological support. Apply [det-def-localizing-closure-ctf-equals-bc](2) directly on $T$, with $\Lambda=\mathcal O_E$: the coefficient sheaf is the pulled-back integral sheaf identified with $R_T$ in [sk-def-sp-coefficient-towers]. The cited statement gives Tor amplitude in $[r-1,s]$, so $M$ has finite Tor amplitude. All its hypotheses hold on $T$ itself; no affine-local-to-global constructibility claim is used.

Uses: det-def-localizing-closure-ctf-equals-bc, sk-def-sp-coefficient-towers. Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.md, Clause (2), now applied directly to qcqs T.

### Former step 5

Fix any Tor interval $[a,b]$ for $M$ [det-def-sfb-constructible-tor-amplitude]. For any $R_n$-module sheaf $N$ in degree zero, use the explicit sentence “Derived tensor is computed by replacing one factor by a K-flat resolution” in [lem-weil-pbc-ringed-projection-mate-exact], with the identity morphism of the ringed topos, first over $R_n$ to $P_n$ from step 3 and $N[0]$, and then over $R$ to $P$ and $\operatorname{Res}_RN[0]$. Both K-flat complexes have flat terms by steps 1 and 3. This gives
$$(M/\ell^n)\otimes^{\mathbf L}_{R_n}N\simeq P_n\otimes_{R_n}N\cong P\otimes_R\operatorname{Res}_RN\simeq M\otimes_R^{\mathbf L}\operatorname{Res}_RN.$$
The middle isomorphism is induced by $(x\otimes c)\otimes y\mapsto x\otimes cy$, with inverse $x\otimes y\mapsto(x\otimes1)\otimes y$; the balancing relations [def-pur-sheaf-tensor-product] make these sheaf maps, and they commute with differentials. Restriction of scalars leaves the underlying degree-zero sheaf unchanged. Thus the last object has cohomology only in $[a,b]$, proving that every level has Tor amplitude in $[a,b]$. This argument assumes no flatness of $R\to R_n$.

Uses: det-def-sfb-constructible-tor-amplitude, lem-weil-pbc-ringed-projection-mate-exact, def-pur-sheaf-tensor-product. Source: literature/stacks-project/sites-cohomology.tex, Tag 06YU, one-factor K-flat computation, applied twice to the explicit coefficient-balancing isomorphism.

### Former step 6

If $M=0$, its reductions are zero and the one-stratum partition $T=T$ suffices (also when $T$ is empty). Otherwise, for each of the finitely many nonzero cohomology sheaves $H^q(M)$, the qcqs clause of [sk-def-sfb-constructible] supplies a finite stratification of $T$ by constructible locally closed subschemes with finite constant local models. Iterate [lem-weil-pbc-constructible-stratification-intersection] to take their common refinement; its strata are the actual scheme fiber products, and the induced maps to the original strata pull the local models back. On a refined stratum $S$, pro-étale locally, each cohomology sheaf is $R_S\otimes_{\underline{\mathcal O_E}}\underline N$ for a finitely presented $\mathcal O_E$-module $N$. Exactness and tensor compatibility of restriction use [lem-sfb-alpha-iso], [lem-weil-pbc-site-pullback-abelian-exact] and [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Finite coefficient sheaves pull back to the same finite coefficient sheaves by [lem-sfb-alpha-iso] applied to the finite condensed ring.

Put $A=\mathcal O_E$. It is a DVR by [def-weil-l-adic-coefficient-extension](2), hence Noetherian. A finite presentation $A^u\to A^v\to N\to0$ has finitely generated torsion-free kernel $L\subset A^v$, so [lem-sc-dvr-fg-torsionfree-free] gives $L\cong A^w$ and a finite free resolution $0\to A^w\to A^v\to N\to0$. Exact constant inverse image [lem-weil-pbc-site-pullback-abelian-exact] and flatness of $R_S$ over $\underline A$ from [lem-weil-pbc-completed-constant-sheaf-reduction] give a two-term free $R_S$-resolution of the local model. Finite free sheaves are flat because their tensor functors are finite sums of the exact identity functor [def-pc-flat-sheaf-modules], and the complex is K-flat by [lem-pc-bounded-above-flat-kflat-site]. Thus [lem-pur-derived-change-of-rings] computes its reduction by the same two-term matrix over $A_n=A/\ell^n$.

The scalar ring $A_n$ is finite: cofinality in [sk-def-sp-coefficient-towers] gives $\varpi_E^N A\subseteq\ell^nA$ for some $N$, so $A_n$ is a quotient of the finite ring in [def-weil-l-adic-coefficient-extension](4). The kernel and cokernel of the resulting finite matrix are finite $A_n$-modules, hence finitely presented: take all elements as generators and all elements of the finite kernel as relations, and exact constant inverse image identifies the sheaf cohomology with these constant finite modules. Therefore $H^q(M)\otimes_R^{\mathbf L}R_n$, restricted to each stratum, has locally constant finite-type cohomology in degrees $-1,0$ on the same finite global stratification of $T$.

Uses: sk-def-sfb-constructible, lem-weil-pbc-constructible-stratification-intersection, lem-sfb-alpha-iso, lem-weil-pbc-site-pullback-abelian-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-weil-l-adic-coefficient-extension, lem-sc-dvr-fg-torsionfree-free, lem-weil-pbc-completed-constant-sheaf-reduction, def-pc-flat-sheaf-modules, lem-pc-bounded-above-flat-kflat-site, lem-pur-derived-change-of-rings, sk-def-sp-coefficient-towers. Source: literature/stacks-project/sites-modules.tex, Tags 093M (lemma-completion-flat), 093J (lemma-constant-exact); DVR resolution via more-algebra.tex Tag 0AUW; K-flatness via sites-cohomology.tex Tag 06YQ. Constructibility is used globally on qcqs T..

### Former step 7

Use the standard truncations [def-sbc-standard-tstructure-derived-category]. For cohomological support in $[r,s]$, the successive triangles are
$$\tau_{\leq q-1}M\longrightarrow\tau_{\leq q}M\longrightarrow H^q(M)[-q]\longrightarrow(\tau_{\leq q-1}M)[1]\qquad(r\leq q\leq s).$$
The initial object $\tau_{\leq r-1}M$ is zero and the final object $\tau_{\leq s}M$ is $M$. Exact derived coefficient change [lem-pur-derived-change-of-rings] carries these triangles to the finite levels; exact restriction to the strata and the coefficient-preserving tensor comparison in step 6 carry them to the stratum sites. For a resulting triangle, [lem-sf-derived-homology-long-exact] gives the short exact sequence
$$0\longrightarrow\operatorname{coker}(H^{i-1}(Z)\to H^i(X))\longrightarrow H^i(Y)\longrightarrow\ker(H^i(Z)\to H^{i+1}(X))\longrightarrow0.$$
The ring $A_n$ is Noetherian since it is finite. The small-site theorem [lem-weil-pbc-locally-constant-derived-serre] closes locally constant finite-type $A_n$-sheaves under these kernels, cokernels and extensions. Starting from zero and the shifted reductions supplied by step 6, finite induction proves that the cohomology of $M/\ell^n$ is locally constant of finite type on each stratum. Because $A_n$ is finite, a finitely generated local $A_n$-module is finite as a set, and each geometric stalk is that finite local module. The strata of step 6 partition $T$ globally into finitely many constructible locally closed subschemes with actual immersion maps. These verify every clause of [def-weil-proetale-constructible-sheaf]. Hence every level has constructible cohomology in the sense of [def-weil-proetale-constructible-sheaf], with the same global finite partition of $T$.

Uses: def-sbc-standard-tstructure-derived-category, lem-pur-derived-change-of-rings, lem-sf-derived-homology-long-exact, lem-weil-pbc-locally-constant-derived-serre, def-weil-proetale-constructible-sheaf. Source: literature/stacks-project/sites-modules.tex, Tag 093U (3), with derived truncation triangles from derived.tex Tags 08J5 and 05RS; finite induction on the global constructible stratification.

### Former step 8

In the Tor test of step 5 take $N=R_n$. Tensoring with this unit returns $M/\ell^n$, so its cohomology vanishes outside the same $[a,b]$. Steps 5--7 give finite-Tor constructible levels with a common cohomological interval, and step 3 gives all normalization isomorphisms. These are the defining conditions of [sk-def-sp-normalized-towers], so the strict derived tower constructed in steps 1--2 belongs to its normalized full subcategory.

Uses: det-def-sfb-constructible-tor-amplitude, sk-def-sp-normalized-towers. Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-def-sp-normalized-towers/sk-def-sp-normalized-towers-reduction.md, Constructibility conclusion for qcqs T; unit definition of normalized constructible towers.

## Searches and duplicate audit

Before creating nodes I searched the whole DAG by titles/statements, tags and concepts, and the whole imported blueprint using tools/blueprint_refs.py search. Search questions included strict coefficient reduction, derived scalar transitivity, finite matrix reduction, stratified reduction, mixed tensor, finite local model, Postnikov, strict tower, scalar extension, constant local model, K-flat, locally constant and Serre. Regex-like queries which produced zero hits were followed by literal-word searches. Blueprint ancestor is the item itself, so each new node has an empty via list. No imported blueprint node states a new node exactly. All Mathlib entries are copied from the actual per-item searches.jsonl query text; results are the actual hit names and counts. Second semantic phrasings were run for all four questions. The first broad grep matched restrictScalars/IsScalarTower text rather than strict systems; a focused CategoryTheory grep then found zero hits. The first matrix Loogle query reported unknown identifier Sheaf, so I also ran and read the valid SheafOfModules.IsFinitePresentation query. Its five hits define local finite presentation, without derived coefficient reduction or finite constant cohomology.

I read Mathlib ExactFunctor.lean's exact-functor requirements, Monoidal/Tor.lean's projective-resolution Tor definition, Presheaf/Monoidal.lean's ordinary tensor construction, Sheaf/Quasicoherent.lean's presentation definition, and Abelian/SerreClass/Basic.lean's Serre closure. None is a one-line specialization to these new comparisons. Ordinary scalar cancellation and ordinary completion hit different categories. The pre-existing item searches are retained unchanged.

## Not duplicates

lem-sp-strict-coefficient-tensor-descent vs lem-pe-kflat-roos-representative-invariance: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-pe-kflat-roos-representative-invariance instead asserts K-flat representative invariance of augmented scalar-extension Roos cones. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-pe-two-term-reduction-cohomology: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-pe-two-term-reduction-cohomology instead asserts Cohomology and quotient maps of a two-term integral coefficient complex. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-pe-restricted-kflat-tensor-identification: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-pe-restricted-kflat-tensor-identification instead asserts Restricted scalar-first K-flat tensor models identify derived scalar extensions. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs def-pe-integral-presentation-encoding: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; def-pe-integral-presentation-encoding instead asserts Specified integral coefficient presentation encoding. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-pe-kflat-scalar-tower-realization: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-pe-kflat-scalar-tower-realization instead asserts K-flat realization of the augmented derived scalar-extension tower. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-sfb-ringed-finite-free-resolution-tensor: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-sfb-ringed-finite-free-resolution-tensor instead asserts Tensor computation from a specified bounded-above finite free sheaf resolution. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-pe-integral-reduction-transition-comparison: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-pe-integral-reduction-transition-comparison instead asserts Quotient transitions under normalized integral coefficient comparison. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-pe-integral-normalized-restriction-squares: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-pe-integral-normalized-restriction-squares instead asserts Normalized finite restriction squares for the integral coefficient presentation. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-sbc-derived-scalar-extension-counit-shift: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-sbc-derived-scalar-extension-counit-shift instead asserts Counit-compatible shift structure of derived change of rings on a site. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-sbc-koszul-tensor-derived-tower: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-sbc-koszul-tensor-derived-tower instead asserts Ordinary Koszul tensor towers represent derived tensor towers. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-sbc-scalar-extension-counit-properties: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-sbc-scalar-extension-counit-properties instead asserts K-flat computation and triangulatedness of a specified scalar-extension counit. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-sbc-derived-coefficient-map-descent: the new statement asserts the normalized strict-system tensor complex and its resolving-class descent for arbitrary ring-sheaf sequences; lem-sbc-derived-coefficient-map-descent instead asserts Descent of a termwise coefficient map through a resolving counit. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-sfb-ringed-finite-free-resolution-tensor: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-sfb-ringed-finite-free-resolution-tensor instead asserts Tensor computation from a specified bounded-above finite free sheaf resolution. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-weil-pbc-integral-local-reduction-lower-bound: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-weil-pbc-integral-local-reduction-lower-bound instead asserts A completed integral local reduction loses at most one lower degree. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-weil-pbc-regular-single-reduction: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-weil-pbc-regular-single-reduction instead asserts Reduction preserves a regular single module in degree zero. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-weil-pbc-alternating-unit-resolution: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-weil-pbc-alternating-unit-resolution instead asserts Alternating unit resolution of an exact periodic pair. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-weil-pbc-ringed-tensor-cohomological-bounds: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-weil-pbc-ringed-tensor-cohomological-bounds instead asserts Cohomological bounds for derived extension of ring-sheaf scalars. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-sbc-koszul-tensor-derived-tower: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-sbc-koszul-tensor-derived-tower instead asserts Ordinary Koszul tensor towers represent derived tensor towers. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-weil-pbc-regular-quotient-self-cohomology: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-weil-pbc-regular-quotient-self-cohomology instead asserts Self-reduction along a regular quotient. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-weil-pbc-periodic-quotient-tor: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-weil-pbc-periodic-quotient-tor instead asserts Tor from an exact periodic unit pair. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-weil-pbc-uniformizer-reduction-cohomology: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-weil-pbc-uniformizer-reduction-cohomology instead asserts Cohomology commutes with completed principal reduction under injectivity. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-weil-pbc-principal-adjacent-quotient-tor: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-weil-pbc-principal-adjacent-quotient-tor instead asserts Residue Tor between adjacent principal quotients. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-sf-cochain-tensor-model-rigidity: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-sf-cochain-tensor-model-rigidity instead asserts Rigidity of derived tensor models on cochain representatives. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-mixed-derived-coefficient-cancellation vs lem-exc-intrinsic-resolution-tensor-homology: the new statement asserts mixed derived tensor cancellation with arbitrary degree-zero target modules and the actual coefficient-transition adjunct; lem-exc-intrinsic-resolution-tensor-homology instead asserts Tensor cohomology in the intrinsic coefficient presentation. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sfb-scalar-finite-free-resolutions: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-sfb-scalar-finite-free-resolutions instead asserts Scalar finite free resolutions over a DVR and finite bases over a field. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sfb-ringed-finite-free-resolution-tensor: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-sfb-ringed-finite-free-resolution-tensor instead asserts Tensor computation from a specified bounded-above finite free sheaf resolution. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-weil-pbc-integral-local-reduction-lower-bound: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-weil-pbc-integral-local-reduction-lower-bound instead asserts A completed integral local reduction loses at most one lower degree. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sbc-root-normalization-generic-stalk-flat: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-sbc-root-normalization-generic-stalk-flat instead asserts Flat normalization stalks at the generic root divisor. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-pod-point-exact-extension-sections: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-pod-point-exact-extension-sections instead asserts Exact completed extension and sections adjunction at a point. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sf-etale-tor-flat-pullback-model: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-sf-etale-tor-flat-pullback-model instead asserts Etale finite-Tor flat models with their termwise geometric pullback. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-weil-ramified-pullback-tower-identification: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-weil-ramified-pullback-tower-identification instead asserts Ramified identification of the scalar-extended finite pullback tower. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-weil-ramified-coefficient-quotient-comparison: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-weil-ramified-coefficient-quotient-comparison instead asserts Ramified completed coefficient quotient comparison. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sf-open-quotient-koszul-completeness: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-sf-open-quotient-koszul-completeness instead asserts DVR quotient augmentation, Koszul completion and open completeness. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sf-integral-line-tensor-comparison-representative: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-sf-integral-line-tensor-comparison-representative instead asserts K-flat line tensor models and finite balancing. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-tw-finite-projective-model-pullback: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-tw-finite-projective-model-pullback instead asserts Normalized finite-projective constant models under ordinary derived pullback. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-trf-point-reduction-unit-normalization: the new statement asserts simultaneous finite scalar matrix reductions of one integral finite constant local model; lem-trf-point-reduction-unit-normalization instead asserts Point coefficient-reduction comparisons are normalized by scalar-extension units. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs lem-sfb-degreewise-bounded-devissage: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; lem-sfb-degreewise-bounded-devissage instead asserts Existing degreewise dévissage for a finite cohomological interval. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs prop-weil-pbc-integral-tstructure: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; prop-weil-pbc-integral-tstructure instead asserts The standard t-structure on the integral category. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs prop-weil-pbc-levelwise-truncations: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; prop-weil-pbc-levelwise-truncations instead asserts Levelwise truncations of the adic tower. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs thm-weil-pbc-integral-truncations: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; thm-weil-pbc-integral-truncations instead asserts Truncations of the integral category. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs lem-weil-envelope-tstructure: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; lem-weil-envelope-tstructure instead asserts The envelope inherits the t-structure. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs def-weil-t-structure: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; def-weil-t-structure instead asserts t-structure. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs prop-weil-localized-tstructure: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; prop-weil-localized-tstructure instead asserts The rational t-structure. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs def-sbc-standard-tstructure-derived-category: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; def-sbc-standard-tstructure-derived-category instead asserts The standard t-structure on the derived category of an abelian category. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs lem-trf-finite-locally-constant-coherent: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; lem-trf-finite-locally-constant-coherent instead asserts Finite locally constant set sheaves are coherent and stable under finite operations. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs lem-pc-derived-lower-truncation-step-ses: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; lem-pc-derived-lower-truncation-step-ses instead asserts Successive lower truncations have a two-term kernel quasi-isomorphic to one cohomology object. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs lem-pc-lower-truncation-transition-kernel: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; lem-pc-lower-truncation-transition-kernel instead asserts Kernel geometry and homology of a fixed successive lower truncation transition. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-stratified-reduction-postnikov-comparison vs lem-pc-natural-bounded-below-truncation-couples: the new statement asserts coefficient-preserving restriction of derived reduction plus finite Postnikov propagation on a supplied global partition; lem-pc-natural-bounded-below-truncation-couples instead asserts Individual bounded-below truncation couples with natural comparisons. The latter is an input or a different comparison, not the complete assertion of the new node.

lem-sp-strict-coefficient-tensor-descent vs lem-coef-derived-system-evaluation-calculus: that node fixes uniformizer quotient rings and a completed scalar source and also constructs limit adjunction/internal-Hom calculus; the new node gives resolving-class descent for arbitrary small ringed sites and arbitrary R-algebra sequences, including nonsurjective maps, without a completed source or limit.

lem-sp-strict-coefficient-tensor-descent vs lem-coef-semilinear-derived-sections: the latter gives system scalar-extension operations, not the displayed strict one-source K-flat roof comparison and resolving-class descent normalization; the statement of the new node exposes exactly this representative argument.

lem-sp-mixed-derived-coefficient-cancellation vs lem-pur-system-scalar-coherence: scalar-composition associators there concern repeated extension and their universal counits, whereas mixed cancellation here allows arbitrary target module N, retains exact restriction of scalars, proves the Tor test, and identifies the particular transition adjunct. Ordinary cancellation nodes lem-sfb-scalar-tensor-cancellation-independent and lem-pur-change-of-rings-tensor-cancellation-independent have no derived assertion.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sfb-finite-constant-model-two-term-free-resolution: the latter ends at the integral scalar/sheaf resolution; the new statement includes its simultaneous finite coefficient matrix realizations with actual transitions, finite quotient rings, and constant finite kernel/cokernel sheaves.

lem-sp-stratified-reduction-postnikov-comparison vs lem-sfb-degreewise-bounded-devissage: generic devissage assumes a supplied extension-closed property Q and proves Q(K); it neither identifies reduction with restriction on strata nor checks finite local models and finite stalks on a global partition. The new node must construct that comparison and verify this application of Q.

lem-sp-stratified-reduction-postnikov-comparison vs lem-weil-pbc-integral-reduction-constructible: the older node assumes a noetherian topological space and addresses a single reduction; the new node works on arbitrary T with a supplied finite partition and specifies all restricted reductions, exact truncation-image triangles and the same partition for every level.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-pc-bounded-above-flat-tensor-acyclic-degree: the existing node proves acyclicity of the total tensor in a fixed degree; it does not construct finite scalar matrix models or their quotient transitions.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-weil-pbc-completed-adic-koszul-kflat: the existing node proves K-flatness of a specified completed Koszul complex, without the arbitrary finite module models or finite matrix cohomology.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-weil-pbc-independent-bounded-flat-kflat: the existing node is the bounded-flat K-flat criterion; the new task must construct a finite scalar presentation and all its quotient realizations.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-weil-pbc-site-tensor-local-model-comparison: the existing node compares tensor cohomology of supplied constant-ring models; the new task constructs integral models and their simultaneous finite quotient matrices and constant finite cohomology.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-weil-pbc-split-perfect-tensor-kinjective: the existing node concerns K-injectivity after tensoring a split perfect complex, not reduction of finite integral local models.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sfb-constant-field-tor-bounds: the existing node assumes a field and bounds Tor; here the integral scalar ring is a DVR and the conclusion specifies finite quotient matrix models with transitions.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sfb-finite-flat-constructible-total-tensor: the existing node assumes a Noetherian etale setting and finite coefficients and addresses total tensor constructibility; here integral pro-etale local models must first be resolved and simultaneously reduced.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sfb-finite-free-mono-cokernel-kflat: the existing node starts from a monomorphism of finite free sheaves and gives K-flatness; here the scalar matrix must be constructed and its finite quotient cohomology and transitions identified.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sfb-flat-scalar-cyclic-resolution: the existing node resolves the single cyclic scalar quotient over a supplied flat sheaf algebra; the new task handles arbitrary finitely presented integral modules and all finite reductions on one cover.

lem-sp-integral-local-model-finite-matrix-reduction vs lem-sfb-flat-scalar-tensor-resolution: the existing node computes derived tensor from supplied scalar projective resolutions; it does not construct the finite two-term matrix or prove simultaneous finite constant kernel/cokernel models.

lem-sp-mixed-derived-coefficient-cancellation vs lem-fd-ringed-flat-single-tensor-cohomology: the existing node concerns cohomology after tensoring one flat sheaf over one ring; mixed cancellation allows nonflat ring changes and arbitrary target modules.

lem-sp-mixed-derived-coefficient-cancellation vs def-pc-derived-tensor-cohomology-vanishes: the existing node defines a vanishing predicate and proves no mixed cancellation or transition comparison.

lem-sp-mixed-derived-coefficient-cancellation vs def-pc-derived-tensor-complex-cohomology-vanishes: the existing node defines a complex vanishing predicate and proves no derived change-of-rings comparison.

lem-sp-mixed-derived-coefficient-cancellation vs def-sc-derived-tensor-augmentation: the existing node defines augmentation data; it does not prove the mixed derived comparison or preservation of Tor intervals.

lem-sp-mixed-derived-coefficient-cancellation vs lem-sc-source-kflat-tensor-left-triangulated: the existing node gives triangulatedness of tensor with one source over one ring, without mixed restriction of scalars or actual coefficient-transition adjuncts.

lem-sp-mixed-derived-coefficient-cancellation vs def-pd-section-derived-realization: the existing node specifies internal/section realization comparisons, not a theorem for arbitrary ring maps and arbitrary target modules.

lem-sp-mixed-derived-coefficient-cancellation vs def-pd-section-derived-tensor-data: the existing node defines conjugate section tensor data, rather than proving cancellation across ring changes.

lem-sp-mixed-derived-coefficient-cancellation vs lem-pd-section-kflat-tensor-comparison: the existing node compares internal and section tensors under a fixed exact equivalence; the new node compares two scalar rings and preserves arbitrary Tor intervals.

lem-sp-mixed-derived-coefficient-cancellation vs def-weil-pbc-completed-constant-realization-data: the existing node is a record of supplied completed realization and reduction data; it does not establish mixed scalar cancellation.

lem-sp-mixed-derived-coefficient-cancellation vs def-weil-pbc-tensor-descent-representative-comparison: the existing node defines the published two-factor representative comparison over one ring and explicitly makes no scalar-restriction assertion.

lem-sp-mixed-derived-coefficient-cancellation vs lem-weil-pbc-completed-constant-derived-tensor-tower: the existing node derives an ordinary diagram of R-module tensors; it does not identify extension to S followed by tensor with an arbitrary S-module N, or the specified transition adjunct.

lem-sp-mixed-derived-coefficient-cancellation vs lem-sfb-successive-derived-quotient-normalization: the existing node already gives successive scalar-extension coherence, which the future proof can reuse; it has target a ring sheaf T and does not state mixed cancellation with arbitrary S-module N or the resulting Tor-interval test.

lem-sp-stratified-reduction-postnikov-comparison vs lem-sfb-rhom-colimit-cohomology-ladder: the existing node concerns filtered colimits of derived Hom and signed long exact ladders; no geometric restriction or coefficient reduction is asserted.

lem-sp-stratified-reduction-postnikov-comparison vs lem-cbc-finite-extension-reduction-cone-bound: the existing node gives a cohomological bound for one reduction cone, without coefficient-preserving stratum restriction, finite local models, or a global constructible partition.

lem-sp-stratified-reduction-postnikov-comparison vs lem-sf-derived-homology-long-exact: the existing node is the generic long exact cohomology sequence; the new task constructs geometric coefficient comparisons and carries out its finite local-model application.

lem-sp-stratified-reduction-postnikov-comparison vs lem-sp-derived-split-fibre-projections: the existing node concerns split graph/fibre triangles, not restricted coefficient reduction or finite stratified cohomology.

lem-sp-stratified-reduction-postnikov-comparison vs lem-pc-raw-truncation-couple-naturality: the existing node concerns naturality of raw spectral couples, without reduction or geometric restriction.

lem-sp-stratified-reduction-postnikov-comparison vs lem-weil-pbc-finite-postnikov-isomorphism: the existing node propagates invertibility of a supplied natural transformation through finite Postnikov towers; the new task constructs the stratum/reduction comparison and proves finite locally constant cohomology.

lem-sp-stratified-reduction-postnikov-comparison vs lem-weil-pbc-heart-test-bounded-below: the existing node tests invertibility on a heart for bounded-below objects; it contains no finite scalar coefficient comparison or constructible partition assertion.

lem-sp-stratified-reduction-postnikov-comparison vs lem-weil-pbc-truncation-descends: the existing node descends truncation functors; it does not compare geometric restriction with reduction or establish the finite constant local-model conclusion.

lem-sp-strict-coefficient-tensor-descent vs def-a1-integral-completed-tower-pullback-universes: the existing node defines completed integral resolving-pair data and ordinary module towers; the new theorem establishes descent for arbitrary R-algebra sequences into strict semilinear systems.

lem-sp-strict-coefficient-tensor-descent vs lem-a1-principal-koszul-strict-replacement: the existing node replaces a supplied completed quotient tower by a Koszul tower; the new task constructs and descends a one-source tensor functor for arbitrary coefficient sequences.

lem-sp-strict-coefficient-tensor-descent vs lem-per-proetale-scalar-slice-comparison: the existing node compares scalar extension with restriction to a slice site, not localization into the derived category of strict semilinear systems.

lem-sp-strict-coefficient-tensor-descent vs def-pc-derived-tensor-cohomology-vanishes: the existing node defines a vanishing predicate and contains no strict-system descent theorem.

lem-sp-strict-coefficient-tensor-descent vs def-pc-derived-tensor-complex-cohomology-vanishes: the existing node defines tensor-complex vanishing and does not construct a strict coefficient system or its localization.

lem-sp-strict-coefficient-tensor-descent vs def-pc-kflat-complex: the existing node defines K-flatness, without the resolving-class localization and strict-system functor asserted here.

lem-sp-strict-coefficient-tensor-descent vs def-sc-bounded-flat-shift-representative: the existing node defines a bounded flat representative predicate; it does not establish unbounded strict-system descent.

lem-sp-strict-coefficient-tensor-descent vs def-sc-derived-tensor-augmentation: the existing node defines augmentation data rather than proving simultaneous strict quotient-transition descent.

lem-sp-strict-coefficient-tensor-descent vs def-sc-flat-telescope-stage-map: the existing node defines stage maps in a telescope, not the strict semilinear-system tensor functor.

lem-sp-strict-coefficient-tensor-descent vs lem-pc-bounded-above-flat-kflat-site: the existing node is a bounded-flat criterion; the new node proves unbounded resolving-class descent into strict coefficient systems.

lem-sp-strict-coefficient-tensor-descent vs lem-pc-bounded-above-flat-tensor-acyclic: the existing node proves a tensor-acyclicity criterion without coefficient-system localization or roof independence.

lem-sp-strict-coefficient-tensor-descent vs lem-pc-complex-hocolim-colimit: the existing node identifies a complex homotopy colimit with its colimit, without the coefficient-sequence construction or descent.

## Review by Q92

I read the current main-20261015 reduction statement, the normalized-tower unit and smooth-purity chapter, the exact Lean theorem and its docstring, and the released re-split note. The source is an imported agent-written construction; the expanded old argument, not an unrelated proof route, supplies the four tasks. I read Stacks sites-cohomology.tex at 06YS (lemma-K-flat-resolution), 0G7D (lemma-factor-through-K-flat), 0G7E (lemma-pullback-K-flat), 06YU (definition-derived-tor), 06YY (lemma-derived-base-change), and the bounded-flat criterion 06YQ. For the matrix task I read sites-modules.tex 093J (lemma-constant-exact), 093M (lemma-completion-flat), and more-algebra.tex 0AUW (lemma-dedekind-torsion-free-flat). For the stratum/Postnikov task I read sites-modules.tex 093U(3) and derived.tex 08J5 and 05RS. The new source fields give the tags and labels. No source claims that tensor sheaves are computed sectionwise: every generator formula is followed by sheafification.

Step 1 takes strict-system descent and the evaluated quotient transitions from the first new statement, and identifies its category using det-sp-coefficient-towers-abelian(1)--(2). The hypotheses match because R_T maps compatibly to each finite quotient on the fixed small site. Step 2 uses exactly the actual transition-adjoint clause of the mixed-cancellation statement; it does not infer invertibility merely from isomorphic endpoints. Step 3 uses clause (2) of ctf-equals-bc for the existence of the integral Tor interval and the second new node for preservation of any interval; qcqs is imposed here and not used for arbitrary-T normalization. The coefficient identification is precisely the inverse limit in sk-def-sp-coefficient-towers.

Step 4 uses the qcqs finite global partition in sk-def-sfb-constructible, the fiber-product common refinement in constructible-stratification-intersection, and the two new local/global statements for finite matrix models and their stratum/truncation comparisons. I checked that the local-matrix statement is about finite constant local models rather than arbitrary integral constructible complexes. The global/Postnikov statement assumes the actual finite immersed partition and states the derived restriction comparison; it does not get it from a definition. Its induction concerns images of truncation triangles, not a false claim that nonflat reduction commutes with truncation. Existing degreewise-bounded-devissage and locally-constant-derived-serre provide generic inputs to that task. Step 5 just reads the normalized full-subcategory definition with the bounds and maps already supplied. citations.json contains verbatim portions of the actual statements for every cited step/node pair.

I checked zero modules, zero M, the empty scheme, equal quotient indices, chains of three indices, free scalar modules, and torsion scalar modules A/pi. The ramified case is covered by cofinal ell- and pi-powers, not by identifying ell with a uniformizer. The torsion example has cohomology in degrees -1 and 0, confirming that no flatness of R to R_n was smuggled in. The Noetherian assumption used for Serre closure is on the finite scalar ring A_n, not on the stratum. The fixed finite global partition is supplied, so no affine-local-to-global finite-partition claim is hidden. Statements and proof dependencies are acyclic by construction: no new statement refers to the item, and the four new nodes have empty proof/proof_deps. All non-elementary assembly steps are below 2000 characters and the complete assembly is below 3000. Every new node is statement-only.

The first dry run exposed additional same-tag pairs because the server and read clone enumerate nodes differently. I opened the listed statements, distinguished their actual conclusions above, and retained the source tags. In particular the existing successive-derived-quotient-normalization theorem supplies ring-valued associativity but not the arbitrary-module Tor test; the generic completed-constant-derived-tensor-tower does not provide strict semilinear target descent. I also removed spurious statement dependencies parsed from interval notation; every retained dependency is an actual named node.

## Unfinished

No stage-1 repair work is intentionally left unfinished. The four new proofs are deliberately unsplit independent tasks, as ordered. Their statements, sources, logged searches and the full allocated old argument are available above. No Lean was written or compiled.
