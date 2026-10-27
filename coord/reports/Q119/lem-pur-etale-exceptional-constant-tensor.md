# Q119 repair: lem-pur-etale-exceptional-constant-tensor

The returned item has been re-split into four independently claimable statement-only nodes. The item's statement is retained byte for byte; its proof is now four assembly steps, 1982 characters in total. All four new nodes have status `unsplit`, empty proof/proof_deps, null proof_origin and mathlib_match, and inherit the chapter and unit. No Lean was written and no compiler, Lake or build was run.

The sandbox initially contained only dispatcher brief markers, with no retained node, report or search log. The first required dry run exited with “FAILED: no node files under .../dag/nodes/”. I copied the current live node, which contains the exact ten-step returned proof and existing searches, as the baseline. `returned-baseline.json` retains that full record locally. No repository git command was run. All maintainer-owned fields, the source, existing search records, and statement dependencies remain unchanged in the delivered item. The delivery tool rebases the result on current server state.

## Repair of every return point

The sole numbered substance of this return is the human's re-split decision: spread all 10238 characters of proof work into at least three comparable new nodes, leave those nodes statement-only, and assemble them in at most 3000 characters. The four packages below divide the old argument as 2969, 2299, 2815 and 2155 characters. No package states the whole original theorem: geometry/amplitude, coherent left projection, compactness/right-adjoint sums, and an abstract conditional mate-generation theorem are separate tasks. The last is independent of schemes; the third assumes the independently proved amplitude and projection inputs. No new package depends on another new package, so all four are available in parallel. Their statements expose the exact interfaces needed by the parent.

| New node | Retained argument | Separate obligation |
|---|---|---|
| lem-pur-etale-support-unbounded-amplitude | old steps 1–3 | Noetherian hypotheses, a uniform fibre bound, sheaf bounds, lower-bound injectives, exactness/sums and the brutal-truncation telescope |
| lem-pur-etale-support-projection-shift-unit | old steps 4 and 8 | Proper/open projection composite, constants, signs, stalk-detected equality, unit and coefficient-shift squares |
| lem-pur-etale-support-compact-adjoint-sums | old steps 5–7 | Constructible finite-Tor images, compact tests, right-adjoint sums, adjunction-compatible exact shifts and exact coproduct-preserving coefficient functors |
| lem-pur-coefficient-action-adjoint-generation | old steps 9–10 | Abstract counit-mate naturality, shift and unit calculations, localizing isomorphism locus, and generation by the ring |

The complete original arguments follow below, with every old citation and its original source assignment. This is the handoff proof plan for each new worker, not proof text inserted into any new node. Every argument is assigned exactly once. In particular I did not suppress the telescope, the finite-Tor argument over nonregular rings, the coefficient-shift sign check, the counit equation, or the coproduct part of localizing generation. Resolution independence is also carried by the new projection statement and by the parent's final assembly via uniqueness of adjunction transposition.

## Attachment check and Mathlib results

I searched `lean/WeilConjectures/` by the item tag and exceptional/constant/tensor notions, and read `lean/Sheaf/AlgebraicGeometry/EtaleExceptionalConstantTensor.lean`. The item's `exceptionalConstantTensor` theorem (line 321) ends in `sorry` (line 367), so this is not an attachment. The proved upstream `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nat` in `SixFunctors/Etale/Derived/ConstantTensorProjection.lean` concerns ordinary direct image and a finite module; it does not give the exceptional right-adjoint tensor map, the uniform amplitude or arbitrary unbounded coefficient complexes. It was therefore not claimed as an attachment.

Each new node was searched through msearch.py with LeanFinder, Loogle, grep and LeanSearch, and a second LeanFinder phrasing. All services answered. Exact commands and actual results are retained in searches.jsonl, search-plan.json and the four *.search.txt files; the JSON nodes record those same tool/query pairs and actual output with per-node verdicts. The unbounded-amplitude hits are t-structure predicates/representatives, with unrelated continuous compact-support grep hits. The projection hits concern complex unit constraints, Tor, algebraic etaleness and ordinary adjunction shifts. The compact-image hits concern light condensed internal projectivity, ordinary adjoint limit preservation and qcqs sections. The abstract mate hits include Adjunction.CommShift machinery, scalar adjunctions and reflective monoidal structures, but none proves this invertibility theorem for exact D(C)-coefficient functors. I read the adjunction shift source as a supporting candidate. None of these is an exact match or a one-line specialization for a complete package; there are zero new Mathlib leaves.

## Blueprint and source reading

I read the chapter record sec-smooth-purity, unit sk-def-sf-operations, GOAL.md, the three blueprint levels in SETUP.md, the worker/stage documents and delivery-errors sections B–E. The current ancestor text is `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md`, particularly its adic-stage paragraph on compatible finite functors. This repair supplies the constant-coefficient tensor input below that paragraph; it does not change the unit or chapter route. Each new blueprint.from has that ancestor, its exact place and via `[item, lem-pur-etale-coefficient-system-adjoint]`.

I ran blueprint_refs.py ancestor and whole-blueprint searches for “constant tensor”, “compact generators”, “projection shift”, “cohomological amplitude”, “projection formula”, “adjunction transpose”, “adjoint tensor”, “compact support amplitude” and “coefficient action”. I searched the whole DAG by statements, titles, sources and these notions, and read the near matches listed below. No blueprint node states a proposed package in the required generality, so same_as is empty.

For the item and packages 1–2, I read Zheng Theorem 2.18(2) and Corollary 2.19 on printed p. 12: they cover all unbounded inputs and a 2d amplitude bound. For package 3, I read Bhatt–Scholze Definition 6.3.1, the start of Section 6.4, Example 6.4.1 and Proposition 6.4.8 on printed pp. 45, 48–49. These distinguish perfect-valued constructibility from mere finite cohomology; the inherited finite-Tor compact-generator node supplies the precise version used here, including the nonseparated case. For package 4, I read Zheng Construction 2.26 on printed p. 15, whose adjunct is exactly inverse projection followed by the fixed counit, and Proposition 2.29(2) on p. 16 for the resulting constant-tensor assertion. The inherited independent compactness/generation proof is retained: I do not adopt that proposition's smooth-purity argument.

I also read Stacks derived.tex lemma-adjoint-is-exact (0A8D) and sites-cohomology.tex lemma-pullback-tensor-product (07A4) and equation-projection-formula-map (0B56). The latter constructs the actual map and does not itself assert an arbitrary unbounded projection isomorphism; the proper and open nodes supply that. No prohibited SGA source or trace route is used. No literature is wanted.

## Not duplicates

lem-pur-etale-support-unbounded-amplitude vs lem-dg-compact-support-amplitude: the existing theorem only bounds higher compact-support images of a sheaf; the new package proves the bound on all bounded-above unbounded-derived inputs, uniform geometric d, and exactness/coproducts/lower bounds.
lem-pur-etale-support-unbounded-amplitude vs lem-pur-bounded-heart-amplitude: the existing result propagates a bound only through bounded complexes and assumes an exact functor; the new result includes an arbitrary bounded-above input and establishes geometric functor hypotheses.
lem-pur-etale-support-unbounded-amplitude vs lem-amb-proper-coproducts: the existing result concerns only proper derived direct image, with no compactification composite or amplitude bound.
lem-pur-etale-support-projection-shift-unit vs lem-sf-etale-ambient-adjoint-projection: that result gives the projection isomorphism and a particular mate construction; it states no coefficient-shift equation or unit normalization of the actual map.
lem-pur-etale-support-projection-shift-unit vs lem-amb-proper-coproducts-projection: that result handles only the proper factor and does not state the open composite's shift/unit normalization or the constant-complex pullback comparison.
lem-pur-etale-support-projection-shift-unit vs lem-weil-pbc-ringed-projection-mate-exact: that result supplies proper projection shift/unit coherence for a ringed-topos direct image, not invertibility and coherent proper/open compact-support composition.
lem-pur-etale-support-projection-shift-unit vs lem-sf-finite-exchange-projection-commshift: that result requires bounded finite-Tor constructible pro-etale inputs over the fixed finite-field datum; the new statement is on ordinary etale sites with arbitrary finite primary C, arbitrary algebraically closed k, and arbitrary unbounded inputs.
lem-pur-etale-support-projection-shift-unit vs lem-pur-projection-formula-coefficient-coherence: that result is a bounded pro-etale unit/associativity assertion at special coefficient rings, not this unbounded etale coefficient-shift assertion.
lem-pur-etale-support-compact-adjoint-sums vs lem-pur-etale-finite-ring-compact-generators: the existing result constructs compact tests on a scheme but says nothing about their compact-support images, the right adjoint's coproducts, or coefficient functor exactness.
lem-pur-etale-support-compact-adjoint-sums vs lem-sc-compact-tests-right-adjoint-coproducts: that abstract criterion assumes compact test images; the new package proves this geometric hypothesis from constructibility and finite Tor amplitude and includes exact coefficient functors.
lem-pur-etale-support-compact-adjoint-sums vs lem-pur-etale-closed-right-adjoint-coproducts: that existing result concerns only a closed immersion and its right adjoint, not general separated finite-type f, compact images under F, or the exact coefficient functors.
lem-pur-etale-support-compact-adjoint-sums vs lem-sp-etale-compact-support-tor-window: that result requires separated schemes and a specified bounded flat constructible representative; the new package does not impose separatedness over k or such a representative and includes compact detection and right-adjoint sums.
lem-pur-coefficient-action-adjoint-generation vs lem-sf-generating-class-determination: that theorem propagates an already shift-compatible transformation only through the thick closure. It does not construct the counit mate, prove its shift/unit equations or propagate through coproducts in the unbounded derived module category.
lem-pur-coefficient-action-adjoint-generation vs lem-pc-derived-module-free-generation: that theorem describes the localizing generation of D(C); the new statement constructs and normalizes a particular adjunction mate and proves its invertibility under explicit exact/coproduct hypotheses.
lem-pur-coefficient-action-adjoint-generation vs lem-sfb-derived-scalar-mate-thick-locus: that statement concerns a particular pro-etale ring-change direct-image mate and its thick locus, not arbitrary coefficient-action bifunctors and invertibility on all D(C).
lem-pur-coefficient-action-adjoint-generation vs lem-pur-adjoint-left-projection-action: that result treats the lax monoidal structure of a right adjoint to a strong monoidal functor and does not include triangulated shift normalization, arbitrary coefficient complexes or localizing generation.

## Review by Q119

I checked the repair against the actual node statements, not just their ids or proofs. Parent step 1 takes its coefficient-independent d and every bounded-above input from the explicit conclusion of package 1; no sheaf-only bound is being applied to an unbounded complex. The empty source and d=0 cases are included. Parent step 2 uses package 2's actual map P, its derived-category naturality and resolution independence, and its explicit f*V_Y=V_X identification. That package also states the shift square and unit identity later required; citing only the old open-tensor isomorphism would not have supplied these equations.

Parent step 3 cites packages 1 and 2 precisely to discharge package 3's hypotheses: exact F, the interval bound with N=2d, and the projection for every L,K. The interval bound does not require V to be perfect. Package 3 explicitly concludes the exact coproduct-preserving A_M and B_M with compatible shifts and counit equation; I did not infer sums from being a right adjoint. I checked that the geometric hypotheses are identical in all three packages: f separated finite type, X and Y finite type over algebraically closed k, ell invertible, C finite ell-primary, and no separatedness of Y over k.

Parent step 4 instantiates package 4's bifunctors by constant-coefficient derived tensor. Package 2 supplies precisely its natural unital shift-compatible P. Package 3 supplies the exact coproduct functors and the adjunction-compatible shift structures. The adjunct in package 4 has the same order, P inverse, and fixed counit as the item, so its isomorphism is the requested canonical map. Its conclusion includes naturality in both V and M and the coefficient-shift square; these are not inferred from equality on generators. All citations in these four steps have verbatim quotes in citations.json, taken from the cited statements. The unit-required generating-class and derived-module generation theorems are also used explicitly in parent step 4 for the thick-closure and final localizing-generation inference. Their statements were read and quoted verbatim. The remaining old theorem citations become the explicit future proof plan below; the new nodes intentionally have no proof dependencies yet, as required for a one-level re-split.

For B1–B10, I checked empty proofs and no proof sketch embedded in statements; each node introduces all objects and hypotheses, uses TeX, cites definitions for derived categories/tensor/constructibility/compactness, has an exact source place, real searches and blueprint ancestry. I read close existing results before choosing names. For C1–C8, all non-elementary parent inputs are conclusions of cited new packages, no result is taken from a dependency's proof, and no new node depends on the parent or another new package. The unit is unchanged; the generic bifunctor lemma is below the unit, not a replacement route. For D1–D5, the packages split four different arguments rather than moving everything into one new theorem. For E1–E7, I checked ordinary etale rather than pro-etale categories throughout, arbitrary unbounded V,M, nonregular finite rings, and exactness of constant inverse image, and found no statement dispute.

Small cases: if X is empty, F and G are zero and both comparisons and the 0-bound hold; if f is the identity and d=0, P is tensor identity and its adjoint mate is identity. Finite C=Z/ell^2 tests the finite-Tor rather than finite-module/perfect distinction; no claim that all finite C-modules are perfect occurs. A nonseparated finite-type Y is covered by the inherited compact-generator statement and the finite-type finiteness theorem without strengthening to a separated Y. In the abstract package take A=B=D(C), F=G=identity and both T ordinary derived tensor: its prescribed mate is identity. The abstract package assumes the exact A_M,B_M and their sums, so it makes no false unconditional claim that every right adjoint commutes with tensor. Zero coefficients and zero V or M also give zero maps between zero objects, hence isomorphisms.

There are no non-elementary parent steps over 2000 characters; the longest is below 900. The new packages are statement-only as requested. The old long argument has not been discarded; the following complete handoff preserves it.

## Retained argument for the new workers

### lem-pur-etale-support-unbounded-amplitude

Old step 1 (verbatim):

A field is Noetherian, so $X,Y,\overline X$ are Noetherian by finite type over a Noetherian base, and hence quasi-compact and quasi-separated. Here $\overline X$ is finite type over $k$: on a finite affine cover of $Y$, take finite affine covers of the inverse images under the finite-type map $p_f$; a finite list of $k$-algebra generators for each base algebra, together with the chosen algebra generators upstairs, generates the upstairs algebra over $k$. Thus this assertion follows directly from the definition of finite type. Choose $d\ge0$ bounding the dimensions of the scheme-theoretic fibres of $f$, using quasi-compactness of $Y$. Extension of the residue field to an algebraic closure preserves the dimension of each finite-type fibre, so the same $d$ bounds the geometric fibres. This choice depends only on $f$. If $X$ or $Y$ is empty choose $d=0$; all compact-support values on an empty source are zero. In the rest of the proof any geometric fibre bound $d$ is allowed, and $N_f=2d$.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lem-fin-finite-type-fibre-dimension-bound, lem-kun-dimension-extension, def-weil-finite-type-morphism.

Source: literature/stacks-project/morphisms.tex; Tag 01T6 (lemma-finite-type-noetherian), Tag 0A3V (lemma-morphism-finite-type-bounded-dimension); quasi-separatedness is Tag 01OY in properties.tex; field-extension invariance is the cited lem-kun-dimension-extension.

Old step 2 (verbatim):

The termwise $j_!$ is exact and left adjoint to $j^*$, so its functor on the unbounded derived category is exact and preserves arbitrary coproducts. The total derived $Rp_{f,*}$ is exact by the K-injective derived-functor theorem and preserves arbitrary coproducts by the proper coproduct theorem. Thus $F=Rp_{f,*}j_!$ is exact and preserves arbitrary coproducts. Module sheaves have enough injectives; a bounded-below object in $D^{\ge b}$ has a K-injective representative with zero terms below $b$. Applying the additive $p_{f,*}$ termwise to such a representative shows that $Rp_{f,*}$, and therefore $F$, preserves this lower bound. For a sheaf $H$ on $X$, the compact-support cohomological-dimension theorem applies: $C$ is finite and its additive exponent is invertible since $\ell\ne p$. It gives $F(H)\in D^{[0,2d]}$, for arbitrary $H$, with no constructibility assumption.

Uses: lem-amb-etale-adjoint-locality, lem-sf-exact-functor-derived-triangulated, prop-weil-pbc-kinjective-resolutions-exist, lem-pc-right-derived-functor-triangulated, lem-amb-proper-coproducts, lem-weil-pbc-module-sheaves-enough-injectives, lem-weil-pbc-dplus-injective-representative, lem-dg-compact-support-amplitude.

Source: literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf; Corollary 2.19; unbounded coproducts as in Proposition 2.15. K-injective exactness uses the cited general derived-functor tools.

Old step 3 (verbatim):

Let $K\in D^{\le a}$. Replace it by a complex with zero terms in degrees $>a$, using good truncation. Its brutal lower subcomplexes $B_m=\sigma_{\ge a-m}K$, $m\ge0$, form an increasing sequence with termwise colimit $K$. Each $B_m$ has a finite filtration by its individual terms in their original degrees, so exactness of $F$ and the sheaf bound of step 2 give $F(B_m)\in D^{\le a+2d}$: at a filtration step the cohomology long exact sequence keeps the upper bound. The complex-colimit theorem identifies $K$ with the telescope of $(B_m)$, and the hocolimit-preservation theorem identifies $F(K)$ with a telescope of $(F(B_m))$. Coproducts are termwise in these derived categories, since module sheaves are Grothendieck abelian; their exactness means that a coproduct of objects in $D^{\le a+2d}$ is still in this subcategory. The telescope triangle and its long exact cohomology sequence therefore give $F(K)\in D^{\le a+2d}$. No convergence assertion for an unbounded spectral sequence is needed. Together with step 2, on bounded intervals this gives $F(D^{[r,s]})\subset D^{[r,s+2d]}$.

Uses: def-sbc-standard-tstructure-derived-category, def-kun-truncations, lem-kun-complex-colimit-hocolim, lem-kun-functor-preserves-hocolim, lem-weil-pbc-module-sheaves-grothendieck-abelian, lem-kun-grothendieck-derived-coproducts.

Source: literature/stacks-project/derived.tex; Telescope argument (homotopy colimits); the complex-colimit and exact-functor telescope lemmas cited above.

### lem-pur-etale-support-projection-shift-unit

Old step 4 (verbatim):

For any $L\in D(Y_{\mathrm{et}},C)$ and $K\in D(X_{\mathrm{et}},C)$ compose the proper projection isomorphism and the open-immersion tensor isomorphism:
$$L\otimes^L Rp_{f,*}j_!K\ \cong\ Rp_{f,*}(p_f^*L\otimes^L j_!K)\ \cong\ Rp_{f,*}j_!(j^*p_f^*L\otimes^L K)=F(f^*L\otimes^L K).$$
Both cited statements apply on the ordinary etale sites to arbitrary unbounded complexes and the given finite commutative ring $C$. The pullbacks here are termwise exact inverse images for the constant coefficient ring. Their composite is $f^*$, and $f^*V_Y=V_X$ because inverse image carries the constant ring and constant-module sheafification to the same constant coefficients. The composite is the compact-support projection map: the proper map is the counit projection map with the indicated tensor symmetries, and the open map is the extension-by-zero tensor map. In particular taking $L=V_Y$ proves the first displayed isomorphism in the statement. We retain the stronger formula for arbitrary $L$ for use in the next step.

Uses: lem-amb-proper-coproducts-projection, lem-pur-etale-open-derived-tensor, prop-weil-pbc-inverse-image-modules-exact, def-weil-pbc-constant-sheaf.

Source: literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf; Theorem 2.18(2); equivalently compose the proper and open projection formulas.

Old step 8 (verbatim):

The projection isomorphism of step 4 is natural, unital and compatible with shifts in the coefficient variable $L$. For the proper factor this is the ringed-topos projection-mate exactness theorem. For the open factor use the canonical extension-by-zero tensor map of the cited open tensor theorem. The extension-by-zero stalk theorem identifies its stalk with the identity where the point lies in $X$ and with $0\to0$ outside $X$; the stalk-tensor theorem identifies the tensor factors. These are equalities on sheaf maps: exactness and conservativity of geometric stalks detect zero morphisms by applying the stalk functors to the image of their difference. Apply this degreewise to complexes. These maps commute with the tensor differential $d(x\otimes y)=dx\otimes y+(-1)^{\deg x}x\otimes dy$ and with the usual shift constraints. When factors are interchanged, the symmetry sends $x\otimes y$ to $(-1)^{\deg x\deg y}y\otimes x$, so the same coefficient-shift square still commutes. The tensor-unit map is the identity under the unit constraints. Composition preserves shift compatibility; thus, denoting step 4's coefficient projection map by $P$, the transformation $P^{-1}_{V,GM}$ commutes with coefficient shifts and has $P^{-1}_{C,GM}=1_{FGM}$ under tensor-unit identifications.

Uses: lem-weil-pbc-ringed-projection-mate-exact, lem-pur-etale-open-derived-tensor, def-kun-derived-tensor, lem-kun-tensor-unit, lem-weil-pbc-commshift-nattrans-comp-whisker, lem-weil-pbc-extension-by-zero-stalks, lem-pod-etale-stalk-tensor-scalar, prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative.

Source: literature/stacks-project/sites-cohomology.tex; Tags 07A4 (lemma-pullback-tensor-product), 07A6 (lemma-adjoint), 0B56 (equation-projection-formula-map); the open factor uses Tag 03S5 (proposition-describe-jshriek) in etale-cohomology.tex, with the stated degreewise sign calculation.

### lem-pur-etale-support-compact-adjoint-sums

Old step 5 (verbatim):

Apply the compact-generation lemma to $X$ and $Y$; its hypotheses require finite type over the algebraically closed field and invertibility of $\ell$, not separatedness of either scheme over $k$. Let $(E_s)$ be its family on $X$, and include all integer shifts in the indexing set. To show that $F(E_s)$ is compact, first its cohomology is bounded constructible: the constructible sheaf finiteness theorem applies to each of the finitely many constructible cohomology sheaves of $E_s$, and the successive good-truncation triangles give a finite Postnikov filtration, and exactness of $F$ gives constructibility of $F(E_s)$: the long exact cohomology sequence expresses each new cohomology sheaf as an extension of a kernel and a cokernel of maps between constructible sheaves, which are constructible. Suppose $E_s$ has Tor amplitude $[r,s']$. For every module sheaf $N$ on $Y$, $f^*N$ is a sheaf and step 4 gives
$$F(E_s)\otimes^L N\ \cong\ F(E_s\otimes^L f^*N).$$
The input on the right lies in $D^{[r,s']}$, so steps 2–3 place the output in $D^{[r,s'+2d]}$. Thus $F(E_s)$ has finite Tor amplitude, and compactness on $Y$ follows from the compact-generation lemma. This argument allows nonregular finite rings $C$; no assertion that every finite $C$-module is perfect is used.

Uses: lem-pur-etale-finite-ring-compact-generators, sbc-thm-finiteness-finite-type, def-kun-truncations, thm-constructible-serre.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.4.8, with the finite-Tor interpretation of Definition 6.3.1; compact-support constructibility uses the cited finiteness theorem.

Old step 6 (verbatim):

The adjunction $F\dashv G$ is the fixed one in the item. The test family $(E_s[n])$ consists of compact objects, detects isomorphisms, and has compact images under $F$ by step 5. All categories have set-indexed coproducts and the required locally small Hom spaces. Apply the compact-test right-adjoint coproduct theorem to conclude that $G$ preserves arbitrary coproducts. Explicitly its comparison $\bigoplus_iGM_i\to G(\bigoplus_iM_i)$ induces, on testing with $E_s[n]$, the isomorphism
$$\bigoplus_i\operatorname{Hom}(FE_s[n],M_i)\ \cong\ \operatorname{Hom}(FE_s[n],\bigoplus_iM_i),$$
by adjunction and compactness of $FE_s[n]$. Detection makes the comparison an isomorphism.

Uses: thm-amb-etale-exceptional-adjoint, lem-pur-etale-finite-ring-compact-generators, lem-sc-compact-tests-right-adjoint-coproducts.

Source: literature/stacks-project/duality.tex; Tag 0A9R, the Hom-adjunction compactness calculation stated in lem-sc-compact-tests-right-adjoint-coproducts; compactness is Definition 07LS in derived.tex.

Old step 7 (verbatim):

Equip $G$ with the unique shift structure compatible with the exact functor $F$ and its fixed adjunction. The adjunction-shift theorem supplies it, with the counit equation
$$\epsilon_{M[n]}=\epsilon_M[n]\circ c_{F,n,GM}\circ F(c_{G,n,M}).$$
The triangulated-right-adjoint theorem then makes $G$ exact with this structure. The constant-complex functor $V\mapsto V_T$ is exact and preserves coproducts: the constant presheaf functor does so sectionwise, and sheafification is exact and preserves all colimits. Passing to complexes preserves shifts and cones; termwise coproducts compute derived coproducts. For fixed $M$ it follows that
$$A_M(V)=V_X\otimes^L GM,\qquad B_M(V)=G(V_Y\otimes^L M)$$
are exact functors of $V\in D(C\text{-}\mathrm{Mod})$ and preserve arbitrary coproducts, by the exactness and direct-sum properties of derived tensor and by step 6.

Uses: lem-weil-pbc-adjunction-shift-compatibility-unique, lem-sf-triangulated-right-adjoint, lem-weil-pbc-site-r-module-presheaf-sheafification-exact, lem-sf-exact-functor-derived-triangulated, lem-kun-grothendieck-derived-coproducts, lem-kun-derived-tensor-triangulated, lem-kun-derived-tensor-direct-sums.

Source: literature/stacks-project/derived.tex; Tag 0A8D (lemma-adjoint-is-exact), with the explicitly adjunction-compatible shifts; exactness and sums as in the cited tensor and sheafification lemmas.

### lem-pur-coefficient-action-adjoint-generation

Old step 9 (verbatim):

Define $\alpha_{V,M}:A_M(V)\to B_M(V)$ by transposing
$$F(V_X\otimes^L GM)\xrightarrow{P^{-1}_{V,GM}}V_Y\otimes^L FGM\xrightarrow{1\otimes\epsilon_M}V_Y\otimes^L M.$$
Naturality of $P$, of $\epsilon$, and of the adjunction bijection proves naturality in $V,M$. For completeness the coefficient shift square for $\alpha$ is obtained by transposing its two sides under $F\dashv G$: after using the equation for $\epsilon$ in step 7, the two transposes are precisely the coefficient shift square for $P^{-1}$ from step 8 followed by $1\otimes\epsilon_M$. That square commutes, and the adjunction bijection is injective, so $\alpha$ is compatible with the specified shifts. Under $V=C$, step 8 identifies the transpose with $\epsilon_M$. The adjunction triangle identity says the transpose of $1_{GM}$ is $\epsilon_M$; hence $\alpha_{C,M}=1_{GM}$.

Uses: thm-amb-etale-exceptional-adjoint, lem-weil-pbc-adjunction-shift-compatibility-unique, lem-kun-tensor-unit.

Source: literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf; Construction 2.26, with shift compatibility verified by transposition and the counit equation.

Old step 10 (verbatim):

Fix $M$ and let $\mathcal L_M$ consist of the coefficient complexes $V$ for which $\alpha_{V,M}$ is invertible. It contains $C$ by step 9. Exactness of both functors and the proved shift compatibility imply that it is closed under shifts, distinguished triangles and retracts by the generating-class invertibility theorem. It is also closed under arbitrary coproducts: under the coproduct comparisons for $A_M$ and $B_M$, naturality along every coprojection identifies $\alpha_{\oplus V_i,M}$ with $\oplus\alpha_{V_i,M}$, which is invertible if each summand is. The derived-module free-generation theorem therefore gives $\mathcal L_M=D(C\text{-}\mathrm{Mod})$. Thus the second displayed map in the item is an isomorphism for every unbounded $V$ and $M$. Both maps are constructed from functors, natural maps and the fixed adjunction on the derived categories; changing resolutions computes these same maps, rather than defining a new comparison. This follows for the first map from its proper projection and open tensor construction in step 4, and for the second from the bijectivity of transposition. The argument uses generation only to propagate invertibility, never to infer equality of transformations from their values on generators, and asserts no tensor formula for $G$ with a nonconstant sheaf complex.

Uses: lem-sf-generating-class-determination, lem-pc-derived-module-free-generation, lem-amb-proper-coproducts-projection, lem-pur-etale-open-derived-tensor, thm-amb-etale-exceptional-adjoint.

Source: literature/stacks-project/more-algebra.tex; Tag 09PB (remark-P-resolution) as recorded in lem-pc-derived-module-free-generation; the mate is Zheng Construction 2.26.

## Validation

The mandatory initial no-push run diagnosed the absent sandbox files. The first complete remote dry run identified a unit-route reachability failure: sk-prop-sf-pf-reduction must reach sk-lem-sf-determination. I repaired the parent final assembly to use lem-sf-generating-class-determination explicitly for the thick isomorphism locus, followed by lem-pc-derived-module-free-generation; these are real steps of the preserved original argument, not unused graph edges. The notation c for shifts is now defined locally in both new statements that use it. The repaired remote dry run completed successfully: `OK (not pushed) deliver/Q119/lem-pur-etale-exceptional-constant-tensor at 9bfe9652896: preflight passed`. This includes the server DAG and split-review checks. A final no-push check is run after this validation note and the additional closed-immersion nonduplicate explanation, then the authorized direct push. All four new nodes are unsplit; the only completed natural-language proof here is the parent assembly. There is no claim of completed Lean proofs.
