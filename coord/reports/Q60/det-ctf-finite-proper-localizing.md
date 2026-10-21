# Stage-1 repair: det-ctf-finite-proper-localizing

## Worker report

This repairs the human's 2026-10-21 return of the 15,969-character proof. The latest route note explicitly requires new statement-only nodes, with status unsplit and no proof steps. The previous attempt treated the request for proof drafts as an exception to that rule; its dry runs rejected all six new split nodes. I ran the required initial dry run on the retained sandbox and reproduced exactly those six status failures. I have now applied the clarified rule. The item's statement is unchanged, including the general-field standing setting, the actual adjunction mate and all three conclusions.

Files delivered under dag/nodes/sec-six-functors-basics/:

- det-ctf-finite-proper-localizing.json: existing item, split; five assembly steps, 2609 characters instead of 15,969.
- lem-sfb-finite-proper-geometric-cd-bound.json: new statement, unsplit; no Mathlib match. Uniform geometric fibre bound and torsion cohomological dimension.
- lem-sfb-finite-classical-localizing.json: new statement, unsplit; no Mathlib match. Closure of classical cohomology under triangles, sums, truncations and inverse image, containing the generated category.
- lem-sfb-finite-proper-classical-truncation.json: new statement, unsplit; no Mathlib match. Relative truncation window uniform under every base change.
- lem-sfb-finite-proper-classical-coproducts.json: new statement, unsplit; no Mathlib match. Canonical coproduct comparison for arbitrary unbounded classical families.

These four are precisely the new lemmas directly used by the parent's proof. Each has proof=[], proof_deps=[], proof_origin=null; the next stage-1 workers split them. Their statements, definitions, blueprint references and actual Mathlib search records are retained. Two deeper helper candidates from the previous attempt, neighborhood vanishing and weakly contractible evaluation, are preserved below with all six proof drafts, but are not submitted as orphan nodes. Their unsubmitted JSON drafts and the earlier report also remain in the sandbox's retained-proof-drafts directory. No repository node has been deleted or changed outside this delivery's item. The delivery tools package only the five JSON files under dag/nodes and this report.

Attachments: none. I searched lean/WeilConjectures for the item tag and concepts and read lean/Sheaf/Paper/FiniteProperLocalizing.lean. finiteProperLocalizing and finiteProperLocalizing_baseChange still have sorry. The upstream AlgebraicGeometry.ProEtale.isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology is a related theorem in WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/LowerStarCoproducts.lean, but covers only the sum assertion, under finite-type-over-a-field hypotheses and its specified module-sheaf universe. It neither states every clause of the item nor gives our arbitrary-scheme helper. No partial result is claimed as an attachment.

WANTED: none.

What was wrong: several substantial arguments had remained inside the reviewed parent proof, and the previous repair delivered their proofs as split nodes despite the one-level stage-1 contract. This repair fixes both problems. It also corrects doubled TeX escapes in the short parent proof and says explicitly that the finite-Tor comparison identifies Dctf, rather than suggesting an equivalence of whole unbounded categories. All original parent fields other than proof, proof_deps and split_report remain unchanged. In particular its statement, source, Lean record, review metadata and established general-field route repair are preserved. No new statement dispute is claimed.

What remains: the four new nodes intentionally await their own stage-1 splits. Their proof drafts below preserve the previous work for those workers. There is no remaining gap in the parent's assembly relative to the statements it cites.

## Not duplicates

lem-sfb-finite-proper-geometric-cd-bound vs lem-fin-finite-type-fibre-dimension-bound: the existing node bounds ordinary fibre dimensions; the new one supplies the same bound after every base change and a torsion cohomology bound on every separably closed geometric fibre.
lem-sfb-finite-proper-geometric-cd-bound vs lem-kun-proper-torsion-cd-bound: the existing node assumes a dimension bound and proves relative étale vanishing; the new one obtains a bound from a quasi-compact base and states geometric fibre cohomology.
lem-sfb-finite-proper-geometric-cd-bound vs lem-cbc-compactification-geometry-fibre-bound: that node assumes a Noetherian finite-dimensional base and gives geometric dimensions; the new node only assumes the base quasi-compact and also gives torsion cohomology.
lem-sfb-finite-classical-localizing vs det-pe-classical-derived-weak-serre: the existing node gives closure of sheaves under kernels, cokernels and extensions; the new one gives the derived localizing subcategory, ambient sums, truncations, pullback and containment of Loc(Dctf).
lem-sfb-finite-classical-localizing vs lem-sfb-finite-classical-unbounded-comparison: that node assumes a finite or algebraically closed ground field and gives unbounded essential surjectivity, neither of which is asserted or assumed here.
lem-sfb-finite-classical-localizing vs lem-weil-pbc-proetale-module-cohomology-coproducts: that node concerns classical right derived functors on sheaves of rational modules; the new one concerns classicality of cohomology and closure in derived categories of finite-ring modules.
lem-sfb-finite-proper-classical-truncation vs det-pe-unbounded-classical-truncation: the existing node concerns section cohomology on one site object and assumes vanishing for every classical sheaf; the new one supplies the relative proper hypotheses and produces a sheaf-level window uniform over every base change.
lem-sfb-finite-proper-classical-truncation vs lem-sfb-unbounded-direct-image-truncation-stability: the existing node assumes a finite/algebraically-closed field and an étale input; the new one allows arbitrary schemes with a uniform fibre bound and arbitrary pro-étale classical-cohomology inputs.
lem-sfb-finite-proper-classical-coproducts vs lem-sfb-adic-proper-bounded-below-coproducts: the existing node requires a common lower bound; the new one permits arbitrary unbounded families with classical cohomology.
lem-sfb-finite-proper-classical-coproducts vs lem-weil-pbc-proetale-bounded-below-coproducts: the existing node assumes rational coefficients and a common lower bound; the new node assumes finite-ring coefficients and no such bound.
lem-sfb-finite-proper-classical-coproducts vs det-proper-unbounded-window-ii-general: the existing node concerns E or Qlbar coefficients and ind-constructibility; the new one concerns finite rings, all classical cohomology, and arbitrary schemes with the given relative dimension bound.

None of the four new nodes restates a clause of the item: they provide geometric, cohomological or classical-category input with different hypotheses and conclusions. The item still proves generator preservation, localizing minimality, the actual mate's invertibility, and the open/compactification claims by assembly.

## Review by Q60

I read the main-20261015 item statement and proof, its unit sk-prop-ctf-finite-proper and six-functors chapter. I compared the sandbox against current repository data: the original parent proof has exactly 15,969 characters, and the statement is byte-for-byte identical. This is the deliberate finer split, not an attempt to replace a stale assignment. The unit's route remains finite Tor and constructibility on the étale side, bounded-below comparison, relative finite cohomological dimension for unbounded operations, localizing minimality, and extension by zero. The established repair avoiding an unbounded equivalence over an arbitrary ground field is retained. No forbidden SGA source is used.

I opened the statement of every node cited in each parent step; citations.json contains a verbatim relevant quotation for every pair (step,node). In step 1, finite type over a Noetherian scheme gives Noetherianity, and locally Noetherian implies quasi-separated. Fields are Noetherian because they have only two ideals; finite rings are Noetherian because their ideal sets are finite. These verify the qcqs and coefficient-Noetherian hypotheses of det-pe-finite-tor-comparison-noetherian. Its statement is explicitly an equivalence of Dctf subcategories preserving Tor intervals. The two finite-discrete coefficient nodes identify the actual condensed coefficient with constant A. The new geometric node supplies both the all-base-change dimension bound e and geometric torsion bound 2e. The new classical-closure node puts Loc(Dctf) inside the classical-cohomology category.

In step 2 I checked the statement of det-ctf-finite-proper-tor: it has exactly the standing finite-type separated k-schemes, prime-power coefficient and supplied geometric ell-primary cohomological-dimension bound. We apply it with d=2e and obtain Tor interval [a,b+2e] and constructibility. Properness supplies finite type and separatedness, so the cited separated-implies-quasi-separated lemma verifies the qcqs hypothesis of sk-thm-pe-direct-image-comparison. The input is bounded, hence bounded below, as required by its direct-image clause. That clause is compatible with units and counits. This proves preservation of the small category, without any claim about a general unbounded comparison.

In step 3 the new coproduct node asserts invertibility of the canonical ambient comparison for every small classical family, not merely an unspecified isomorphism of endpoints. Every family in the closure is classical by step 1. The right-derived-triangulated node supplies shifts and distinguished triangles. The objects in the classical subcategory whose images belong to the target closure consequently form a replete triangulated subcategory closed under ambient sums and containing every generator. This is exactly the minimality property in sk-def-localizing-closure. The triangulated-functor-restriction statement supplies the restricted exact functor and its inherited shifts. The closure's indexing universe is the ambient one throughout.

In step 4 the new truncation statement applies to any classical complex after ANY scheme base change, with strict inequality N<m-2e-1. The uniform choice N=m-2e-2 satisfies it on both sides of the naturality square. The new classical-closure statement supplies g'^* classicality and truncation compatibility. Constant-coefficient inverse image is exact, including non-flat g. I read sk-thm-properbasechange: it states the actual exchange on bounded-below classical PRO-ÉTALE module complexes with torsion underlying cohomology, without a constructibility or invertible-torsion hypothesis. Here ell^n kills every cohomology sheaf. Its exchange is defined by sk-def-exchange as the same mate as def-weil-pbc-ambient-ringed-exchange, whose displayed formula is the specified unit, square comparison and counit. Thus the lower map in the naturality square is the same canonical map, and degreewise invertibility of the vertical maps proves the upper map invertible. No extra comparison lemma is hidden behind transport language.

In step 5 det-proper-image-localizing-open has exactly the standing schemes and includes finite discrete ell-primary rings among its admissible coefficients. Its statement gives preservation of Dctf, ambient sums and the exact restricted functor. Composing with step 3 proves the compactification statement; the canonical coproduct maps compose because their composites with each coprojection are the respective functor images of that coprojection. The empty family follows from additivity.

For the geometric-bound node I read Stacks Tag 0A3V, morphisms.tex, lemma-morphism-finite-type-bounded-dimension, together with the existing dimension-base-change and supremum-of-local-dimensions statements. They justify keeping a single e for every base change. The geometric cohomology assertion follows the existing separably-closed field cd=0 and finite-type torsion-cd statements, or the proper torsion bound. Properness and quasi-compactness, not a finite cd hypothesis on k, are what is required.

For the classical-closure node I read det-pe-classical-sheaves-modules, det-pe-classical-derived-weak-serre, the ringed-site Grothendieck-abelian statement, the termwise-derived-coproduct statement, the inverse-image clause of sk-thm-pe-direct-image-comparison and the finite-Tor comparison. Exact comparison and weak Serre closure give sums and triangle closure; exact ambient sums compute cohomology and good truncations termwise. The source is the blueprint's Transfer paragraph, with the reviewed relative repair as agent-written elaboration. This statement has its own objects, classicality definition, coefficient hypotheses and qcqs condition exactly where needed for Loc(Dctf).

For the truncation node I read Stacks Tag 095U, etale-cohomology.tex, lemma-cohomological-dimension-proper; Tag 08FI, sites-cohomology.tex, lemma-restrict-K-injective-to-open; Tag 0D6J, sites-cohomology.tex, lemma-modules-abelian-unbounded; and clause (2) of det-pe-unbounded-classical-truncation. The proper bound holds for ALL torsion sheaves and does not require the base Noetherian. The K-injective statement applies to any site object. Exact evaluation on affine weakly contractible objects identifies the cohomology-sheaf comparison with section cohomology of the inverse-image scheme. The section window then uses 2e in place of its bound. The source is the finite-window paragraph of the blueprint proof, not an assumption of unbounded comparison. The two deeper drafts below retain the details for its later worker.

For the coproduct node I read det-pe-bounded-continuity-direct-image and the exact-coproduct input, together with the common-lower-bound coproduct statement and the relative window argument in the source proof. A finite-subset filtered diagram has a common chosen lower bound after truncating all K_s at the SAME N. The window transfers this bounded-family comparison to an arbitrary family. The statement specifies the actual comparison and includes the empty family. It is stronger than the source-library finite-type-over-a-field theorem, so that declaration is recorded as related and not claimed as a closed attachment.

I reread delivery-errors B–E and checked the relevant failure modes: the four new files are statement-only, self-contained, with all notions named or defined; no proof sketch is embedded in a statement, all TeX escapes are single, every step's non-elementary inputs are cited, and no citation is borrowed from another node's proof. The global DAG and blueprint searches were repeated for classical cohomology, uniform truncation, geometric fibres and proper coproducts; the nearest blueprint ancestor is the item itself. The comparisons under Not duplicates record the closest existing statements. All four are real independent lemmas rather than elementary steps or relabelled target clauses. No new node depends on the parent, and all four are directly reached by it. The report, original statements, citations and full previous search log are retained in the sandbox. The actual LeanFinder/LeanSearch/Loogle/grep results were read and reused; invalid identifier patterns remain marked invalid rather than negative evidence. Working second phrasings give only infrastructure such as sigmaComparison and truncGE, not these geometric theorems.

Small cases: A=0, empty schemes and empty fibres yield zero complexes; e=0 still allows N=m-2. The empty coproduct is zero. Identity base changes and arbitrary non-flat base changes use exact constant-coefficient pullback. Non-Noetherian pro-étale neighborhoods are allowed by the relative vanishing statement. Disconnected weakly contractible objects use projectivity of the full representable, not a supposed choice of one cover member. An arbitrary unbounded family uses one N per output degree, never a bound depending on s. No finite cohomological dimension of the ground field is assumed.

## Preserved proof drafts for future stage-1 splits

These are retained mathematical work, not proof fields of the four unsplit nodes. The neighborhood-vanishing and evaluation statements are unsubmitted helper candidates for the future truncation split. The quotations in the retained new-node-citations.json correspond to these original drafts and require rechecking when reused. All six drafts have fewer than 3,000 proof characters each.

### lem-sfb-finite-classical-localizing

Statement: Fix a prime $\ell$, a finite commutative ring $A$ with $\ell^n1_A=0$ for some $n\geq1$, and a scheme $T$. Use ordinary constant-$A$ module sheaves and unbounded derived categories on the small étale and pro-étale sites [def-weil-pbc-derived-categories] [def-weil-pbc-proetale-modules]. Let $\mathcal C_T$ consist of complexes whose cohomology sheaves are classical, meaning they lie in the essential image of $\nu_T^*$ on étale module sheaves [sk-def-pe-classical-definition] [det-pe-classical-sheaves-modules]. Then $\mathcal C_T$ is full replete, triangulated, closed under all small ambient coproducts and under canonical truncations. Cohomology and canonical truncations commute with these coproducts. For every scheme map $r:W\to T$, constant-coefficient inverse image $r^*$ takes $\mathcal C_T$ into $\mathcal C_W$ and commutes with truncations [def-weil-pbc-proetale-operations]. If $T$ is quasi-compact and quasi-separated, then $\Loc(\Dctf(T,A))\subseteq\mathcal C_T$ [sk-def-sfb-constructible] [sk-def-localizing-closure].

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Transfer, classical cohomology subcategory; old split step 4.

1. Classical sheaves are closed under sums because the comparison in [det-pe-classical-sheaves-modules] is a left adjoint, and under kernels, cokernels and extensions by [det-pe-classical-derived-weak-serre]. Module sheaves are Grothendieck abelian by [lem-pur-ringed-site-grothendieck-abelian]. Thus sums are exact, being filtered colimits of finite sums. Termwise sums compute ambient derived coproducts by [lem-kun-grothendieck-derived-coproducts]. Exactness implies that kernels, cokernels and cohomology commute with sums. The good truncation formulas therefore commute with sums as well. The long exact cohomology sequence of a triangle, using the weak Serre property, proves triangle closure; shifts, repleteness and truncation closure follow directly from cohomology.

   Inputs: det-pe-classical-sheaves-modules, det-pe-classical-derived-weak-serre, lem-pur-ringed-site-grothendieck-abelian, lem-kun-grothendieck-derived-coproducts.

2. For a scheme map, [sk-thm-pe-direct-image-comparison] identifies $r^*\nu_T^*$ with $\nu_W^*r_{\mathrm{ét}}^*$; constant-coefficient inverse images are exact. Thus $r^*$ preserves classical cohomology and good truncations. A finite ring is Noetherian, so for qcqs $T$ the equivalence [det-pe-finite-tor-comparison-noetherian] makes every $\Dctf(T,A)$ object classical. The minimality in [sk-def-localizing-closure], applied to the subcategory just proved localizing, gives the asserted inclusion.

   Inputs: sk-thm-pe-direct-image-comparison, det-pe-finite-tor-comparison-noetherian, sk-def-localizing-closure.


### lem-sfb-finite-direct-image-weakly-contractible-evaluation

Statement: Let $A$ be a commutative ring, $f:X\to Y$ a scheme morphism, and $V\to Y$ an affine weakly contractible object of the small pro-étale site. Set $Z=X\times_YV$ with projection $r:Z\to X$ [def-weil-pbc-proetale-site] [sk-def-pe-weak-contractible] [def-pc-fibre-product]. Use ordinary constant-$A$ module sheaves, unbounded K-injective derived direct image and derived sections [sk-def-sfb-derived-categories] [def-weil-pbc-proetale-operations] [def-weil-pbc-sites-and-cohomology]. For every unbounded complex $K$ and integer $m$ there is a natural identification of $A$-modules
$$ (\mathcal H^mRf_*K)(V)\cong H^mR\Gamma(Z,r^*K). $$
Here $r^*$ is exact localized restriction, so $r^*\tau_{\geq N}K\cong\tau_{\geq N}r^*K$ [def-weil-pbc-ringed-derived-restriction]. No classicality, properness or boundedness of $K$ is assumed.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Transfer, neighborhood evaluation and restriction; old split steps 7–8.

1. Base change of a site object is a site object by [det-pe-topos-functoriality-inverse-image]. The sites and constant coefficients on $Z$ are the localization at $Z\to X$ by [lem-weil-proetale-weakly-etale-localization]. Clause (3) of [lem-sfb-proetale-object-inverse-image-restriction] identifies $r^*$ on module sheaves with restriction, including the scalar action. Its exact derived functor is termwise restriction by [def-weil-pbc-ringed-derived-restriction]; the kernels and cokernels in good truncations consequently give its truncation compatibility.

   Inputs: det-pe-topos-functoriality-inverse-image, lem-weil-proetale-weakly-etale-localization, lem-sfb-proetale-object-inverse-image-restriction, def-weil-pbc-ringed-derived-restriction.

2. Choose a K-injective representative $I$ of $K$ using [sk-def-sfb-derived-categories]. By [lem-pur-kinjective-restrict-localized], $I|_Z$ is K-injective and computes $R\Gamma(Z,r^*K)$. The direct-image formula of [det-pe-topos-functoriality-inverse-image] gives $(f_*I)(V)=\Gamma(Z,I|_Z)$ term by term. Evaluation at $V$ is exact by [det-proper-heart-continuity-sections], so it commutes with cohomology and yields the displayed identification. The same resolution functors and equality on morphisms give naturality in $K$, in particular for its canonical truncation maps.

   Inputs: sk-def-sfb-derived-categories, lem-pur-kinjective-restrict-localized, det-pe-topos-functoriality-inverse-image, det-proper-heart-continuity-sections.


### lem-sfb-finite-proper-classical-coproducts

Statement: Let $A$ be a finite commutative ring, and $f:X\to Y$ a proper scheme morphism. Assume $e\geq0$ bounds all fibre dimensions after every base change [def-weil-proper-morphism] [def-pc-base-change] [def-kun-topological-krull-dimension]. Work in ordinary constant-$A$ module sheaves and their unbounded pro-étale derived categories, with total K-injective $Rf_*$ [def-weil-pbc-proetale-modules] [sk-def-sfb-derived-categories]. For every small family $(K_s)_{s\in I}$ of complexes with classical cohomology, the canonical ambient coproduct comparison is invertible:
$$\bigoplus_{s\in I}Rf_*K_s\xrightarrow{\sim}Rf_*\bigl(\bigoplus_{s\in I}K_s\bigr).$$
Classical means [sk-def-pe-classical-definition], and the comparison is the map whose composite with the $s$-th coprojection is $Rf_*(\iota_s)$. The family may be empty; no common cohomological bound or cohomological-dimension assumption on a ground field is imposed.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Étale statements, direct sums from finite cohomological dimension; old split steps 11–12.

1. Exact coproducts and cohomology compatibility are supplied by [lem-sfb-finite-classical-localizing]. First take a small family of complexes $L_s$ with a common lower cohomological bound $N$. Replace each by its good lower truncation representative, which has zero terms below $N$. Index their finite direct sums by the filtered set of finite subsets of the indexing set. Their termwise colimit is $\bigoplus_sL_s$. By [det-pe-bounded-continuity-direct-image], for qcqs $p$ this filtered colimit commutes with every $\mathcal H^mRp_*$. The finite-subset complexes all vanish below the SAME $N$, as required by that statement. The unbounded derived functor is triangulated, in particular additive, by [lem-pc-right-derived-functor-triangulated]. Its additivity identifies the finite sums of images with the images of finite sums. Exact sums in the module category and [lem-kun-grothendieck-derived-coproducts] therefore identify the resulting map with
$$ \mathcal H^m(\bigoplus_sRp_*L_s)\xrightarrow{\sim}\mathcal H^mRp_*(\bigoplus_sL_s). $$
All identifications respect the coprojections, being induced by the finite-subset inclusions. In particular this is the canonical ambient coproduct comparison; the empty family gives zero.

   Inputs: det-pe-bounded-continuity-direct-image, lem-kun-grothendieck-derived-coproducts, lem-pc-right-derived-functor-triangulated, lem-sfb-finite-classical-localizing.

2. Fix $m$ and put $N=m-2e-2$. By [lem-sfb-finite-classical-localizing], sums remain classical, and both cohomology and good truncations commute with ambient sums. Apply [lem-sfb-finite-proper-classical-truncation] for $S=Y$ to each $K_s$ and their sum. Put $L_s=\tau_{\geq N}K_s$; these have a common lower bound, so the preceding step applies. Naturality of the canonical coproduct comparison gives a square in degree $m$: its top is the comparison for $K_s$, bottom that for $L_s$, and vertical maps are the summed and total truncation maps. Both vertical maps are invertible by the truncation lemma, and the bottom is invertible by the preceding step. Therefore the top is invertible for every $m$, proving the claim in the derived category. Each map respects coprojections, so the result concerns the specified comparison.

   Inputs: lem-sfb-finite-classical-localizing, lem-sfb-finite-proper-classical-truncation.


### lem-sfb-finite-proper-classical-neighborhood-vanishing

Statement: Let $A$ be a finite commutative ring annihilated by a positive integer, let $f:X\to Y$ be a proper scheme morphism, and let $e\geq0$ bound the dimensions of every fibre of every base change of $f$ [def-weil-proper-morphism] [def-pc-base-change] [def-kun-topological-krull-dimension]. For an affine weakly contractible object $V\to Y$ of the small pro-étale site, put $Z=X\times_YV$ and $h:Z\to V$ [def-weil-pbc-proetale-site] [sk-def-pe-weak-contractible] [def-pc-fibre-product]. For every classical constant-$A$ module sheaf $H$ on $Z_{\mathrm{proét}}$, one has $R^qh_*H=0$ and $H^q(Z_{\mathrm{proét}},H)=0$ for $q>2e$ [det-pe-classical-sheaves-modules] [def-weil-pbc-proetale-operations] [def-weil-pbc-sites-and-cohomology]. This concerns all classical $H$ on $Z$, without requiring descent from $X$ or Noetherianity of $V$.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Étale statements, uniform relative bound on proper pro-étale neighborhoods; old split steps 5–6.

1. By [lem-pc-proper-base-change], $h$ is proper. It is quasi-compact since it is finite type and quasi-separated by [lem-pc-separated-quasi-separated]. Write $H=\nu_Z^*F$ by [det-pe-classical-sheaves-modules]. The underlying étale abelian sheaf of $F$ is torsion, since the fixed annihilator of $A$ kills it. Apply [lem-kun-proper-torsion-cd-bound] with the assumed fibre bound $e$. Clause (2) of [lem-weil-pbc-exchange-forget-coefficients], using the identity base-change square for $h$, identifies the module and abelian derived direct images after forgetting scalars. Forgetting detects zero, so $R^qh_{\mathrm{ét},*}F=0$ for $q>2e$. The qcqs bounded-below comparison [sk-thm-pe-direct-image-comparison] applied to $F[0]$ gives $R^qh_*H=0$. None of these statements assumes $V$ Noetherian.

   Inputs: lem-pc-proper-base-change, lem-pc-separated-quasi-separated, det-pe-classical-sheaves-modules, lem-kun-proper-torsion-cd-bound, lem-weil-pbc-exchange-forget-coefficients, sk-thm-pe-direct-image-comparison.

2. The terminal object $V$ of $V_{\mathrm{proét}}$ is weakly contractible: by [lem-weil-proetale-weakly-etale-localization] and [lem-weil-pbc-localized-sheaves-over-representable], this topos is $\operatorname{Sh}(Y_{\mathrm{proét}})/h_V$. An epimorphism onto its terminal object is an epimorphism onto $h_V$ in the original topos, and splits by the defining projectivity of $h_V$ in [sk-def-pe-weak-contractible]. It is affine as well. Consequently $\Gamma(V,-)$ is exact by [det-proper-heart-continuity-sections]. The derived composition isomorphism [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] for $Z\xrightarrow{h}V\to\mathrm{point}$ identifies $R\Gamma(Z,H)$ with $R\Gamma(V,Rh_*H)$. Exactness of $\Gamma(V,-)$ and the preceding step give $H^q(Z,H)=0$ for every classical $H$ and $q>2e$. In particular this bound is for ALL classical sheaves on $Z$, not merely those pulled back from $X$.

   Inputs: lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-localized-sheaves-over-representable, sk-def-pe-weak-contractible, det-proper-heart-continuity-sections, lem-weil-pbc-ringed-topoi-derived-pushforward-composition.


### lem-sfb-finite-proper-classical-truncation

Statement: Let $A$ be a finite commutative ring and $f:X\to Y$ a proper morphism of schemes. Suppose $e\geq0$ bounds the dimensions of all fibres after every base change [def-weil-proper-morphism] [def-pc-base-change] [def-kun-topological-krull-dimension]. For any scheme map $S\to Y$, write $f_S:X_S=X\times_YS\to S$. In the ordinary constant-$A$ unbounded pro-étale derived categories, let $J\in D(X_S,A)$ have classical cohomology [def-weil-pbc-proetale-modules] [sk-def-pe-classical-definition]. For integers $m,N$ with $N<m-2e-1$, the canonical truncation map induces a natural isomorphism of sheaves on $S_{\mathrm{proét}}$
$$\mathcal H^mRf_{S,*}J\xrightarrow{\sim}\mathcal H^mRf_{S,*}\tau_{\geq N}J.$$
Use total K-injective direct image and good truncations [sk-def-sfb-derived-categories] [def-kun-truncations]. The same $e$ and inequality work for every $S$.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Étale statements, both sides depend on a bounded-below truncation; old split steps 9–10.

1. For an affine weakly contractible $W\to S$, put $Z=X_S\times_SW=X\times_YW$. The hypothesis on all base changes passes to $f_S$. Properness passes to it by [lem-pc-proper-base-change]. Apply [lem-sfb-finite-proper-classical-neighborhood-vanishing] to $f_S,W$: every classical sheaf on $Z$ has cohomology zero above $2e$. The restriction of $J$ to $Z$ is classical by [lem-sfb-finite-classical-localizing].

   Inputs: lem-pc-proper-base-change, lem-sfb-finite-proper-classical-neighborhood-vanishing, lem-sfb-finite-classical-localizing.

2. By [lem-sfb-finite-direct-image-weakly-contractible-evaluation], evaluation at $W$ of the asserted truncation map is precisely the canonical map $H^mR\Gamma(Z,J|_Z)\to H^mR\Gamma(Z,\tau_{\geq N}(J|_Z))$. Clause (2) of [det-pe-unbounded-classical-truncation] makes it invertible for $N<m-2e-1$, since the preceding step bounds ALL classical sheaves on $Z$. Clause (3) of [det-pe-sections-conservative] now gives the sheaf isomorphism. These comparisons apply to the truncation map itself, so are natural in $J$.

   Inputs: lem-sfb-finite-direct-image-weakly-contractible-evaluation, det-pe-unbounded-classical-truncation, det-pe-sections-conservative.


### lem-sfb-finite-proper-geometric-cd-bound

Statement: Let $f:X\to Y$ be a proper morphism of schemes with $Y$ quasi-compact [def-pc-scheme] [def-weil-proper-morphism] [def-weil-pbc-quasi-compact-scheme]. There is an integer $e\geq0$ such that every fibre of every base change $f_S:X\times_Y S\to S$ has Krull dimension at most $e$ [def-pc-base-change] [def-pc-scheme-fibre] [def-kun-topological-krull-dimension]. Moreover, for every geometric point $\bar y:\operatorname{Spec}\Omega\to Y$, with $\Omega$ separably closed, and every torsion abelian étale sheaf $F$ on $X_{\bar y}$, one has $H^q(X_{\bar y},F)=0$ for $q>2e$ [def-weil-geometric-point] [def-weil-pbc-torsion-etale-sheaf] [def-weil-pbc-etale-cohomology]. Empty fibres are allowed.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md, Étale statements, uniform cohomological bound; old split step 2 before the finite-Tor application.

1. Properness includes finite type. Apply [lem-fin-finite-type-fibre-dimension-bound] to obtain $e\geq0$ bounding all $X_y$. For any base change and point $x'$ of a fibre, [lem-sc-fibre-dimension-after-base-change] identifies its local dimension with that at the image $x$ in $X_y$. Taking suprema by [lem-weil-pbc-dimension-supremum-local-dimensions] bounds every base-changed fibre by the same $e$.

   Inputs: lem-fin-finite-type-fibre-dimension-bound, lem-sc-fibre-dimension-after-base-change, lem-weil-pbc-dimension-supremum-local-dimensions.

2. A geometric fibre is proper over $\Omega$ by [lem-pc-proper-base-change], hence finite type. By [lem-kun-03qu-sep-closed], $\Omega$ has torsion cohomological dimension zero. For a nonempty fibre of dimension $r\leq e$, apply [thm-sc-finite-type-torsion-cd] with $c=0$: its torsion cohomology vanishes above $2r\leq2e$. The empty fibre has zero sections and zero cohomology in every degree.

   Inputs: lem-pc-proper-base-change, lem-kun-03qu-sep-closed, thm-sc-finite-type-torsion-cd.

## Validation

The required initial dry run reproduced the six new-node status errors. After this repair the remote dry run exited 0 and printed `OK (not pushed) deliver/Q60/det-ctf-finite-proper-localizing at d96e626c8c4: preflight passed`. The final report also preserves all six proof drafts from the original JSON snapshots; the delivery command will run its checks again on the final package. All parent citation quotes are verbatim, the statement is identical to the live item, every direct dependency exists, and proof_deps equals the union of step uses. No Lean writing or compilation, repository git command, launcher edit, or unauthorized agent was used.
