# Q23 stage-1 repair: strict finite pullback tower comparison

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-finite-pullback-strict-tower-comparison.json`: statement unchanged; five assembly/localization/shift steps, 2299 characters in total.
- `lem-a1-finite-reduction-tower-resolving-model`: statement, unsplit; Mathlib no match. Extracts old steps 1–2 (1776 characters of argument).
- `lem-a1-pulled-koszul-tower-chain-comparison`: statement, unsplit; Mathlib no match. Extracts old steps 3–5 (1636 characters of argument).
- `lem-a1-balanced-finite-tower-generator-comparison`: statement, unsplit; Mathlib no match. Extracts old steps 6–7 (2085 characters of argument).
- `citations.json`: verbatim statement quotations for every use of every new parent step.
- `searches.jsonl`: actual msearch.py results retained for the three new nodes. The original item's existing search records are retained unchanged.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact blueprint tag, the declaration name, and the tower/resolving/Koszul concepts. There is no qualifying project declaration. The existing `lean/Sheaf/Paper/FinitePullbackStrictTowerComparison.lean:428` theorem has `sorry` at line 432; its docstring contains the old nine-step proof. No attachment is claimed for definitions or partial ordinary comparisons.

## WANTED

None. All mathematical sources used here are present locally. No SGA source is used.

## What was wrong and what changed

This repairs the human's batch5 re-split return, rather than offering an unchanged re-push. At start the sandbox held only dispatcher brief markers, with no item, old report or searches. I copied the live item, preserving its statement, all original searches, citations inside the original proof, source, blueprint metadata and Lean metadata. Thus there was no separate retained head to rebase. The delivery tool rebases the permitted stage-1 fields on current origin; I run no git commands.

The parent carried 7676 characters of proof work. Three independent statement-only obligations now distribute its first seven steps with comparable argument sizes. The first concerns the resolving/counit models, the second concerns the ordinary Koszul isomorphism and the correct target augmentation, and the third concerns balanced coefficient transport and fixed finite generators. None asserts the parent's derived natural isomorphism with all shifts. Each introduces its own schemes, rings, coefficient maps, complexes, transitions and maps. All have empty proof and proof_deps, status unsplit, no proof sketch inside their statements. Their argument material is retained below in this report for their future workers. The parent retains and spells out the actual localization and integer-shift arguments (old steps 8–9).

The statement was not disputed or changed. In particular the completed coefficient sheaf is never silently replaced by the discrete constant valuation ring; only each finite constant coefficient structural map is an isomorphism. Ordinary completed module pullback need not be exact, and its structural ring map need not be invertible. There are no completeness, boundedness or constructibility assumptions.

## What could not be finished

Nothing in the authorized stage-1 repair remains; the new nodes are intentionally unsplit for parallel work, as the return requires. No Lean was written and no compiler, Lake, local preflight, check_dag or review_split was run.

## Blueprint and duplicate searches

I read GOAL.md, the stage-1 brief, stage document, worker role, SETUP's three blueprint levels, the chapter/unit records and delivery-errors B–E (including the merged copy). The blueprint route remains the finite-map/stalk restriction in the first paragraph of lem-a1-finite-map-purity, via the three pre-existing ancestor nodes. In the current main-20261015 snapshot I read that lemma's statement. The inherited detailed strict-completed comparison is an agent refinement, not a claim that the blueprint itself states its normalization.

Before creating any nodes I ran `tools/blueprint_refs.py ancestor` for the item and whole-blueprint searches for `strict tower`, `localization shift`, `K-flat`, `scalar-association`, `Koszul`, `finite pullback`, `Koszul tower` and `resolving`. I searched all DAG nodes for the source tags and key concepts, and read the existing principal Koszul replacement, diagram K-flat replacement, cochain coherence, derived tensor descent, pulled-reduction comparison, strict quotient computation, tensor additive constraints, scalar counit, transition-generator and completed coefficient tensor-normalization statements. Definitions of the very constructions are not existence theorems. The extracted nodes are not elementary two-line facts: their retained proofs invoke several substantive resolution, quasi-isomorphism invariance and ringed pullback results and verify strict generator equalities. The explicit human re-split instruction requires these former arguments to be queued separately.

Each new node received two distinct LeanFinder queries, one Loogle query, one source grep and one LeanSearch query through the required msearch.py command, and the actual log was used to populate the JSON. All services answered. I read the result signatures. Relevant local candidates were checked at Mathlib/CategoryTheory/Functor/Derived/LeftDerived.lean:193–205 (a derived functor only after its existence assumption), ModuleCat/Sheaf/PullbackContinuous.lean:106–111 and 167–174 (ordinary sheafification and composition), and PullbackFree.lean:118–138 (free sheaf pullback). The semantic results also contain ordinary module tensor quotients and Tor/flatness. None gives these specified unbounded good-complex strict quotient/Koszul models or their fixed finite-generator normalization. All new nodes remain unsplit, with no Mathlib match.

## Review by Q23

I read the Stacks sources themselves: proetale.tex Tag 099N, lemma-pushforward-Noetherian-case, especially (5) and its proof, as the parent's context; derived.tex Tag 06XN, lemma-find-existence-computes, specifically its left-derived dual; sites-cohomology.tex Tag 06YS, lemma-K-flat-resolution, Tag 0G7D, lemma-factor-through-K-flat, and Tag 0G7E, lemma-pullback-K-flat; sites-modules.tex Tag 03EL, lemma-tensor-product-pullback with its balanced adjunction proof; and more-algebra.tex Tag 0FNH, item-shift-tensor, with its sign convention. For each extraction these support the precise source field: 06XN for resolving models, 0G7E for the Koszul/pulled-flat complexes, and 03EL for balanced comparison. The strict-tower, normalized-generator refinements are agent arguments, retained verbatim below; I do not attribute all those details to the general Stacks statements.

For new parent step 1 I opened the first new statement: it supplies exactly B_g with universal counit beta invertible on good complexes and the canonical chi from the strict Koszul augmentation. Its small indexing category is explicitly N-positive opposite, and every input is flat-term K-flat. The retained proof below verifies both resolving-class hypotheses using kflat-resolution, derived-change-of-rings (1), constant-exact and levelwise-abelian, not the definition of K-flatness alone.

For step 2 I opened the second statement: it asserts goodness of GP and every G(P tensor Q_n), the ordinary strict theta with its two generator formulas, and the target-ring augmentation as a quasi-isomorphism of strict towers. Ringed-topos pullback 0G7E applies to any coefficient ring map; there is no false assertion that ordinary G preserves all quasi-isomorphisms. The source Q_n complexes have flat terms and are K-flat by the already-existing principal replacement statement; the target augmentation is applied to GP only after these hypotheses are obtained.

For step 3 the third statement gives lambda and C, both whole-tower chain isomorphisms, and explicitly the equality lambda a_GP theta = C G(a_P). I compared its finite-generator formula with the actual KoszulNormalization and BalancedNormalization in FinitePullbackStrictTowerComparison.lean:185–236, and HasCompletedReductionFiniteEvaluationNormalization in CompletedPullbackReduction.lean:764–782. Degree zero is the specified projection, degree minus one is zero. The coefficient square is pi'_n c_g = c_(g,n) g^-1 pi_n. Its balancing makes the two insertion-of-one inverses legitimate, including the zero ring. Quotient transition compatibility is the actual equation q'(pi'_(n+1)(b)a) = pi'_n(b)q'(a), not an inference from equality of arbitrary derived evaluations. The normalized equality is a chain-map equality before localization.

Step 4 uses the chain-map naturality and representative computations stated by all three new nodes and the existing site's tensor-descent statement. I opened that statement: it explicitly gives W^-1 P equivalent to D(R), with P the flat-term K-flat homotopy subcategory. This is sufficient for the single-variable descent here; no unsupported appeal to fully-faithful Yoneda or objectwise derived evaluations occurs. Inverting the naturality square at a quasi-isomorphism gives the square for its inverse; essential surjectivity gives invertibility everywhere. All formulas remain R'-linear.

Step 5 uses the existing total-tensor integer-shifts statement: its first-variable comparison is unsigned for every integer. I checked the differential equation (-1)^r(-1)^(p+r)=(-1)^p, including negative integers. The definitions of strict reduction and derived tower pullback, together with the resolving-class theorem, fix the termwise/counit comparisons used in the equality; this is not an arbitrary alternative shift structure. Flat terms are merely reindexed and K-flatness is preserved by shifting tensor tests. The localization equivalence again extends the equality to all derived inputs. The cites in citations.json are copied literally from the opened statements, and proof_deps is the union of uses.

I checked small cases separately: g identity gives the ordinary tensor/unit comparisons; P=0 gives zero towers; T' empty gives zero module sheaves and the unique zero-ring maps; n=1 has Q=[R --t--> R] and the quotient A/t; the adjacent transition obeys t^n t=t^(n+1); r=0 is identity and r=1,-1 have the displayed differential sign. None requires the completed structural map to be invertible. The completed ring and finite sheaves retain their specified projections. The only corrections were distributing the work, making the two Koszul generator and balanced normalization obligations explicit in self-contained statements, and keeping the source/target augmentation distinction visible. There is no mathematical route change.

## Supplement to the extracted balanced comparison

The extra map $C_P:G(F(P))\to B_g^0(P)$ also has the asserted inverse. This does not follow from an arbitrary commuting ring square alone. The existing principal-Koszul replacement statement, specialized to $P=R_W[0]$, gives $S_{W,n}=R_W/t^nR_W$ through the specified projection for both schemes. Exact inverse image gives $g^{-1}S_{T,n}=g^{-1}R_T/(t^n)$. Ordinary ringed module pullback is a left adjoint and hence right exact, so $G(S_{T,n})=R_{T'}/t^nR_{T'}=S_{T',n}$, with the comparison induced by the very same projection square. Apply ordinary tensor coherence to obtain $G(P\otimes S_{T,n})\cong GP\otimes S_{T',n}$, and follow it by $\lambda_{P,n}$ to obtain $C_{P,n}$. Its formula on the quotient-unit generator is exactly $\pi_{T',n}(b)$; inverse maps can equivalently be checked locally by lifting finite coefficients along the surjective projection $\pi_{T',n}$. These comparisons preserve all quotient transitions because their projections do. This supplies the quotient-module justification for the $C_n$ used in old step 7 and makes clear why no invertibility of the completed ring map is used.

## Preservation of every old argument

The following is the live returned nine-step proof, verbatim, with each old cited node and source retained. Steps 1–2 become the first new obligation, 3–5 the second, 6–7 the third. Steps 8–9 remain the parent's explicit localization/shift proof. These paragraphs are report material for future workers, not proof steps attached to the unsplit new nodes.

### Old step 1

Let $\mathcal P_T$ be the flat-term K-flat complexes over $R_T$. On all complexes define $B_g^0(P)_n=\operatorname{Res}_n g_n^*(P\otimes_{R_T}S_{T,n})$, using the quotient transitions and their compatible coefficient maps. This additive construction commutes with shifts and mapping-cone complexes: it acts on each differential and each of the two summands of a cone. A quasi-isomorphism between objects of $\mathcal P_T$ remains a quasi-isomorphism after tensoring with each $S_{T,n}$ by change of rings, and then after $g_n^*$ by finite-coefficient exactness. Restriction of scalars leaves the underlying abelian sheaves unchanged. Exactness in towers is levelwise, so $B_g^0$ takes these quasi-isomorphisms to quasi-isomorphisms of tower complexes. Flat-term K-flat resolutions exist for every complex. The resolving-class theorem therefore supplies an everywhere defined functor $B_g:D(R_T)\to D(\operatorname{Tow}_{R_{T'}})$, with its canonical computation isomorphism $B_g(QP)\cong Q B_g^0(P)$ for $P\in\mathcal P_T$.

Uses: lem-pc-kflat-resolution, lem-pur-derived-change-of-rings, prop-weil-pbc-proetale-constant-exact, lem-weil-tower-category-levelwise-abelian, lem-pur-left-derived-from-kflat-class.

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YS (lemma-K-flat-resolution), 06YT/06YY (change-of-rings quasi-isomorphism invariance), and derived.tex 06XN (lemma-find-existence-computes); finite exactness as cited.

### Old step 2

For $P\in\mathcal P_T$ put $F(P)=(P\otimes S_{T,n})_n$ and $H(P)=(P\otimes Q_{T,n})_n$. The principal-Koszul strict replacement lemma gives a natural strict quasi-isomorphism $a_P:H(P)\to F(P)$ whose source levels are K-flat with flat terms. Its source transitions are $1_P\otimes(t,1)$ and its target transitions are the actual quotients. Thus $QF(P)$ is the specified reduction tower $(QP)_\bullet$. By the definition of $V_g$ and its diagram resolving class, $GH(P)$ computes $V_g((QP)_\bullet)$: use $V_g(Qa_P)^{-1}$ followed by the computation isomorphism at $H(P)$. These identifications are natural for chain maps $P\to P'$. The index category is the small category $\mathbf N_{\geq1}^{\mathrm{op}}$, so the diagram replacement statement applies.

Uses: lem-a1-principal-koszul-strict-replacement, def-weil-pbc-adic-coefficient-datum, def-weil-pbc-completed-pullback, lem-weil-pbc-diagram-kflat-replacements.

Source: literature/stacks-project/sites-cohomology.tex, Tag 06YS and the strict principal-Koszul replacement; Tag 06YY and the small-diagram construction specified in completed pullback.

### Old step 3

Apply preservation of K-flat complexes with flat terms under ringed-topos pullback to $(g,c_g)$, first to $P$ and then to each $P\otimes Q_{T,n}$ supplied in Step 2. It follows that $GP$ and every $G(P\otimes Q_{T,n})$ are K-flat with flat terms. The morphism of topoi is presented by the chosen small pro-etale sites, and $c_g:g^{-1}R_T\to R_{T'}$ is a map of commutative ring sheaves, precisely the hypotheses of that preservation theorem. This argument imposes no flatness or invertibility condition on $c_g$.

Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-a1-principal-koszul-strict-replacement, def-weil-pbc-completed-pullback.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0G7E (lemma-pullback-K-flat), as included in the ringed-topoi tensor/pullback statement.

### Old step 4

The ordinary cochain tensor comparison gives $G(P\otimes Q_{T,n})\cong GP\otimes GQ_{T,n}$. Under the action unitor $GR_T\cong R_{T'}$, the map $G(t^n)$ is multiplication by $t^n$: the components defining $c_g$ preserve the constant scalar $t$. Consequently $GQ_{T,n}\cong Q_{T',n}$. These isomorphisms identify $G(t,1)$ with $(t,1)$ and hence give the first isomorphism of strict towers in the statement, not just separate isomorphisms of derived evaluations. The cochain comparison is natural and respects action unitors; no quasi-isomorphism preservation is needed for this ordinary chain isomorphism.

Uses: lem-pur-cochain-pullback-tensor-coherence, def-weil-pbc-completed-pullback.

Source: literature/stacks-project/sites-cohomology.tex, Tags 03EL (sites-modules, lemma-tensor-product-pullback) and 07A4 (lemma-pullback-tensor-product); cochain comparison and action unitors.

### Old step 5

Apply the principal-Koszul strict replacement lemma on $T'$ to the complex $GP$, whose flat-term K-flat hypotheses were checked in Step 3. It gives the strict quotient augmentation $(GP\otimes Q_{T',n})_n\to(GP\otimes S_{T',n})_n$, and every component is a quasi-isomorphism. Levelwise exactness in the tower category makes this a quasi-isomorphism of tower complexes. This proves the assertion about the middle arrow; it does not result from applying the possibly nonexact functor $G$ to an arbitrary quasi-isomorphism.

Uses: lem-a1-principal-koszul-strict-replacement, lem-weil-tower-category-levelwise-abelian.

Source: literature/stacks-project/sites-cohomology.tex, Principal-Koszul augmentation over the target completed coefficient sheaf; Tag 02MZ (homology, lemma-inverse-systems-abelian).

### Old step 6

Put $R=R_T$, $R'=R_{T'}$, $S_n=S_{T,n}$ and $S'_n=S_{T',n}$. Finite constant coefficient transport identifies $g^{-1}S_n$ with $S'_n$. The coefficient square commutes because $\pi'_n c_g$ is, by definition, $g^{-1}R\to g^{-1}S_n\to S'_n$. Apply the cochain scalar-association comparison to $R\to S_n$, $R'\to S'_n$ and this square. Both $GP\otimes_{R'}S'_n$ and $g_n^*(P\otimes_R S_n)$ identify with $g^{-1}P\otimes_{g^{-1}R}S'_n$. On the first the identification is $(x\otimes b)\otimes a\mapsto x\otimes\pi'_n(b)a$, with inverse $x\otimes a\mapsto(x\otimes1)\otimes a$. On the second it is $(x\otimes z)\otimes a\mapsto x\otimes c_{g,n}(z)a$, with inverse inserting $1$ in the $g^{-1}S_n$ factor. The commuting coefficient square makes these formulas balanced; the two composites are identities by the tensor relations. The formulas commute with restrictions and degreewise differentials and therefore induce inverse maps of sheaf tensor complexes. Composing the first identification with the inverse of the second gives the last isomorphism in the statement.

Uses: prop-weil-pbc-proetale-constant-ring-map, lem-pur-cochain-pullback-tensor-coherence, def-pur-sheaf-tensor-product, def-weil-pbc-completed-pullback.

Source: literature/stacks-project/sites-cohomology.tex, Tags 03EK (sites-modules, section-tensor-product) and 03EL; scalar-association map kappa in the cochain coherence statement.

### Old step 7

All formulas of Step 6 commute with quotient transitions. For example reducing $(x\otimes b)\otimes a$ from level $n+1$ to $n$ gives $x\otimes q'_{n+1,n}(\pi'_{n+1}(b)a)=x\otimes\pi'_n(b)q'_{n+1,n}(a)$ along either path. The corresponding formula on the finite pullback side follows from $q'c_{g,n+1}=c_{g,n}g^{-1}q$. Together with Step 4 this proves strictness of the entire displayed zigzag. Let $C_n:G(P\otimes S_n)\cong B_g^0(P)_n$ be the same scalar-association map. The zigzag at level $n$ is also $C_nG(a_{P,n})$: on a degree-zero Koszul generator the augmentation is the quotient $R\to S_n$, and on the degree-minus-one generator it is zero. On the inverse-image quotient-unit generator $b\otimes g^{-1}(x\otimes1)$, $C_n$ gives the finite pullback generator with scalar $\pi'_n(b)$. This is exactly the pure-tensor and K-flat representative normalization of the fixed interface. Hence evaluation of our zigzag is the specified finite comparison, rather than an arbitrary isomorphism with the same source and target.

Uses: lem-pur-cochain-pullback-tensor-coherence, def-weil-pbc-completed-pullback, def-a1-integral-completed-pullback-interfaces.

Source: literature/stacks-project/sites-cohomology.tex, Tag 03EL and the quotient scalar-association formulas; the fixed interface definitions, read with CompletedPullbackReduction.lean, ordinary and derived generator normalizations.

### Old step 8

Every arrow constructed in Steps 2 and 4--7 is natural in a chain map $f:P\to P'$: its local tensor formulas replace $x$ by $g^{-1}f(x)$ on both paths. The augmentation is $1\otimes\epsilon_n$, so it has the same property. Thus they define a natural isomorphism between the restrictions of $V_g\circ(-)_\bullet$ and $B_g$ to the homotopy category of flat-term K-flat complexes. These functors already exist on derived categories by Step 1 and the specified tower definitions. The localization equivalence $W_T^{-1}\mathcal P_T\simeq D(R_T)$ in the site tensor-descent statement extends this natural isomorphism uniquely. Explicitly the chain-map naturality equation for a quasi-isomorphism $s$ can be multiplied by the two inverse images of $s$ to give naturality for $s^{-1}$; the equivalence says these localized maps give all derived morphisms. Every object has a representative in $\mathcal P_T$, so all components are invertible. This defines $b_g$, proves naturality for all derived morphisms, and proves independence of representatives. Each map is $R_{T'}$-linear by its balanced formula.

Uses: lem-weil-pbc-site-derived-tensor-descent, lem-pur-cochain-pullback-tensor-coherence, lem-a1-principal-koszul-strict-replacement.

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YS and 0G7D (lemma-factor-through-K-flat), via the flat-term K-flat localization equivalence; the displayed natural cochain maps.

### Old step 9

Fix $r\in\mathbf Z$. The tensor comparison extracting a shift from the first argument is unsigned: $(P[r]\otimes Q_{T,n})\cong(P\otimes Q_{T,n})[r]$ sends each tensor to itself in the reindexed summand. For $x$ of degree $p$ in $P[r]$, its differential is $(-1)^r dx\otimes y+(-1)^p x\otimes dy$ on both sides, since the shifted total differential has second coefficient $(-1)^r(-1)^{p+r}=(-1)^p$. The same comparison applies to $S_n[0]$. Termwise $G$ and $g_n^*$ commute with shifts by the identity on terms. The balanced maps, the quotient augmentation and the transitions have degree zero, so the resulting shift squares for every arrow of the zigzag commute already as chain maps. The canonical resolving-class shift comparisons for reduction and $V_g$ are computed by these termwise shifts; flat-term K-flat classes are stable under them. Thus on $\mathcal P_T$ the resulting equality is $s^B_{K,r}b_{g,K[r]}=b_{g,K}[r]s^V_{K,r}$. The localization equivalence of Step 8 extends this equality to every $K$. This proves precisely the asserted shift compatibility for all integers.

Uses: lem-weil-pbc-total-tensor-integer-shifts, lem-pur-left-derived-from-kflat-class, lem-weil-pbc-site-derived-tensor-descent.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FNH (more-algebra, item-shift-tensor); canonical exact left-derived comparisons from derived.tex 06XN/05SE.

## Not duplicates

lem-a1-finite-reduction-tower-resolving-model vs lem-sbc-scalar-extension-counit-properties: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns K-flat computation and triangulatedness of a specified scalar-extension counit; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-sbc-derived-coefficient-map-descent: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Descent of a termwise coefficient map through a resolving counit; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-sf-right-derived-from-adapted-complexes: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Right derived functor from a class of adapted complexes; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs def-zl-derived-change-of-rings-model: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Canonical derived change-of-rings cochain model; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-trf-bounded-above-acyclic-derived-computation: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Bounded above acyclic complexes compute a left derived functor; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs def-trf-singleton-site-operations: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Punctual ringed-site operations and normalized comparison predicates; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-pc-ringed-space-tensor-pullback-absolute: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Absolute K-flat derived comparison for concrete tensor pullback; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs q3-ringed-space-tensor-pullback-absolute-postcomposition: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Absoluteness of tensor pullback derived comparison; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-pc-kflat-scalar-extension-counit: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Universal scalar extension counit on K-flat module complexes; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs q3-ringed-space-tensor-pullback-left-derived: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns K-flat derived comparison for concrete tensor pullback; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs def-sfb-derived-change-of-rings-cochain-model: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Derived change-of-rings cochain presentation; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-sc-global-tensor-pullback-derived-data: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Absolute derived tensor comparison after point evaluation; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-a1-finite-pullback-strict-tower-comparison: the new node is only one of three separate chain/resolving arguments extracted by the human re-split request; it has no all-derived natural comparison b_g with integer shifts, which is the parent conclusion.

lem-a1-finite-reduction-tower-resolving-model vs def-a1-integral-completed-tower-pullback-universes: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Integral completed strict-tower interfaces at independent universes; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-weil-pbc-ringed-derived-adjunction-independent-universes: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Derived module inverse image is left adjoint to a supplied derived direct image; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-weil-pbc-completed-constant-derived-tensor-tower: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Universal derived tensor tower from K-flat resolutions; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-pur-coefficient-tensor-derived-unit: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Universal derived comparison for the identity coefficient tensor; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-cbc-strict-quotient-pullback-computation: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Resolved strict quotient pullback with its specified augmentation; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-pur-resolving-class-derived-adjunction: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Normalized derived adjunction from a resolving class; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-cbc-cochain-augmentation-descent: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Descent of an augmentation through its universal cochain counit; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-pur-derived-change-of-rings: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Derived change of rings along a morphism of sheaves of rings, computed by K-flat resolutions; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-cbc-derived-constant-tower-normalization: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Unique representative normalization of the derived constant-tower comparison; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-pur-resolving-class-essential-constancy: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Resolving classes make denominator pro-diagrams essentially constant; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-pur-left-derived-from-kflat-class: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Left derived functor on the derived category computed by a resolving class; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-cbc-derived-tower-evaluation-normalization: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Unique representative normalization of derived tower evaluation; it does not state that entire specific assertion.

lem-a1-finite-reduction-tower-resolving-model vs lem-cbc-cochain-derived-adjunction: the new node establishes the combined strict finite-reduction functor B_g and its good-representative counit plus the particular principal-Koszul chi computation of V_g, whereas the existing statement concerns Normalized derived adjunction for a specified cochain left derived pair; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sf-open-operation-models: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Open operation comparisons with fixed tensor models and right square; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sf-open-pullback-support: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Derived pullback preserves open support; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sf-scalar-pullback-composition: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Composition coherence of normalized scalar/pullback comparisons; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pod-point-extension-kflat: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns K-flatness of the point extension of a flat-term module complex; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-coef-semilinear-system-models: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Generic strict semilinear system constructions and representative normalization; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sf-canonical-open-restriction-model: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Canonical open restriction on augmented quotient models; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-etale-native-tensor-pullback: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Native unbounded derived tensor commutes with etale inverse image; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sf-boundary-bounded-tensor-comparison: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Bounded tensor preparation for the boundary direct-image comparison; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sf-open-restriction-completeness: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Completeness and the actual completion unit after ordinary open restriction; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-sfb-internal-derived-scalar-comparisons: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Normalized internal derived scalar comparison interface; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sfb-constant-module-kflat: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Constant realization preserves flat-term K-flat complexes; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sfb-constant-realization-derived-scalar-extension: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Derived constant realization commutes with derived scalar extension; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-sfb-integral-quotient-projection-map: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Integral quotient internal projection arrow; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sfb-ringed-site-point-kflat-resolution: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns K-flat resolution with K-flat stalk; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sfb-successive-derived-quotient-normalization: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Successive derived scalar extensions agree with direct quotient extension; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sfb-flat-term-kflat-functor: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Flat-preserving colimit functors preserve flat-term K-flat complexes; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-sfb-integral-quotient-coefficients: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Canonical integral uniformizer quotient coefficient maps; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sfb-kflat-scalar-comparison-normalization: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Representative and adjunction normalization of scalar pullback comparison; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-sfb-scalar-extension-kflat: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Scalar extension preserves all K-flat sheaf complexes; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-per-proetale-scalar-slice-comparison: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Normalized scalar extension comparison on a pro-etale slice; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-a1-finite-pullback-strict-tower-comparison: the new node is only one of three separate chain/resolving arguments extracted by the human re-split request; it has no all-derived natural comparison b_g with integer shifts, which is the parent conclusion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-pullback-resolving-computation: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Derived pullback computes on resolving complexes with independent universes; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Derived tensor comparison for arbitrary ringed topoi; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-cochain-pullback-tensor-shift: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns The prescribed cochain pullback tensor comparison commutes with both signed shifts; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-ringed-pullback-preserves-kflat: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Ringed pullback kflat; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-pulled-reduction-normalization-comparison: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Successive quotient normalizations under the pulled reduction comparison; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-ringed-topos-kflat-pullback: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Ringed-topos pullback preserves flat-term K-flat complexes; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns A flat resolution whose ringed-topos pullback is K-flat; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-flat-coefficient-reduction-adjunct: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Finite scalar comparison preserves derived reduction adjuncts; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Derived pullback computes K-flat tensor representatives; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Tensor pullback adjoint to a supplied ringed-topos module direct image; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Canonical tensor comparison unit uniqueness; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-constant-derived-normalization-universal: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Constant derived realization preserves universal coefficient arrows; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-ringed-topos-acyclic-kflat-pullback: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Ringed-topos pullback in the acyclic K-flat case; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-completed-adic-koszul-kflat: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns K-flatness of the actual completed exterior Koszul complexes; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-pbc-successive-derived-scalar-normalization-data: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Normalized presentation data for successive derived scalar extensions; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-diagram-kflat-replacements: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Objectwise K-flat replacements in strict diagram categories; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Canonical tensor comparison unit existence; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Common quotient reduction of the geometric scalar comparison; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-normalized-derived-isomorphism-transport: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Universal normalization and evaluation of source-site local Isom sheaves; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-pbc-derived-scalar-extension-local-systems: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Coherent localized derived scalar extension and comparison; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-quotient-expression-kflat-normalization: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Simultaneous K-flat normalization of strict quotient expressions; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-normalized-scalar-comparison-realization: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Normalized realization of scalar comparisons on quotient systems; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-pur-derived-constant-pullback-comparison: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Canonical derived constant-sheaf pullback comparison; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-integral-operations-well-defined: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-etale-scalar-pullback-existence: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Existence of normalized derived scalar/pullback comparison; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-pur-strict-quotient-expressions: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Strict quotient expressions with actual horizontal transitions; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-pur-etale-scalar-pullback-iso: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Canonical derived scalar and pullback isomorphism; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-external-rhom-evaluation-naturality: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Four-variance naturality of the external evaluation transpose; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-pur-change-of-rings-complex: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Termwise change of rings of a cochain complex; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-integral-ambient-operation-models: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Ambient completion presentations for integral pullback and tensor; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-etale-scalar-flat-kflat-comparison: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Native flat-term K-flat étale complexes in scalar coordinates; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-scalar-tensor-pullback-normalization: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Scalar/tensor pullback normalization on a K-flat representative; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-exc-proetale-constant-support-projection: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Constant-coefficient projection for compact support; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-cbc-completed-open-kflat: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Completed-coefficient open extension preserves flat-term K-flat models; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-kflat-change-of-rings: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Change of rings preserves K-flat complexes with flat terms; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs def-pur-open-coefficient-normalizations: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Exact-pullback and open-unit coefficient normalizations; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-etale-scalar-pullback-uniqueness: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Uniqueness of normalized derived scalar/pullback comparison; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-weil-point-derived-tensor-tower-coherence: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Ordinary derived scalar associators and point sections-tensor tower coherence; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-kflat-change-of-rings-all-independent: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Change of rings preserves all K-flat complexes with independent coefficient universe; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-varying-ring-tensor-comparison: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Normalized tensor comparison for one varying-ring inverse image; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-kflat-change-of-rings-independent: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Change of rings preserves K-flat complexes with flat terms in independent universes; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pur-coefficient-pullback-comparison: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Canonical inverse-image coefficient comparison; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-fix-tensor-pullback-square: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Tensor inverse-image comparisons commute around an open square; it does not state that entire specific assertion.

lem-a1-pulled-koszul-tower-chain-comparison vs lem-pd-module-ringed-topos-derived-comparison: the new node proves the two-generator ordinary principal-Koszul tower isomorphism together with goodness of the pulled complexes and the target quotient augmentation, whereas the existing statement concerns Module-object and ringed-topos derived tensor comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-site-inverse-image-multimap-universal: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Universality of inverse-image units for natural maps with finitely many inputs; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-site-inverse-image-bilinear-adjunction: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Bilinear adjunction for the inverse image of a morphism of sites; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-ringed-slice-normalized-comparisons: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Existence of normalized slice tensor, Hom and Koszul comparisons; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-coef-semilinear-geometry-derived: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Derived geometric system operations and normalization; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sf-point-evaluation-tensor-coherence: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Signed tensor coherence for point sections; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sf-point-evaluation-scalar-data: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Balanced scalar comparison for point sections; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-coef-signed-single-dual-restriction: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized slice comparison for a single coefficient dual; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sf-open-operation-models: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Open operation comparisons with fixed tensor models and right square; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-ramified-finite-pullback-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized finite pullback comparison along coefficient quotient base change; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-finite-pullback-transition-generators: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Composite finite pullback transitions reduce both tensor coefficients; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sf-point-evaluation-tensor-data: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized tensor presentation for point sections; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sf-point-evaluation-derived-compatibility: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Representative-normalized derived point comparisons; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-coef-semilinear-geometry-ops: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical geometric mate and projection words; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-etale-native-tensor-pullback: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Native unbounded derived tensor commutes with etale inverse image; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sf-point-ringed-evaluation-model: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Ringed geometric-point evaluation with signed tensor and coefficient models; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-coef-semilinear-geometry-base: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Geometry base fields for coefficient linear operations; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sf-evaluation-hom-site-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Evaluation-induced derived Hom comparison for the etale-proetale morphism; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sf-point-evaluation-scalar-coherence: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Tensor square for balanced point scalar data; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sf-open-normalization-data: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Geometric and operation data for open tensor normalization; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-scalar-inverse-image-tower-diagram: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Ordinary inverse-image and balanced scalar-tower square; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-ringed-derived-tensor-diagrams: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Coherence equations for explicit canonical derived comparison maps; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-ringed-derived-tensor-lift: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Symmetric monoidal coherence of a canonical derived tensor lift; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-condensed-support-projection-formula: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Natural support tensor projection formulas on unbounded condensed modules; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sfb-ringed-slice-comparison-model: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized ringed slice comparison data; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sfb-module-object-projection-map: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical derived projection map for condensed module objects; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-ringed-derived-two-iso-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Specified geometric 2-isomorphism comparison on derived modules; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-proetale-intrinsic-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Right-tensor comparison for intrinsic constant-ring realization; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-etale-stalk-total-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical signed total tensor stalk comparison and chain naturality; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-geometric-two-iso-scalar-pairing: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Geometric two-isomorphisms preserve the ordinary scalar balanced pairing; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sfb-condensed-pullback-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized condensed-module pullback tensor comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sfb-proetale-trace-coefficient-interfaces: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical internal-module trace coefficient interfaces; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-localized-site-tensor-restriction: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Restriction to a localized site commutes with the sheaf tensor product; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-kflat-scalar-comparison-normalization: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Representative and adjunction normalization of scalar pullback comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sfb-scalar-ordinary-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized ordinary scalar tensor comparison in independent site universes; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-per-local-system-tensor-monodromy: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Tensor comparison for arbitrary torsion local systems; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-per-proetale-scalar-slice-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized scalar extension comparison on a pro-etale slice; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-per-galois-descent-monodromy-tensor: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Monodromy and tensor of modules descended along a finite Galois cover; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-continuous-module-encoding-scalar-extension: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Scalar extension under the continuous integral and rational module encodings; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-closed-immersion-scalar-change: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Ordinary closed scalar change with transported coefficients; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-left-exact-site-inverse-image-tensor: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Inverse image induced by a continuous left-exact site functor and its tensor structure; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-weil-pbc-canonical-ringed-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized ordinary tensor comparison data; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-weil-pbc-actual-finite-coefficient-transport: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Actual-ring finite coefficient transport and normalized local restriction; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-canonical-ringed-tensor-comparison-construction: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Construction of the normalized ordinary tensor comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-weil-pbc-normalized-scalar-restriction: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized completed-coefficient scalar and restriction comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-continuous-module-encoding-restriction: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Continuous module encoding commutes with restriction along an etale morphism; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-localization-inverse-image-coherence: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Coherent localization comparison for exact inverse image; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-algebraic-inverse-image-pairing-isIso: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Universality of the transported inverse-image pairing; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-ringed-topoi-module-pullback-tensor: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Underived tensor comparison for pullback of modules on ringed topoi; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-algebraic-inverse-image-pure-pairing: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns The canonical bilinear pairing of the specified inverse image; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-reduction-pullback-derived-tower: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized derived pullback of a strict coefficient reduction tower; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-scalar-extension-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Scalar extension preserves the normalized sheaf tensor; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-algebraic-inverse-image-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns The normalized tensor comparison for the specified algebraic inverse image; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-continuous-module-encoding-lattices: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Local freeness and lattice compatibility of the explicit continuous encodings; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-proetale-closed-underived-projection: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Underived tensor projection for closed pro-etale immersions with arbitrary ring coefficients; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Tensor comparison tail for scalar-extended inverse-image modules; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Common quotient reduction of the geometric scalar comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-weil-pbc-ringed-tensor-square-presentation: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Representative presentation of a commutative ringed tensor square; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-pur-signed-line-pullback-normalization-data: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized signed pullback families and scalar squares; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-common-line-positive-scalar-powers: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Common-line presentations and nonnegative powers under scalar extension; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-scalar-tensor-unit: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Scalar action unitor for a normalized signed tensor comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-module-tensor-extension-equation: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Ordinary scalar-extension tensor equation; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-signed-line-derived-base-change: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Signed line comparisons and their unbounded derived tensor action; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-module-tensor-composition-equation: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Ordinary tensor square for composite module pullback; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-ringed-site-pullback-dual-free-chart: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Invertibility of a pulled evaluation comparison on a finite-free chart; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-tate-inverse-limit-base-change: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Base change of an ell-adic inverse-limit tower and of its finite reduction tensor; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-pur-semilinear-tensor-presentation-data: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Data for semilinear transport of sheaf tensor presentations; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-normalized-tensor-constraint-transport: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Transport of normalized tensor constraints through coherent realization; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-proetale-inverse-image-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-pur-cochain-coefficient-arrows: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical scalar-association and transition arrows on cochain sheaves; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-ringed-site-pullback-pairing-transfer: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Extension of module pairings along a ringed site morphism; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-module-tensor-monoidal-equations: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Associativity and symmetry of the canonical ordinary module tensor comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-cochain-pullback-tensor-coherence: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Signed tensor comparison and composition on cochain sheaf pullbacks; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-pur-cochain-tensor-coherence-data: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical cochain ringed-pullback and coherence data; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-torsion-line-system-base-change: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized tensor extension of compatible torsion line systems; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-canonical-ringed-tensor-comparison-independent-universes: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Existing normalized ordinary tensor comparison with independent site universes; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sp-proetale-scalar-mate-identifications: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-strict-coefficient-comparison-calculus: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Simultaneous strict coefficient comparisons on ring-sheaf towers; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-inverse-image-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns The unit-normalized tensor comparison for an isomorphic base change; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-sp-constant-scalar-pullback-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical constant-coefficient scalar extension, direct image and pullback comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-independent-ringed-tensorator-existence: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Existence of the tensorator for fixed scalar insertion at independent site sizes; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-module-tensor-generator-calculus: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Pure tensors and normalized insertion naturality for sheaf modules; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-cochain-comparison-monoidal-equations: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Monoidal equations for the canonical cochain pullback comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-independent-normalized-scalar-composition: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized composition of module scalar extensions; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-inverse-image-scalar-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Inverse image commutes with extension of scalars, with its unit formula; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-inverse-image-scalar-unit-normalization: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical algebraic realization and scalar-unit normalization of pro-etale inverse image; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-kun-derived-pullback-composition-monoidal: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical derived etale inverse-image composition is monoidal; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs def-pur-cochain-coefficient-universe-transport: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Canonical common-universe transport of ring and module sheaves; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-coefficient-scalar-units: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Multiplication units for derived scalar extension; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sf-reduction-pull-finite-evaluation: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Finite evaluation respects the specified reduction/pullback comparison; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-independent-inverse-image-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized tensor comparison for an algebraic inverse image at independent site sizes; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-varying-ring-tensor-comparison: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Normalized tensor comparison for one varying-ring inverse image; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-sf-finite-field-local-tensor-model: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Localized inverse-image constant models under field scalar extension; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-module-tensor-coefficient-equations: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Ordinary module tensor equations for coefficient change; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pur-isomorphism-inverse-image-tensor-hom: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Inverse image along an isomorphism of schemes commutes with tensor products and sheaf Hom; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pd-ringed-tensor-adjunction-mate: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Identify ringed tensor comparisons with specified adjunction mates; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pd-section-ordinary-oplax-normalization: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Ordinary module pullback oplax mate on balanced generators; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pod-etale-stalk-tensor-scalar: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Geometric stalks commute with tensor products and scalar extension on the etale site; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-pod-lisse-tensor-and-scalar-extension: the new node specifies the strict balanced quotient-square maps lambda and C and their equality with the Koszul augmentation, including the fixed finite-evaluation generator, whereas the existing statement concerns Tensor products, scalar extension and stalks of lisse sheaves of modules; it does not state that entire specific assertion.

lem-a1-balanced-finite-tower-generator-comparison vs lem-weil-finite-pullback-transition-generators: the existing lemma computes one transition on an already defined pulled tensor generator; it does not construct the balanced comparison between completed and finite coefficient pullback or its normalized equality with the Koszul augmentation.

lem-a1-finite-reduction-tower-resolving-model vs lem-cbc-strict-quotient-pullback-computation: the existing lemma assumes a universal derived pair and an objectwise good replacement and computes its augmentation; the new obligation establishes B_g and supplies the particular strict principal-Koszul good replacement and its two representative computations.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-pulled-reduction-strict-tower-comparison: the latter restricts the tower to the discrete constant valuation ring, and also takes derived limits; it supplies neither this completed-ring-linear normalized comparison nor the fixed integer-shift square.
