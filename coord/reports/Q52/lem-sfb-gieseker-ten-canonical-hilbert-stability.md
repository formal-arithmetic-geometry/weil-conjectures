# Q52 assignment status

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-gieseker-ten-canonical-hilbert-stability.json: verbatim copy of the current live node; no changes, no new nodes.

## Attachments

None. A search of lean/WeilConjectures for the item identifier, ten-canonical and Gieseker found no attachment.

## Wanted

None.

## Assignment conflict

The live item already has status split and a passing review dated 2026-10-22 by NT-cc-Q15-c77141e5e for Q15. The final paragraph of coord/brief-stage1.md says that live split-and-reviewed nodes win and must never be split. This is a superseded assignment, not a new split or a repair request.

## Unfinished work

No new split or delivery can be made under that rule. The first dry run exited 1 because the retained sandbox contained no node files. This copy preserves the current live proof and review unchanged so that a second dry run can diagnose the assignment.

## Review by Q52

I read the stage-1 contract and the delivery-errors B–E checklist, inspected the live item and verified its completed review metadata. I did not independently re-review or alter its mathematical proof: the stage-1 rule forbids splitting an already reviewed live node. No mathematical statement, citation, search record or proof step was changed, and no new node was created.

## Diagnostic citation packet

The subsequent dry run requested citations.json. It now quotes the entire live statement of each dependency used by each unchanged step. These verbatim quotations support delivery-tool diagnostics only; this packet does not claim a new independent mathematical review or authority to replace the live split.

## Final dry-run result

The final deliver.py --no-push process exited 1 after server preflight: "the item's node file is unchanged". Nothing was pushed. Changing the node solely to pass that gate would violate the rule forbidding re-splitting the live reviewed node. The dispatcher assignment is therefore blocked as superseded.

## Recovery recheck 2026-10-22

Retained all sandbox files and ran the required dry run first. The process completed with exit 1: `PREFLIGHT FAILED, nothing pushed`; the sole reason was `the item's node file is unchanged`. No second delivery invocation was started.

The current live node remains split with a passing review by NT-cc-Q15-c77141e5e for Q15 dated 2026-10-22. Compared the retained node with the current live node: only lean_audit differs; its statement, proof, citations, split_report and review are identical. A fresh read-only search of lean/WeilConjectures for the item identifier, Gieseker/gieseker and ten-canonical found no attachment. No mathematical content or search record was changed.

The standing brief explicitly says: "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." The assignment is still superseded. Altering completed work merely to evade the unchanged-node gate is not an authorized repair. No push was attempted. BLOCKED: delivery preflight rejects the unchanged, already reviewed live split; dispatcher reassignment is required.


## Dispatcher retry recheck 2026-10-22

Started with the required `deliver.py Q52 lem-sfb-gieseker-ten-canonical-hilbert-stability --no-push` and polled that same process to completion (exit 1). The server admitted preflight in slot 20; its final diagnostic was: `PREFLIGHT FAILED, nothing pushed`, with the sole reason `the item's node file is unchanged`.

Re-read GOAL.md, the worker and stage-1 instructions, SETUP.md's three levels, and both copies of delivery-errors sections B–E. Compared the preserved sandbox node against the current read-only repository: only generated `lean_audit` differs. The live node still has 13 proof steps and a passing Q15 review by NT-cc-Q15-c77141e5e dated 2026-10-22. Repeated the project-source attachment check with `rg -n -i 'lem-sfb-gieseker-ten-canonical-hilbert-stability|gieseker|ten.canonical' lean/WeilConjectures`; it returned no matches. No new Mathlib searches were needed or claimed, because no node was created or re-split.

The final paragraph of coord/brief-stage1.md explicitly requires: "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." This remains a superseded dispatcher assignment, rather than an authorized repair of the completed Q15 delivery. The gate cannot be repaired by changing the preserved mathematical work merely to manufacture a diff. All prior files and content were retained. No repository or launcher file was written, no git or compiler command was run, no second deliver.py invocation was started, and no push was attempted. BLOCKED: unchanged-node preflight rejection on an already reviewed live item; dispatcher reassignment or correction of the superseded-assignment handling is required.

## Item-specific repair completed by Q52

The required recovery dry run exited 1, this time with **two** diagnostics: unchanged item, and a released human re-split requirement limiting its assembly proof to 3000 characters. I read `coord/repair-notes/lem-sfb-gieseker-ten-canonical-hilbert-stability.json`: it is an item-specific maintainer instruction dated 2026-10-22, applies the human's 2026-10-21 decision, and explicitly requires at least three new cited statement-only nodes. This supplies the authorization missing in the earlier attempts and overrides the generic prohibition on splitting already reviewed live nodes. The preceding status sections record those attempts; they are retained as requested, and their superseded BLOCKED conclusion is no longer the outcome of this repair.

## Files written for the repair

- dag/nodes/sec-six-functors-basics/lem-sfb-gieseker-ten-canonical-hilbert-stability.json: statement and imported metadata retained; seven assembly steps, 2299 characters before any diagnostic repairs.
- lem-sfb-semistable-hilbert-trait-nodal-preparation: statement, unsplit; no Mathlib match. Carries old steps 2--3 and the arithmetic-genus preparation in step 5.
- lem-sfb-balanced-nodal-trait-stable-canonical-limit: statement, unsplit; no Mathlib match. Carries old step 4 and the stable-component exclusions in step 5.
- lem-sfb-stable-curve-framed-trait-smoothing: statement, unsplit; no Mathlib match. Carries old steps 7--8, including lifting the prescribed frame.
- citations.json: full verbatim dependency statements for every citation in the seven assembly steps. The remaining local research outputs, query plan, scripts and original-reviewed-node.json are recovery material only.

Attachments: none. A new read-only project-source search found no declaration for this Hilbert-stability item or the three extracted statements. No compiler was run.

WANTED: Morrison, GIT Constructions of Moduli Spaces of Stable Curves and Maps, arXiv:0810.2340, Sections 2.1, 2.4 and 3.2--3.3, printed pp.8--17, local PDF for this item and the new nodes. I read the author's HTML/PDF online at https://arxiv.org/html/0810.2340 and https://arxiv.org/pdf/0810.2340; no literature file was downloaded or changed. The existing argument is agent-written, and its proof_origin remains agent. The singular-total-space version of the extremal-twister input retains its existing reference request; I did not disguise it as a statement of Morrison's Cartier-divisor calculation.

## Review by Q52

I read Morrison Proposition 10, equation (6), and Corollary 11 in the author's online exposition, and the actual Stacks source statements of Tag 0AY8 in more-morphisms.tex, Tag 0E7Y in examples-defos.tex, and Tags 0E76/0E78 in moduli-curves.tex. I read the statement of every assembly dependency, including the lattice and reconstruction nodes and the finite-type-base qualification in Isom-finiteness. I retained the original thirteen-step argument below so that this is an extraction of work for future workers, rather than deletion of its details. The three new files have statements only, empty proof/proof_deps, and no implicit use of this item's conclusion.

Step 1 uses exactly the Hilbert-Pluecker linearization, smooth high-degree stability and potential-stability statements. Their bounds are uniform in the field; g>=2 implies d>9(g-1) and d>=2g+1, and r>=19. The linearization theorem supplies the quotient embedding, central descent and equality of loci, including the nonreduced mu_r case. The old scalar calculation is preserved below rather than replaced by an unsupported characteristic restriction.

Step 2 uses the full conclusion of nodal preparation, followed by balanced stable canonical limits, then the Hilbert-parameter theorem's representing functor. I checked that preparation gives every hypothesis of the balanced-limit node: the family is flat/projective/finitely presented and geometrically nodal and connected, T is trivial generically, the special Hilbert embedding is complete, its chi is 1-g, and both the rational-bridge degree and the numerical bound are explicit. The balanced-limit conclusion supplies the stable genus-g curve and its complete tenth-canonical embedding, precisely the objects classified by J.

Step 3 uses the finite-type locally closed parameter J, the finite-type projective Hilbert scheme over k, the image-boundary DVR statement, and the criterion turning a closed-image immersion into a closed immersion. A boundary trait's generic lift is the exact input to step 2. This checks the given scheme structure, not merely a closed set of geometric points.

Step 4 uses the framed-smoothing statement, which returns a stable family on the entire k[[t]] trait with the specified geometric point and a smooth generic fibre, and smooth high-degree stability. Formation of the ten-canonical space and evaluation already come with the parameter theorem inside the smoothing node. The bound from step 1 is independent of the fraction field's algebraic closure.

Step 5 uses projective semistable replacement exactly over a DVR, with a finite fraction-field extension, generic projective coordinate change and dominating local DVR map. The parameter theorem makes J invariant and turns the resulting factorization into a stable family. Scheme-theoretic factorization uses injectivity of R' into its fraction field; it follows from the closed ideal and generic factorization, not from pointwise containment alone.

Step 6 uses injective lattice restriction and multiplicative equality from the logarithmic pluricanonical-lattice node, with no markings. The stable component definition gives 2g_i-2+n_i>0, which is the positivity hypothesis for the nodal canonical-reconstruction theorem over the Noetherian DVR itself. Taking Proj gives an isomorphism of families; the parameter theorem's frame torsor identifies the special embedded curves up to PGL. The linearization theorem gives geometric field-extension compatibility. This is a few-line assembly of already cited algebra comparisons; no new family-comparison statement is hidden here, and the finite-type-base Isom theorem is not misapplied to k[[t]].

Step 7 uses the parameter groupoid equivalence to identify stabilizers, Isom-finiteness only over Spec(Omega) as a finite-type Omega-base, and the orbit-closure dimension theorem. Every orbit in invariant closed J has zero-dimensional stabilizer and hence equal dimension; the boundary theorem would force strict decrease. No invertibility of automorphism orders is needed.

For the new nodal-preparation node, I checked 0AY8 against the needed hypotheses, not just its conclusion. Generic stability gives geometric reducedness/connectedness and H0=K. Flatness makes the uniformizer a nonzerodivisor, so affine rings inject into their reduced generic localizations; minimal-prime avoidance excludes vertical generic points. Properness comes from the closed projective family, and the DVR base is normal. Only after 0AY8 gives connected special fibre can potential stability be applied. Relative dualizing base change is available on the resulting nodal family. Componentwise Riemann--Roch and Picard-degree additivity turn potential stability into the bound for T. The original genus correction is retained: P(0)=chi=1-g, reducedness over the algebraically closed (therefore perfect) residue field is geometric reducedness, H0=Omega, and dimension-one cohomology vanishing gives H1 dimension g. The statement does not claim the yet-to-be-proved stable or ten-canonical conclusion on the special fibre.

For the balanced-limit node, the geometric special fibre is connected and the generic trivialization is over K itself, as required by the extremal-twister input. A nontrivial special T would force 0<k_Y<=deg_Y T<=k_Y/2. Once T is trivial, a rational bridge has canonical degree zero but hyperplane degree one. A rational one-self-node whole curve and a smooth genus-one whole curve each have chi=0 by the normalization Euler formula, contradicting 1-g for g>=2. These are exactly the remaining unstable normalized-component cases. This verifies the small irreducible, self-nodal and compact-type cases and uses no regularity of X or Cartier property of its components. The relative statement is a polarized local degeneration lemma; it has no Hilbert stability or global closedness assertion.

For framed smoothing, Tag 0E7Y requires properness, dimension <=1, lci, and a finite nonsmooth locus. The original nodal-lci and nodal Fitting-singular-locus statements supply the latter two; proper nodal curves have finitely many singular points. The stable genus-g open locus contains the closed point of the local trait, hence the entire trait, so no fibre is silently assumed stable. Base-change-compatible ten-canonical sections are free over R. Lift any basis realizing the given special projective frame; its determinant is a unit, so it is a basis. This supplies the prescribed frame as well as some framing. The smooth-curve edge case also works; no positive number of nodes or characteristic restriction is assumed.

B--E checklist: no new node contains proof steps or a proof sketch in its statement; all objects and numerical bounds are quantified, every bracketed notion has a statement dependency, and all new nodes have exact logged queries and results. None asserts the item or one of its global clauses. I searched the whole DAG, blueprint and project source; nearby lemmas provide separate ingredients, as listed below. Every non-elementary assembly fact is a cited statement; citations.json quotes their actual statements. The only elementary assembly is reconstruction and frame transport from explicit multiplicative lattice and Proj assertions. No unit/chapter route was changed, no SGA reference was added, and no item statement was weakened. No assembly step exceeds 2000 characters.

## Not duplicates

lem-sfb-balanced-nodal-trait-stable-canonical-limit vs def-sfb-marked-nodal-dualizing-degree-data: the existing node defines a structure containing dualizing and component-degree data and explicitly asserts no existence or positivity; the new polarized degeneration theorem forces a generic tenth-canonical polarization to remain canonical on the special fibre and proves the stable component inequalities from balanced degrees.
lem-sfb-stable-curve-framed-trait-smoothing vs lem-sfb-isolated-curve-formal-lifting: the existing node assumes compatible local Artinian liftings and returns a compatible proper infinitesimal system; it does not produce an effective projective stable smoothing over k[[t]], a smooth generic fibre or an extension of the prescribed ten-canonical projective frame.
lem-sfb-semistable-hilbert-trait-nodal-preparation vs lem-trf-proper-normal-geometric-connectedness: 0AY8 assumes a reduced total space and horizontal generic points; the new local Hilbert-family result proves those hypotheses from flatness and generic stability and also proves nodality, balanced degrees and the arithmetic genus. It is not a specialization under the new node's original hypotheses alone.
lem-sfb-semistable-hilbert-trait-nodal-preparation vs lem-sfb-gieseker-potential-stability: potential stability needs connectedness already and concerns one geometric embedded scheme; preparation starts with a DVR degeneration and establishes the connectedness, relative nodal family, generic trivialization and genus comparison needed downstream.
lem-sfb-semistable-hilbert-trait-nodal-preparation vs lem-sfb-nodal-log-canonical-reconstruction: reconstruction assumes a nodal family and states its dualizing line and Proj comparison; preparation establishes nodality from a semistable Hilbert degeneration and computes its balanced degrees.
lem-sfb-balanced-nodal-trait-stable-canonical-limit vs lem-sfb-nodal-log-canonical-reconstruction: reconstruction neither forces the special polarization to be canonical from a generic isomorphism nor proves the stable-component conditions; those are the new local numerical argument (shared source 0E74).
lem-sfb-balanced-nodal-trait-stable-canonical-limit vs lem-sfb-nodal-trait-twister-extremal-degree: the twister statement only detects a large degree on some subcurve, under a generic trivialization; the new polarized limit combines it with the balanced bound and excludes unstable components using genus and canonical degrees.
lem-sfb-stable-curve-framed-trait-smoothing vs lem-sfb-isolated-lci-curve-smoothing: 0E7Y assumes lci and isolated nonsmooth locus and produces a projective smoothing; the new result begins with a stable curve and a prescribed projective frame, ensures stability of the whole trait, and extends that frame in the canonical Hilbert parameter.
lem-sfb-stable-curve-framed-trait-smoothing vs lem-sfb-stable-and-smooth-family-open-loci: 0E76/0E78/0E86 give open loci for an existing family, not existence of a smoothing or extension of a prescribed projective frame.
lem-sfb-stable-curve-framed-trait-smoothing vs lem-sfb-nodal-deformation-smoothing-parameters: the latter is a local-to-global deformation-ring statement for a curve without infinitesimal automorphisms; it does not state the projective stable family with its prescribed canonical projective frame.

## Searches and proof-work distribution

Each new node has two distinct LeanFinder phrasings, one Loogle query, one grep query and one LeanSearch query, all run through msearch.py. The exact outputs are retained in its mathlib_searches and sandbox search files. All services answered; no unavailable result was converted into an absence claim. The hits were valuative-criterion existence, elliptic good/minimal reduction, smooth morphisms, polynomial Hilbert series, support specialization, and topological vector-bundle trivializations. None has stable/nodal-curve or balanced-polarization hypotheses and conclusions; none is a one-line specialization. Grep and Loogle found no match.

Old step 1 remains assembly step 1 (central descent is already an explicit assertion of the linearization node). Old steps 2--3 and the first part of step 5 become nodal preparation. Old step 4 and the remaining component exclusions in step 5 become balanced canonical limits. Old step 6 remains assembly step 3. Old steps 7--8 become framed stable smoothing and assembly step 4. Old step 9 remains step 5; old steps 10--11 remain elementary assembly step 6; old steps 12--13 remain step 7. These three separate curve-family arguments are open for other workers, and their statements carry all the hypotheses needed to recover the old argument. No new proof has been marked finished merely by shortening prose.

## Original reviewed proof retained in full

### Original step 1

Choose $m$ at least the bounds for the Hilbert embedding, smooth-curve stability and potential stability, with $(g,d,r)=(g,20(g-1),19(g-1))$. These depend only on $g$: $20(g-1)>9(g-1)$ and $20(g-1)\geq2g+1$ for $g\geq2$. The Hilbert-Pluecker construction gives the stated quotient of rank $P(m)$ and the very ample line $\Lambda_m$. Set $A=\Lambda_m^{\otimes r}$ with its descended $G$-linearization. In the central character calculation a scalar $t$ acts on the determinant quotient by $t^{mP(m)}$ (or its inverse under the dual convention); on the $r$th power this is trivial on the group scheme $\mu_r$. The cited descent result therefore applies even when the characteristic divides $r$. Its comparison of loci lets us use the two Hilbert stability inputs with this $A$.

Uses: lem-sfb-hilbert-plucker-pgl-linearization, lem-sfb-smooth-curve-high-degree-hilbert-stability, lem-sfb-gieseker-potential-stability

### Original step 2

Write $J^{ss}=J\cap Z^{ss}(A)$. Consider any trait $\alpha:\operatorname{Spec}R\to Z^{ss}(A)$ whose generic point is in $J^{ss}$, and pull back the universal closed Hilbert family $X\subset\mathbf P^{r-1}_R$. Its generic fibre is a stable curve, hence geometrically reduced and connected. The global-sections criterion gives $H^0(X_K,\mathcal O)=K$. Flatness injects every affine coordinate ring of $X$ into its localization at a uniformizer $t$; that localization is reduced, so $X$ is reduced. There are no vertical irreducible components: in a reduced Noetherian ring a minimal prime consists of zero divisors, whereas $t$ is a non-zero-divisor by flatness. A DVR is a valuation ring by its definition, so the valuation-ring normality theorem makes the trait normal; its other stalk is the fraction field. The minimal-prime avoidance lemma justifies the preceding nonverticality assertion. The family is proper by the projective-bundle properness theorem. The proper-normal-base connectedness theorem now applies over the normal integral trait $\operatorname{Spec}R$ and makes every fibre geometrically connected. Its hypotheses concern the normality of the base; no normality of $X$ is asserted.

Uses: lem-sfb-projective-hilbert-polynomial-representability, lem-sfb-ten-canonical-hilbert-parameter, lem-pc-h0-geom-connected, lem-trf-proper-normal-geometric-connectedness, lem-pc-minimal-prime-avoids-nonzerodivisor, lem-weil-pbc-valuation-ring-normal, def-sc-discrete-valuation-ring, lem-trf-projective-bundle-proper

### Original step 3

Apply potential stability to the geometric special fibre $C$, now known to be connected, since its $m$th Hilbert point is semistable. Thus $C$ is reduced, nodal and of pure dimension one, and the embedding is complete. Both geometric fibres of $X/R$ are therefore nodal. The nodal dualizing theorem gives $\omega=\omega_{X/R}$, compatible with passage to both fibres. Put $T=\mathcal O_X(1)\otimes\omega^{\otimes(-10)}$. The generic ten-canonical condition makes $T|_{X_K}$ trivial; a base-line twist is harmless over the field $K$. On each smooth proper normalized geometric component, Riemann--Roch identifies Euler-characteristic degree with the Picard degree homomorphism, so degrees add under tensor products and change sign under duals. Summing this identity over components, for every proper nonempty union $Y$ of geometric special-fibre components, potential stability gives
$$|\deg_Y(T|_C)|=|\deg_Y\mathcal O_C(1)-10\deg_Y\omega_C|\leq k_Y/2,$$
because $d/(2g-2)=10$.

Uses: lem-sfb-gieseker-potential-stability, lem-sfb-nodal-log-canonical-reconstruction, lem-sfb-ten-canonical-hilbert-parameter, lem-sc-riemann-roch, def-sc-pic0

### Original step 4

The extremal-twister lemma applies to this projective flat finitely presented nodal family and $T$. If $T|_C$ were nontrivial, it would give a nonempty proper subcurve $Y$ with $\deg_Y(T|_C)\geq k_Y>0$. Combined with the preceding upper bound this would imply $0<k_Y\leq k_Y/2$, a contradiction. Hence $\mathcal O_C(1)\simeq\omega_C^{\otimes10}$. This argument uses a lemma for arbitrary nodal total spaces, rather than treating all special-fibre components as Cartier divisors.

Uses: lem-sfb-nodal-trait-twister-extremal-degree

### Original step 5

First, $C$ has arithmetic genus $g$. Its point lies in $Z$, so its fibre Hilbert polynomial is $P$, and the flat-projective Hilbert-polynomial theorem identifies this with $e\mapsto\chi(C,\mathcal O_C(e))$; thus $\chi(C,\mathcal O_C)=P(0)=1-g$. The field $\Omega$ is algebraically closed, hence perfect, so the reduced $C$ is geometrically reduced; it is geometrically connected by step 2; the global-sections criterion gives $H^0(C,\mathcal O_C)=\Omega$. As $C$ is Noetherian of dimension one, $H^q(C,\mathcal O_C)=0$ for $q\geq2$. Hence $\dim_\Omega H^1(C,\mathcal O_C)=g$. The potentially stable $C$ is actually stable. A genus-zero normalized component has at least two node branches. If it has just two, it is either a smooth rational component meeting the rest in two points or the whole curve is an irreducible rational curve with one self-node. For the latter the nodal normalization Euler formula gives $\chi(C,\mathcal O_C)=1-1-0=0\neq1-g$, as $g\geq2$. In the former case potential stability gives hyperplane degree one, whereas the dualizing component-degree formula gives $10(2\cdot0-2+2)=0$, contradicting the isomorphism just obtained. A genus-one component with no node branches would be all of $C$, since $C$ is connected; then the same formula gives $\chi(C,\mathcal O_C)=1-0-1=0\neq1-g$. These exclude exactly the failures of the stable component condition. The embedding is complete by potential stability, so the parameter theorem puts its geometric Hilbert point in $J$. Therefore the special point of every trait in step 2 belongs to $J^{ss}$.

Uses: lem-sfb-gieseker-potential-stability, lem-sfb-flat-projective-hilbert-polynomial-locality, lem-kun-geometric-reduced-perfect, lem-pc-h0-geom-connected, lem-sc-noetherian-cohomology-above-dimension, lem-trf-nodal-curve-normalization-euler, lem-sfb-nodal-log-canonical-reconstruction, def-sfb-stable-pointed-curve, lem-sfb-ten-canonical-hilbert-parameter

### Original step 6

The immersion $J^{ss}\to Z^{ss}(A)$ is of finite type, and $Z^{ss}(A)$ is Noetherian, being open in the finite-type Hilbert scheme over $k$. If its image had a boundary point, the image-boundary DVR lemma would provide a trait through that point with generic lift into $J^{ss}$, contradicting steps 2--5. Thus its image is closed. The closed-image criterion for immersions makes $J^{ss}\hookrightarrow Z^{ss}(A)$ a closed immersion of schemes, including its given scheme structure; this conclusion is stronger than a claim just about closed geometric orbits.

Uses: lem-sfb-ten-canonical-hilbert-parameter, lem-sfb-projective-hilbert-polynomial-representability, lem-sfb-noetherian-image-boundary-dvr, lem-weil-pbc-immersion-closed-image-closed-immersion

### Original step 7

To show that every point of $J$ is semistable, fix a geometric stable curve $C/\Omega$ of genus $g$. The nodal-lci criterion makes $C$ a local complete intersection. The nodal singular-locus statement makes its nonsmooth locus closed and unramified over $\Omega$, hence discrete; since $C$ is proper, this locus is finite. The isolated-lci smoothing theorem gives a projective flat finitely presented family $\mathcal C\to\operatorname{Spec}\Omega[[t]]$ with special fibre $C$ and smooth generic fibre. The stable genus-$g$ open locus in this family contains the closed point. An open containing the closed point of a local scheme is the whole spectrum. Consequently $\mathcal C$ is a stable genus-$g$ family on the entire trait.

Uses: lem-trf-nodal-curve-lci-criterion, lem-trf-nodal-family-fitting-singular, lem-sfb-isolated-lci-curve-smoothing, lem-sfb-stable-and-smooth-family-open-loci

### Original step 8

The parameter theorem makes $f_*\omega_{\mathcal C/R}^{\otimes10}$ locally free of rank $r$ and gives its ten-canonical embedding. Over the local ring $R=\Omega[[t]]$ choose a basis, obtaining $\alpha:\operatorname{Spec}R\to J\subset Z$. Its generic fibre is a smooth complete degree-$d$ embedding; by smooth high-degree stability its Hilbert point is stable, in particular semistable. The bound chosen in step 1 is uniform and so applies also after passing to an algebraic closure of the fraction field.

Uses: lem-sfb-ten-canonical-hilbert-parameter, lem-sfb-smooth-curve-high-degree-hilbert-stability

### Original step 9

Apply projective semistable replacement to $\alpha_K$. Obtain $R\to R'$, finite extension of fraction fields $K\subset K'$, a coordinate change $h\in G(K')$, and $\beta:\operatorname{Spec}R'\to Z^{ss}(A)$ with $\beta_{K'}=h\alpha_{K'}$. The generic curve of $\beta$ is isomorphic to the generic curve of $\mathcal C_{R'}$ and is ten-canonically embedded. Thus $\beta_{K'}$ lies in $J^{ss}$. Its special point lies in $J^{ss}$ by steps 2--6. Since $J^{ss}$ is closed in $Z^{ss}$, the whole $\beta$ factors through it: locally its defining ideal maps to zero in the field $K'$, and $R'\hookrightarrow K'$ is injective. The pulled-back family $\mathcal C'$ is therefore stable and ten-canonically embedded over $R'$.

Uses: lem-sfb-projective-git-semistable-replacement, lem-sfb-ten-canonical-hilbert-parameter

### Original step 10

Compare the two stable nodal families $\mathcal C_{R'}$ and $\mathcal C'$ using the generic isomorphism induced by $h$. Apply invariance of semistable logarithmic pluricanonical lattices with no markings. Restriction to the generic fibre is injective, and the stated multiplicative equalities identify the full graded $R'$-algebras $\bigoplus_{a\geq0}H^0(\mathcal C_{R'},\omega^{\otimes a})$ and $\bigoplus_{a\geq0}H^0(\mathcal C',\omega^{\otimes a})$. The stable component condition makes all the degrees $2g_i-2+n_i$ positive. Canonical reconstruction therefore identifies each family with the Proj of its corresponding algebra. Taking Proj of the algebra isomorphism gives an isomorphism of the two families and in particular of their geometric special fibres. This uses the nodal-family statements over the DVR itself; it does not apply the finite-type-base isomorphism theorem to $\Omega[[t]]$.

Uses: lem-sfb-semistable-log-pluricanonical-lattices, lem-sfb-nodal-log-canonical-reconstruction, def-sfb-stable-pointed-curve

### Original step 11

Both geometric special fibres carry complete ten-canonical embeddings. An abstract isomorphism induces an isomorphism of their spaces of ten-canonical sections; relative to the two projective frames this is a projective coordinate change. Equivalently the frame torsor in the parameter theorem identifies these Hilbert points up to $G$. The geometric special Hilbert point of $\beta$ is semistable, so that of $C$ is semistable as well. The statement holds for every geometric $C$, and the linearization theorem makes semistability compatible with field extension. Hence $J\subset Z^{ss}(A)$, and the closed immersion of step 6 is precisely $J\hookrightarrow Z^{ss}(A)$.

Uses: lem-sfb-ten-canonical-hilbert-parameter, lem-sfb-hilbert-plucker-pgl-linearization

### Original step 12

For a geometric point $z\in J(\Omega)$, the equivalence $[J/G]$ with the curve groupoid in the parameter theorem identifies its scheme-theoretic stabilizer with the automorphism scheme of the underlying stable curve. Apply the finite unramified isomorphism theorem with no markings, with ground field $k=\Omega$ and base $S=\operatorname{Spec}\Omega$; this base is of finite type over that field. It shows that every such stabilizer is finite and thus has dimension zero. No assertion that the order of this finite group is invertible is used.

Uses: lem-sfb-ten-canonical-hilbert-parameter, lem-sfb-stable-pointed-isom-finite

### Original step 13

Work over any algebraically closed extension of $k$. Since $J$ is invariant and closed in $Z^{ss}(A)$, the closure there of an orbit through $z\in J$ lies in $J$. If the orbit were not closed, an orbit in its boundary would have strictly smaller dimension by the orbit-closure lemma. But every point of $J$ has zero-dimensional stabilizer by step 12, so the dimension formula makes every such orbit have dimension $\dim G=r^2-1$. This contradiction shows the orbit is closed in $Z^{ss}(A)$. Together with semistability and the zero-dimensional stabilizer this is exactly $z\in Z^s(A)$. Thus $J\subset Z^s(A)$ and $J\hookrightarrow Z^{ss}(A)$ is closed, as required in every characteristic.

Uses: lem-sfb-git-orbit-closure-dimension

## Delivery validation

The first repaired dry run exited 1 at the duplicate-source gate, asking for two additional pairs (the degree-data definition and the infinitesimal formal-lifting statement). I opened both statements and added the distinctions above. No mathematical duplicate was found. A new server dry run is pending; no push attempted yet.
