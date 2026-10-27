## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-projective-hilbert-polynomial-locality.json — existing statement retained verbatim; four-step assembly, 2188 text characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-projective-twist-base-change-data.json — statement, unsplit, no Mathlib match; relative twist construction, base flatness and base-change identifications.
- dag/nodes/sec-six-functors-basics/lem-sfb-projective-field-coordinate-euler-polynomial.json — statement, unsplit, no Mathlib match; proper/Noetherian/coherent field preparation and the coordinate/Euler polynomial construction.
- dag/nodes/sec-six-functors-basics/lem-sfb-graded-coordinate-polynomial-degree-emptiness.json — statement, unsplit, no Mathlib match; monomial growth, degree bound, and vanishing/empty-Proj criterion.
- citations.json — one verbatim statement quote for every step/node citation.
- searches.jsonl — actual Q42 search-command results, retained without rewriting them.

Three new nodes, zero Mathlib leaves. New nodes have no proof steps, proof dependencies, or proof sketch in their statements. No Lean or unit/chapter file was written, and no compiler, Lake or build command was run.

## Attachments

None. The exact tag search in lean/WeilConjectures returned no declaration for the family item. The HilbertPolynomial and Ample modules address individual proper schemes, not the full family statement. The corresponding lean/Sheaf/AlgebraicGeometry/FlatProjectiveHilbertPolynomialLocality.lean main theorem at line 152 ends in sorry at line 176. Its field theorem also has sorry. Thus it is not finished evidence. The preserved Lean record and target statement have not been changed.

## WANTED

None. I used the local Stacks sources and the current blueprint, not SGA.

## Findings and changes

This repairs the single return: the old 5691-character proof had to be spread across at least two comparable new statement-only nodes, with parent assembly at most 3000 characters. Three independent prerequisites now carry the deferred work. The entire returned statement, existing source/citation/search records and Lean metadata were retained. The sandbox initially contained only dispatcher markers, with no node, report, or searches.jsonl. I recovered the returned node and NR report from the read-only repository and saved copies as returned-item.json and previous-report.md in the sandbox before editing. The first required dry run was attempted before repair and exited because the recovered report had no Review by Q42 section. The report below replaces that missing review, while retaining the historical report at the end.

No statement dispute was found. In particular, no Noetherian hypothesis has been added to the family base. The new field polynomial statement puts the properness/Noetherianity/coherence verification with the argument that needs it. The graded lemma assumes an eventual polynomial instead of claiming to construct it. This separation makes the three statements independently workable and avoids moving the whole family theorem to one replacement node. New-node argument sizes in the old proof are approximately 1100, 1700, and 1179 characters; none carries family polynomial local constancy or family polynomial base change.

The nearest blueprint ancestor remains null: tools/blueprint_refs.py ancestor reports None for this existing created-node chain. I kept that inherited value, copied its precise Hilbert-scheme/direct-image prerequisite place, prefixed the item to each new node's via list, and specified the exact returned steps realized. Whole-blueprint searches for Hilbert polynomial, numerical polynomial, coordinate, integer twists, empty Proj and 0B9T found no node with a new statement. The current main-20261015 chapter route and the stored sk-thm-sf-ctf-stability unit were read; no route change is made.

## Return repaired: argument accounting

Old step 1 is partitioned, not deleted: projective properness over an arbitrary base belongs to the twist-data node; properness, Noetherianity and coherent structure sheaf on each field scheme belong to the field-polynomial node. Old step 2, including gluing over affine base opens, signed tensor powers, finite presentation, base flatness and arbitrary-base-change twist identifications, belongs to the twist-data node. Old step 3 is the existing proper-flat-sheaf Euler theorem, applied with its hypotheses explicitly supplied in new parent step 1. Old step 4, including homogeneous ideal existence, all-integer Euler polynomial, eventual coordinate agreement for every defining ideal, uniqueness and presentation independence, belongs to the field-polynomial node. Old steps 5 and 6 belong to the graded degree/emptiness node; its three-way equivalence includes both directions. Old steps 7 and 8 remain the explicit finite-intersection/interpolation and fibre-product/polynomial-uniqueness assembly in parent steps 3 and 4. The exact old argument text is retained below for the next workers: no argument has been replaced by an unexplained summary.

## Review by Q42

I read perfect.tex Tag 0B9T, lemma-chi-locally-constant-geometric, at lines 7962--7987. It assumes proper finite presentation and a finitely presented module flat over the base, and explicitly says formation commutes with base change. This is exactly the item route; it applies to arbitrary bases and arbitrary field-valued points. I read constructions.tex lemma-when-invertible and lemma-apply-modules, Tags 01MS and 01MT, at lines 1769--1848: the local isomorphism is multiplication by a homogeneous coordinate power and includes negative powers. I read the twist definition's actual transition rule and the pullback definition, so the new twist statement uses the existing gluing model rather than introducing a different twist. Its properness clause uses the same projective-proper result as the returned proof (morphisms.tex Tag 01WC). The additional conclusions are not supplied by the properness theorem alone or by the standard-Proj tensor theorem alone.

For the field-polynomial node I read varieties.tex Tag 0BEM, lemma-numerical-polynomial-from-euler, at lines 10195 onward, and Tags 08AC/08AE at lines 6770--6847. Snapper gives values at every integer, with numericality, not just eventually positive integers. The field scheme is proper by projective properness, finite type over the Noetherian field, hence Noetherian by the same 01T6 statement as before; its structure sheaf is coherent by 01XZ. These are conclusions of the new field lemma, not extra hypotheses on the parent. I read constructions.tex Tag 03GL, lemma-closed-in-projective-space, at lines 2989 onward, including the local ideal argument; it gives an actual homogeneous presentation for every closed subscheme. I read coherent.tex Tag 0AG7, lemma-recover-tail-graded-module, at lines 3862 onward. Together with the existing coordinate/Euler comparison node and Serre vanishing from 08AE it gives equality for every homogeneous defining ideal, including unsaturated ones. The new statement explicitly includes existence of that ideal, all-integer polynomial existence, eventual equality and both uniqueness assertions. It neither repeats just Snapper nor just the existing coordinate/Euler comparison.

For the graded degree/emptiness node I checked the monomial-count paragraph following 08AC and the standard chart definition of Proj. Its polynomial is an input with eventual equality; its conclusions are growth/degree and the empty-Proj criterion, rather than existence or family locality. Counting degree-d monomials gives the upper bound binomial(d+n,n). For a nonzero eventually nonnegative rational polynomial the leading coefficient is positive; the written old lower estimate (a/2)d^r contradicts the upper (n+1)^n d^n for r>n. If Q=0, high graded pieces vanish, making powers of every coordinate zero, hence all standard charts empty. Conversely if Proj(A) is empty, each standard chart's degree-zero localized ring is zero; 1=0 there implies some positive power of its coordinate is zero in A. Choose exponents e_i>=1; every monomial of degree greater than sum(e_i-1) contains a vanishing power. Thus A_d=0 eventually, and polynomial uniqueness gives Q=0. This explicit reverse argument makes the statement independent of an Euler characteristic assumption. The unit ideal and the zero quotient are included throughout. These are substantial coordinate growth and chart arguments being extracted under the human's explicit re-split instruction, not new names for one-line formal consequences.

I opened every cited statement in the four parent steps. In step 1 the twist-data node asserts exactly properness, finite presentation, base flatness and base-change twist identifications. The existing proper-flat Euler node asserts both local constancy and its arbitrary-base-change formula, verbatim in citations.json; f's finite presentation is the parent hypothesis. Applying its second clause to Spec K gives the equality with E_d(t). In step 2 the field-polynomial node explicitly supplies an ideal presentation and eventual coordinate agreement, which are precisely the hypotheses of the graded lemma; the latter explicitly supplies both degree and zero/empty clauses. The first node's induced closed embedding clause makes the field-polynomial lemma applicable to every field pullback. Step 3 cites no new assertion: finite intersections of the previously obtained n+1 open neighbourhoods and the polynomial root bound prove the equality, including zero polynomials. Step 4 uses only the universal property actually stated in def-pc-fibre-product and the earlier field-point results; the two iterated pullbacks have the same projections and universal property. At every integer their polynomials equal the same E_d(h(t')), so uniqueness finishes. No assumption of a map between chosen algebraic closures is made, and no flatness or finite presentation of h is assumed.

I checked B--E of delivery-errors.md against the files. All objects in new statements are quantified, numericality and eventual equality are explicit, the quotient grading and Proj refer to existing definitions, and every introduced sheaf notion is defined by an existing statement dependency or inline. The parent text uses only the full statements quoted in citations.json, never a construction hidden in a cited proof. New nodes contain only statements. They have the item's fixed chapter/unit and inherited blueprint route, actual Mathlib records, empty proofs, and no invented Lean attachments. Definitions elsewhere in the DAG and the human's target statements are not edited. The old off-unit tool declarations are no longer needed in the parent split_report because their mathematical preparation is deferred inside the new statements; maintainer-owned tool_uses and review metadata were retained untouched.

Small cases checked: n=0, J=0 gives A=k[z] and constant polynomial 1, with one nonempty chart; J=(z^a), a>=1, gives eventually zero pieces and empty Proj even though low pieces may be nonzero. For any n, J=(1) gives the zero quotient and empty scheme, while J=0 attains binomial(d+n,n) and degree n. A double point in P^1, J=(z_1^2), has eventual dimension 2 and nonzero constant polynomial, so nilpotents do not cause a false emptiness assertion. Twists with d<0 use dual powers; rank-one local bases remain finite presentations and base-flat stalks. Empty T and Z, nonreduced and non-Noetherian bases, unsaturated ideals, and arbitrary nonflat h do not invalidate any hypothesis. The parent interpolation uses only finitely many values, without a uniform Serre threshold on the family. Every parent step is below 2000 characters and the complete parent proof is 2188 characters.

I read all Q42 search results, including a second natural-language formulation for every new argument. Loogle's hilbertPoly declarations concern coefficients of p/(1-X)^d, not coherent scheme cohomology; Mathlib/RingTheory/Polynomial/HilbertPoly.lean:18--44 explicitly lists graded-module Hilbert polynomials as TODO. Module.isLocallyConstant_rankAtStalk at RingTheory/Spectrum/Prime/FreeLocus.lean:224 concerns a flat finitely presented module, not derived projective cohomology. The proper-Proj instances prove only properness, and the homogeneous-ideal/ProjectiveSpectrum hits supply definitions or point facts, not the new degree/vanishing theorem. LeanSearch also returned unrelated incidence-algebra Euler characteristics and Krull-dimension inequalities. Actual grep searches gave no matches in the named subdirectories. No partial match has been promoted to a Mathlib leaf. Item-level previous searches and the previous report are retained, without claiming they were run by Q42.

Correction made during self-review: the twist-data statement now cites the flat-module definition explicitly; citations.json was refreshed after that change so its quote remains verbatim. No statement of the parent was altered. The preflight/dry-run result is recorded after the checks below.

## Not duplicates

lem-sfb-graded-coordinate-polynomial-degree-emptiness vs def-sfb-projective-coordinate-hilbert-polynomial: the existing node defines a predicate; the new lemma bounds an input eventual polynomial and proves the zero/empty equivalence.

lem-sfb-graded-coordinate-polynomial-degree-emptiness vs lem-sfb-flat-projective-hilbert-polynomial-locality: the existing item is the parent family theorem; this new prerequisite carries only one independent ingredient and has no family polynomial local-constancy or polynomial base-change conclusion.

lem-sfb-projective-field-coordinate-euler-polynomial vs def-sfb-coordinate-quotient-grading: the existing node defines the quotient grading; the new node proves existence and uniqueness of the polynomial computed from it.

lem-sfb-projective-field-coordinate-euler-polynomial vs def-sfb-projective-coordinate-hilbert-polynomial: the existing node defines an eventual-dimension predicate without asserting existence; the new field lemma proves existence, numericality and all-integer Euler comparison.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-per-equivariant-projective-envelope: the existing result constructs an equivariant projective envelope of a quasi-projective scheme; the new result computes Euler and coordinate polynomials of a fixed closed embedding.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-per-projective-closed-subscheme-homogeneous-ideal: the existing result constructs the homogeneous ideal only; the new field result also supplies all-integer Euler polynomial existence, numericality and uniqueness.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-sc-deg-pullback-finite: the existing result is multiplicativity of an ample degree under a finite surjection; the new result constructs the coordinate/Euler polynomial for one field scheme.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-sc-hilbert-difference: the existing result computes differences using meromorphic sections and lower-dimensional cokernels; the new result identifies a numerical polynomial with coordinate dimensions.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-sc-hilbert-polynomial: the existing result is an Euler polynomial for an ample line bundle; the new result supplies a coordinate presentation and eventual equality for every homogeneous defining ideal, including unsaturated ideals.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-sfb-finite-graded-module-section-tail: the existing result identifies high graded pieces with H0; the new result constructs and uniquely characterizes an all-integer numerical Euler polynomial for a closed subscheme.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-sfb-flat-graded-tail-proj: the existing result constructs a flat family from prescribed locally free graded tails and only compares polynomials eventually; the new result proves all-integer Euler polynomial existence and uniqueness for an arbitrary field subscheme.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-sfb-flat-projective-hilbert-polynomial-locality: the existing item is the parent family theorem; this new prerequisite carries only one independent ingredient and has no family polynomial local-constancy or polynomial base-change conclusion.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-sfb-projective-closed-subscheme-homogeneous-ideal: the existing result constructs the homogeneous ideal only; the new result also constructs the numerical all-integer Euler polynomial and identifies and uniquely characterizes it for every defining ideal.

lem-sfb-projective-field-coordinate-euler-polynomial vs lem-sfb-projective-coordinate-ring-euler-polynomial: the existing result compares dimensions and Euler characteristics eventually; the new result constructs the all-integer numerical polynomial and the ideal presentation and proves both uniqueness statements.

lem-sfb-flat-projective-twist-base-change-data vs lem-chow-closed-model: the existing result concerns properness or a projective model, and does not assert the base-flat integer twists and arbitrary-base-change twist identifications of the new result.

lem-sfb-flat-projective-twist-base-change-data vs lem-kun-projective-implies-proper: the existing result concerns properness or a projective model, and does not assert the base-flat integer twists and arbitrary-base-change twist identifications of the new result.

lem-sfb-flat-projective-twist-base-change-data vs lem-sfb-finite-graded-module-section-tail: the existing result compares high graded sections over a Noetherian degree-zero ring; the new result concerns base-flat twists and arbitrary base-change identifications, with no Noetherian base.

lem-sfb-flat-projective-twist-base-change-data vs lem-sfb-standard-proj-twist-tensor: the existing result is multiplication on a fixed absolute Proj; the new result includes base-flat stalks, finite presentation and arbitrary scheme base change for an embedded flat family.

lem-sfb-flat-projective-twist-base-change-data vs lem-trf-projective-bundle-proper: the existing result concerns properness or a projective model, and does not assert the base-flat integer twists and arbitrary-base-change twist identifications of the new result.

lem-sfb-flat-projective-twist-base-change-data vs lem-weil-pbc-finite-separable-base-refinement: the existing result concerns properness or a projective model, and does not assert the base-flat integer twists and arbitrary-base-change twist identifications of the new result.

lem-sfb-flat-projective-twist-base-change-data vs lem-weil-pbc-projective-space-twisting-sheaf-charts: the existing result describes O(1) on projective space over Z; the new result treats every integer twist on a flat closed family over an arbitrary scheme.

Additional concept comparisons: the generic lem-sfb-proper-flat-sheaf-euler-local-constancy is reused directly, not re-created; the twist node does not assert Euler local constancy. The existing lem-trf-standard-graded-hilbert-function asserts existence of an eventual polynomial for finite graded modules, while the new graded lemma assumes an eventual polynomial and proves degree and emptiness. The existing Snapper node is reused as the future field construction's input rather than restated as a family assertion. Its source misprints the theorem tag as 0BEL; the correct local tag map is 0BEM, used in the new source. No unrelated node was edited to correct that existing typo.

## Verification

Initial recovered-version dry run: exited 1 because report.md lacked Review by Q42. Repaired standalone server review_split: PASS. Full repaired dry run: OK (not pushed), preflight passed at 0dc32e5321d. The item statement and all five verbatim citation quotes were checked locally without running any forbidden checker. No local check_dag.py, review_split.py or preflight_delivery.py was run.

## Unfinished work

The requested one-level split is complete. The three new unsplit statements are intentionally separate future tasks under the human's re-split instruction, with no proof bodies. No stage-2 or stage-3 work is included.

## Exact returned argument retained for next workers

### Returned step 1

The given embedding and quasi-compactness make $f:Z\to T$ projective in [def-pc-projective-morphism], hence proper by [lem-pc-projective-proper]. Its finite presentation is a hypothesis. For any field-valued point $\operatorname{Spec}K\to T$, [lem-weil-pbc-closed-immersion-base-change] gives $X=Z_K\hookrightarrow\mathbf P^n_K$, so the same projective-proper result applies to $X$. A field is Noetherian (its only ideals are zero and itself); therefore [lem-weil-pbc-finite-type-over-noetherian] makes $X$ Noetherian. The structure sheaf is quasi-coherent of finite type, so [pqf-lem-coherent-ft-locnoeth] makes $\mathcal O_X$ coherent. These observations justify the properness and coherence hypotheses used below, without imposing a Noetherian condition on $T$.

Uses: def-pc-projective-morphism, lem-pc-projective-proper, lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-finite-type-over-noetherian, pqf-lem-coherent-ft-locnoeth.

### Returned step 2

For each $d\in\mathbf Z$, construct $\mathcal F_d=\mathcal O_Z(d)$ by restricting the rank-one twist of [def-pc-projective-space-twist], over each affine open of $T$. Its transition functions are $(z_i/z_j)^d$. Thus these local constructions agree on base restrictions; their local bases show $\mathcal F_d$ is finitely presented. At every $x\in Z$, $(\mathcal F_d)_x\cong\mathcal O_{Z,x}$ as $\mathcal O_{T,f(x)}$-modules. This module is flat by [def-weil-flat-morphism], so $\mathcal F_d$ is flat over $T$. On tensoring the same free bases along any base map, their transition functions become the images of $(z_i/z_j)^d$; hence module pullback [def-pc-module-pullback] gives exactly the twist on the base-changed embedded scheme. Multiplication of the transition functions also identifies $\mathcal F_d$ with the signed tensor power of $\mathcal F_1$ (dual powers when $d<0$).

Uses: def-pc-projective-space-twist, def-weil-flat-morphism, def-pc-module-pullback.

### Returned step 3

Apply [lem-sfb-proper-flat-sheaf-euler-local-constancy] to $f$ and each $\mathcal F_d$. It supplies a locally constant function $E_d(t)=\chi(Z_{\kappa(t)},\mathcal O(d))$ on $T$. Its arbitrary-base-change clause, applied to $\operatorname{Spec}K\to T$ with image $t$, gives
$$E_d(t)=\chi(Z_K,\mathcal O_{Z_K}(d)).$$
In particular this equality holds for $K=\overline{\kappa(t)}$. We will use it also for field-valued points obtained by composing a geometric point of an arbitrary $T'$ with $T'\to T$.

Uses: lem-sfb-proper-flat-sheaf-euler-local-constancy.

### Returned step 4

Fix any field-valued point as in step 1 and its embedded scheme $X$. Apply [lem-sc-snapper-numerical-polynomial] with $r=1$, $\mathcal F=\mathcal O_X$, and the invertible module $\mathcal L=\mathcal O_X(1)$. Step 2 identifies its signed powers with $\mathcal O_X(d)$. Thus there is a numerical polynomial $Q_X\in\mathbf Q[x]$ with $Q_X(d)=\chi(X,\mathcal O_X(d))$ for all $d\in\mathbf Z$. By [lem-sfb-projective-closed-subscheme-homogeneous-ideal], write $X=\operatorname{Proj}(K[z_0,\ldots,z_n]/J)$. By [lem-sfb-projective-coordinate-ring-euler-polynomial], for $A=K[z_0,\ldots,z_n]/J$ one has $\dim_K A_d=Q_X(d)$ for all sufficiently large $d$. The same comparison holds for any homogeneous ideal defining $X$. Two rational polynomials agreeing at every sufficiently large integer are equal: their difference has infinitely many roots. This proves existence, uniqueness, and independence of the chosen coordinate presentation. Numerical means integer-valued at every integer, as supplied by the Euler polynomial theorem.

Uses: lem-sc-snapper-numerical-polynomial, lem-sfb-projective-closed-subscheme-homogeneous-ideal, lem-sfb-projective-coordinate-ring-euler-polynomial.

### Returned step 5

The degree bound is elementary from the coordinate presentation in step 4. Monomials of total degree $d$ span $K[z_0,\ldots,z_n]_d$, with $\binom{d+n}{n}$ such monomials, so
$$0\le Q_X(d)=\dim_K A_d\le\binom{d+n}{n}\quad(d\gg0).$$
If $Q_X\ne0$, eventual nonnegativity forces its leading coefficient $a$ to be positive. Writing its degree as $r$, for large positive $d$ its lower terms have absolute sum at most $(a/2)d^r$, so $Q_X(d)\ge(a/2)d^r$. For $d\ge1$, the upper bound is at most $(n+1)^n d^n$ (also for $n=0$). If $r>n$, the two inequalities would bound $d^{r-n}$ by $2(n+1)^n/a$ for all large integers, a contradiction. Thus $r\le n$.

Uses: (elementary).

### Returned step 6

If $X=\varnothing$, all the cohomology spaces in the Euler characteristic are zero, so $Q_X=0$. Conversely, if $Q_X=0$, step 4 gives $A_d=0$ for all $d\ge d_0$, after increasing $d_0$ to at least one. In particular each $z_i^{d_0}=0$ in $A$. Localizing at $z_i$ therefore gives the zero ring, whose degree-zero spectrum is empty. These $n+1$ standard Proj charts cover $X$ by [def-pc-proj], so $X=\varnothing$. This argument works over every field and for nonreduced schemes. It also permits the unit ideal $J$ and the zero graded ring.

Uses: def-pc-proj.

### Returned step 7

For a geometric fibre set $P_t=Q_{Z_{\overline{\kappa(t)}}}$. Steps 3--5 give $\deg P_t\le n$ when nonzero and $P_t(d)=E_d(t)$ for every integer $d$. Fix $t$. For each $d=0,\ldots,n$, step 3 supplies an open neighbourhood $U_d$ of $t$ on which $E_d$ is constant. On the finite intersection $U=\bigcap_{d=0}^nU_d$, every $P_u-P_t$ has degree at most $n$ and has the $n+1$ distinct roots $0,\ldots,n$, so it is zero. Therefore $u\mapsto P_u$ is constant on $U$. The argument includes zero polynomials and $n=0$, when one value suffices; it uses no single uniform Serre-vanishing bound on the family.

Uses: (elementary).

### Returned step 8

Let $h:T'\to T$, $t'\in T'$, $t=h(t')$, and $K'=\overline{\kappa(t')}$. The composite $\operatorname{Spec}K'\to T'\to T$ is a field-valued point with image $t$. By the fibre-product universal property [def-pc-fibre-product], its pullback of $Z$ is exactly $(Z\times_TT')_{K'}$, with the pulled-back embedding and twist of step 2. Its Euler polynomial from step 4 has, by step 3, value $E_d(t)=P_t(d)$ at every integer $d$. Polynomial uniqueness therefore identifies it with $P_t$. This uses arbitrary base change of Euler characteristics, not any comparison between the two chosen algebraic closures. Taking $T=\operatorname{Spec}k$ also shows that the zero-polynomial criterion of step 6 applies to every projective scheme over a field, as asserted.

Uses: def-pc-fibre-product.

## Previous NR report retained

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-projective-hilbert-polynomial-locality.json — statement, split into eight proof steps; not a Mathlib leaf.
- citations.json — all fourteen step-to-node citations, with verbatim statements.
- No new DAG nodes and no Mathlib leaves were created. No unit record was changed: this is a prerequisite, not the unit's key statement.

## Attachments

None. I searched lean/WeilConjectures for the exact item id and for Hilbert-polynomial names and docstrings. Modules/HilbertPolynomial.lean and Modules/Ample.lean address individual proper schemes; no project declaration found gives this item's family-locality, arbitrary-base-change, coordinate-polynomial and empty-fibre clauses together. Existing closed nodes are cited where applicable.

## WANTED

None. All mathematical sources used for this split are present in literature/stacks-project/.

## Findings and changes

The item was statement-only, and its sandbox contained no earlier split, report or searches. Its statement is correct and is retained verbatim. I added statement dependencies for the projective-space, geometric-fibre, residue-field, twist, pullback, Proj and Euler-characteristic notions that its text already uses. I preserved all existing fields and searches, then appended the actual NR msearch results in searches.jsonl. No Lean was written and no compiler/build tool was run.

The whole-DAG search for 0B9T, 08AC, 08AE, Hilbert polynomial and Euler local constancy found the existing proper-flat Euler node, coordinate/Euler comparison node, homogeneous-ideal node and numerical-polynomial nodes. The blueprint searches for Hilbert polynomial and projective proper were read. The imported blueprint Hilbert-polynomial lemma concerns one proper scheme with an ample line bundle, not families. I reuse the stronger existing Snapper node instead of introducing a projective-field-polynomial node. All supplementary facts in steps 2, 5--8 are direct arguments, not new nodes.

The source place of existing lem-sc-snapper-numerical-polynomial incorrectly calls its theorem Tag 0BEL. The local Stacks tag map makes 0BEL the section and 0BEM the lemma-numerical-polynomial-from-euler theorem. I read and use that theorem at varieties.tex:10195. Its mathematical statement matches the cited node exactly; I have not edited the other worker's node.

The inherited blueprint.from.node is null, and blueprint_refs.py ancestor reports None. I retained the existing via chain and its explicit Hilbert-construction place rather than inventing an ancestor. The current unit text was read at literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and the stored chapter/unit records were read. This split remains the numerical prerequisite under the existing Hilbert-representability branch, without changing a unit or chapter route.

## Not duplicates

No new nodes. The reused coordinate/Euler comparison is narrower than the item: it gives eventual equality for a single homogeneous quotient, without numerical-polynomial existence, local constancy or family base change. The reused Euler theorem is broader in sheaves but does not itself construct or identify Hilbert polynomials.

## Review by NR

I read perfect.tex, Tag 0B9T, lemma-chi-locally-constant-geometric, including its proof through perfect direct images. Its hypotheses are proper finite presentation and a finitely presented sheaf flat over the base; the base is arbitrary. I read varieties.tex, lemma-numerical-polynomial-from-euler (actual Tag 0BEM), the statement and proof setup of 08AC and the Serre-vanishing proof of 08AE; constructions.tex 03GL, lemma-closed-in-projective-space; and coherent.tex 0AG7, lemma-recover-tail-graded-module. These give the fibre polynomial and its comparison with the homogeneous coordinate ring. I also read morphisms.tex lemma-locally-projective-proper (01WC), lemma-finite-type-noetherian (01T6), and coherent.tex lemma-coherent-Noetherian (01XZ) for the auxiliary hypotheses. There are no new node statements to check against sources.

For step 1 I opened all five cited nodes. The projective definition requires an embedding and quasi-compactness, supplied by the item; for a field fibre its finite standard affine chart cover also supplies quasi-compactness. The projective-proper node actually asserts properness. The closed-immersion base-change node supplies the fibre embedding. The finite-type-over-Noetherian node applies only to the field fibres, not to arbitrary T. The coherent/finite-type equivalence then applies to the structure sheaf on that Noetherian fibre. A field has just two ideals, which verifies the Noetherian base hypothesis here.

For step 2 I checked the full statements of the twist, flat-morphism and module-pullback nodes. The twist node really gives the local free bases and transition functions, so the argument multiplies or tensors those functions explicitly to obtain powers, dual powers, and arbitrary base-change compatibility. Local free rank one makes the sheaf finitely presented; its stalk is the structure stalk, which is flat over the base by the given flat morphism. No coherence or Noetherian assertion about the total Z is used.

For step 3 I opened lem-sfb-proper-flat-sheaf-euler-local-constancy and checked both clauses, verbatim in citations.json. Step 1 gives proper finite presentation and step 2 gives the required sheaf finite presentation and base flatness. The base-change clause applies directly to any field-valued point, including its algebraic closure, giving the asserted geometric Euler values. There is no assumption that coherent cohomology dimensions individually remain constant.

For step 4 I checked each of the three cited statements: Snapper gives a numerical polynomial at all integers for a coherent module and invertible powers on a proper field scheme; 03GL gives a homogeneous ideal for every closed subscheme; the coordinate/Euler node gives eventual equality for any such homogeneous ideal, even an unsaturated ideal. The structure sheaf coherence comes from step 1, and invertibility/power identification comes from step 2. The infinite-root argument establishes uniqueness and presentation independence explicitly. This step takes only the statements of its citations, not their internal constructions.

Step 5 is the elementary monomial count and a written leading-coefficient comparison. It proves the uniform degree bound n without needing dimension theory or a new polynomial-growth lemma. Step 6 uses exactly the standard chart description in def-pc-proj. Vanishing of every high graded piece forces a power of every coordinate to vanish; every localization chart is therefore zero. This proves the nonempty direction without importing positivity of ample Hilbert degree. The empty direction follows from zero cohomology of the empty scheme.

Steps 7 and 8 use results already established in this item's preceding steps. Step 7 takes the finite intersection of the n+1 Euler-constant neighbourhoods, and the root bound then proves equality of the polynomials. Step 8 cites the fibre-product universal property, and applies step 3 to the composite geometric field point over T, giving equality of all polynomial values. It neither assumes an embedding between chosen algebraic closures nor needs a separate flat-field-extension comparison theorem. I checked that the fibre-product node supplies precisely the needed universal property.

Small cases checked: n=0 needs one value and gives a constant polynomial; the empty scheme and unit homogeneous ideal give the zero polynomial; a nonempty zero-dimensional nonreduced fibre has positive eventual graded dimensions and cannot be declared empty by the argument; unsaturated ideals are allowed by the coordinate/Euler statement; nilpotents and disconnectedness in T do not enter the finite-neighbourhood intersection; T and T' may be empty, non-Noetherian, nonreduced, or non-quasi-compact. All steps are shorter than 2000 characters. No step hides a separate comparison or standard-lemma invocation. Generic off-unit statement tools are declared in split_report.tool_uses.

The actual search results were read: Polynomial.hilbertPoly and preHilbertPoly are constructions from rational power-series coefficients (Mathlib/RingTheory/Polynomial/HilbertPoly.lean:18--44), whose TODO still excludes graded-module Hilbert polynomials; they do not assert the scheme-family theorem. Module.isLocallyConstant_rankAtStalk (Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean:224--228) concerns a finitely presented flat module, not proper coherent cohomology. Other hits concern flatness/base-change permanence or unrelated Euler characteristics. A second LeanFinder wording returned the same rank theorem and unrelated condensed-module results, so there is no item-level Mathlib match in these results. I did not create leaves from partial matches.

## Unfinished work

None in the requested one-level split. The existing unsplit input nodes remain their owners' work; no existing dependency was modified.
