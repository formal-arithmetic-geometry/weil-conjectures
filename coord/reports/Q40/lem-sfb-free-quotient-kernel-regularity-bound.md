## Promotion-return repair, 2026-10-23

The current return is the landing refusal “completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it)”. This delivery continues the retained four-child split, rather than submitting the ten-step Q25 side completion. The retained report.md was empty after an interrupted previous attempt; I reconstructed it from the saved report generator, original Q25 proof and retained prior report, preserving the original argument texts, citations and logged searches. The sections below record that earlier mathematical repair; this section records the current promotion-return repair.

I compared work/base-q25.json with the current read-only repository item: all fields are identical. I then compared the retained delivery against the current item: only proof, proof_deps, proof_origin, mathlib_searches and split_report differ. Thus the statement, statement dependencies, Lean record, reviewed_lean, reviewed, blueprint and maintainer-owned tool_uses are current and preserved. Delivery tooling will construct the commit on the current server DAG. The released stage-1 repair note still requires the short assembly and at least two separate statement-only tasks, and the retained split supplies four. This is substantive re-split work beyond the old Q25 completion.

I re-read the current full statements of lem-sfb-coherent-regular-hyperplane-restriction and lem-sfb-m-regular-coherent-sheaf-consequences, the two existing proof citations. The first still supplies a single hyperplane for the finite family F,K,O^r,O_X, injectivity in every twist, coherent pullbacks, and H=P^(n-1) with compatible twists. The second still propagates regularity for n>=0, including the P0 induction case. Neither statement requires a change to the retained assembly. I also read all four child statements against Stacks varieties.tex 08AG, 08A4 and 08AB, with the original Q25 argument and its source-error correction open. Every citations.json quote is a literal substring of the current overlaid statement. No cited statement changed against the retained quotes; no source hypothesis, induction shift or field-uniformity adjustment is needed.

The initial required dry run stopped because report.md lacked the required Review by Q40 section. That omission is repaired here and in the reconstructed review below. The existing searches.jsonl results were read, including the two candidate Mathlib ingredients for restriction: they do not state the whole geometric lemma. No search was repeated or newly claimed, because no child statement or search question changed. No Lean, compiler or Lake command was used.

## Worker report

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-free-quotient-kernel-regularity-bound.json: repaired six-step assembly, 1948 proof-text characters. The statement and statement dependencies are unchanged; current main's Lean and maintainer-owned fields are retained.
   - dag/nodes/sec-six-functors-basics/lem-sfb-projective-quotient-field-extension.json: new statement-only unsplit node, no Mathlib match; coherent quotient transport, twisted cohomology base change, Euler invariance and regularity descent (original step 2).
   - dag/nodes/sec-six-functors-basics/lem-sfb-hyperplane-free-quotient-euler-difference.json: new statement-only unsplit node, no Mathlib match; exactness of the restricted quotient and its Euler finite difference (original steps 3-4).
   - dag/nodes/sec-six-functors-basics/lem-sfb-hyperplane-cohomology-tail-bound.json: retained statement-only unsplit node, no Mathlib match; arbitrary coherent module, hyperplane restriction regularity and cohomology tails (original steps 5-8).
   - dag/nodes/sec-six-functors-basics/lem-sfb-free-quotient-first-cohomology-estimate.json: new statement-only unsplit node, no Mathlib match; Euler and section estimates giving the initial H1 bound (original step 9).
   - citations.json: one full verbatim cited statement for each item step/node pair.
2. Attachments: none. The exact blueprint-tag and declaration search under lean/WeilConjectures finds no complete declaration. Searches by hyperplane, regularity, Castelnuovo and Mumford find other notions and projective-line results. The existing Sheaf.AlgebraicGeometry.FreeQuotientKernelRegularityBound declaration at line 77 ends in sorry, so cannot attach. Upstream's generic EulerChar results do not supply the all-dimensional quotient regularity theorem or any complete new geometric statement.
3. WANTED: none. All source passages used are local Stacks sources.
4. Repair: the maintainer returned the previous Q40 delivery for D2 and the released re-split note's minimum-node/no-shortening requirements. Its one extracted tail lemma was correct, but field descent, restricted-quotient exactness, Euler difference and the numerical initial H1 estimate had been compressed in place. This repair extracts all those arguments instead of defending the shorter text. There are four independent tasks in total. The field task has several transport assertions, the restriction task combines the stalk-exactness and cohomological Euler argument, the tail task has higher-degree propagation and the plateau argument, and the numerical task computes Euler and H1 bounds. They are comparable constituent tasks, none restating uniform regularity or an item clause. The numerical node is extracted under the explicit repair order requiring original step 9 to become a task; it is not a new standalone arithmetic lemma. The full original arguments, including the local chases, are retained verbatim below and assigned to these tasks. Only the base case, invocation of induction, bound choices and final shift arithmetic remain in the assembly.
5. Unfinished: the four new nodes deliberately have proof=[], proof_deps=[], proof_origin=null and status unsplit, as ordered. Subsequent workers can prove them independently. No Lean was written or compiled. No repository or launcher file was edited and no repository git command was run.

## Repair mapping and preservation of the original work

The repair note explicitly preserves the statement and proof route. I compared the retained returned sandbox with the live Q25 ten-step node and the released repair note before editing. The first required dry run completed at cc449c364ea with preflight OK, demonstrating that mechanical acceptance alone did not repair the mathematical work-distribution finding. I retained that material, the existing search log and report, then rebuilt the item from current main so later Lean attachments and reviews are preserved.

- Original step 1 is retained verbatim as assembly step 1: simultaneous induction, n=0, Delta P, the induction bound and b=max(1,m').
- Original step 2 is assigned in full to projective-quotient-field-extension: exact scalar extension on charts, finite presentations, twist transitions, cohomology base change, finite dimensions, Euler invariance and vanishing descent.
- Original steps 3-4 are assigned to hyperplane-free-quotient-euler-difference. The existing common hyperplane theorem still supplies the same single hyperplane for F, K, O^r and O_X. The new task carries the restricted-quotient stalk chase and the Euler difference, while assembly step 3 applies the induction hypothesis and existing regularity propagation on H. No induction hypothesis has been put inside a new lemma.
- Original steps 5-8 are assigned in full to the retained hyperplane-cohomology-tail-bound: higher-cohomology injections, finite H1 dimensions and surjections, lifting products of sections to propagate a plateau, eventual Serre vanishing and the strict-drop count.
- Original step 9 is assigned in full to free-quotient-first-cohomology-estimate: twist exactness, the monomial count, Euler additivity, sections injectivity, and h_b<=P(b). Assembly step 5 only applies the estimate and names N.
- Original step 10 is retained in substance in assembly step 6, with both shift inequalities, field descent, parameter dependence and the vacuous case explicit.

The old arguments have not been replaced by proof sketches inside new statements. Their complete texts are preserved below for each future worker and independent reviewer; each new node states precisely the independently provable conclusion of its assigned argument. This satisfies the statement-only requirement while preserving all source work for review.

## Sources and small-case checks

I read varieties.tex Tag 08AG (lemma-bound-quotients-free), lines 6855-6997, in full, including the exact hyperplane diagram, the middle cohomology paragraphs, and the last numerical paragraph. For the field node I also read 08A4 (lemma-m-regular-extend-base-field, lines 6619ff) and 08AB (lemma-euler-characteristic-extend-base-field, lines 6260ff). They explicitly give regularity equivalence and Euler invariance under arbitrary field extensions; the local exactness and finite-presentation details in original step 2 supplement them. No assumption that the fields be algebraically closed is introduced. The field node works for the identity extension, k(u) over a finite field, n=0 (regularity range empty, finite vector spaces on Spec k), zero modules, and every integer twist.

For the restriction node I read the first part of 08AG through its induction application, with 08A0 (lemma-exact-sequence-induction), 089Z (lemma-hyperplane), and 0EGK (remark-exact-sequence-induction-cohomology). The new lemma assumes the hyperplane is given; it does not claim one exists over a finite field. Injectivity on F is essential to left exactness of restriction. At a local equation x, A intersect xB=xA follows because x is injective on C; the original full chase is preserved below. Its Euler difference comes from the F hyperplane sequence and the finite long exact sequence, not from a false assumption that pullback is always left exact. Test cases: F=0 and K=O^r; K=0 and F=O^r; a skyscraper away from H, for which F_H=0 and the constant Euler polynomial has zero difference; n=1 and H=P0. A skyscraper on H violates the regularity-on-F hypothesis, as it should. For n=1 the restricted regularity condition is empty and the exact quotient remains meaningful.

For the retained tail node I checked 08AG's higher-cohomology, surjective H1 and plateau paragraphs, with 08A3 (definition-regularity), 08A6 (lemma-m-regular-up), 08A7 (lemma-m-regular-multiply) and 0EGK. The supplied hyperplane makes the infinite-field assumption unnecessary. The zero sheaf, a skyscraper away from H, O, and E=O(-D) on P1 at any integer m satisfy the claimed thresholds. On P1, h=max(D-m-1,0), so m+h reaches the actual H1-vanishing threshold when it is needed; this includes m<0 and h=0. Torsion on H is correctly excluded by injectivity. The full plateau proof including the O_X linear-form restriction argument remains below.

For the numerical node I read 08AG's final paragraph together with the statement of the existing projective-twist cohomology node. Here n>=1 and b>=1 guarantee that the monomial count is C(n+b,n) and all positive cohomology of O(b) vanishes. The lemma assumes only the higher cohomology of K(b) needed to turn its Euler characteristic into h0-h1. It does not assume first cohomology vanishes. When K=0 it reads 0<=chi(F(b))=rC; when F=0 it gives h1=0; for O->O_D on P1 of length D, h1(K(b))=max(D-b-1,0)<=D=chi(F(b)). A negative value P(b) is excluded automatically by the inequality whenever a quotient satisfying the hypotheses exists. There is no assumption that the bound be uniform in the sheaf before induction is applied.

## Source error retained

The imported theorem is true and its statement is unchanged. The source proof's last regularity bound m'+dim H1(K(m')) misses the regularity shifts: on P1 with O->O_D, length(D)=2, K=O(-2), one may take m'=0 on H=P0 and h1(K)=1, but K is not 1-regular. Its claim that H0(O(m')) is zero for every m'<=0 also fails at zero. The repaired proof retains the previously accepted b=max(1,m'), N=max(0,ceil P(b)), a=b+N+n+1. The extracted numerical node uses b>=1, and the tail node states cohomology thresholds rather than the erroneous final regularity assertion. No new statement dispute or target change is needed.

## Mathlib and duplicate searches

All retained searches.jsonl entries were read and reused; the queries have not changed for the item and retained tail node, so those searches were not repeated. For each of the three additional nodes I ran msearch.py leanfinder, loogle, grep and leansearch plus a second semantic phrasing, recording the exact query and actual returned summary in that node. All services answered. The restriction searches gave two plausible ingredients, which I checked in source: QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last, Mathlib/RingTheory/Regular/IsSMulRegular.lean:173, is module exactness modulo one scalar, and Polynomial.hilbertPoly_mul_one_sub_succ, Mathlib/RingTheory/Polynomial/HilbertPoly.lean:220, is an identity for the polynomial associated to a rational power series. Neither states the geometric restriction/Euler lemma; that lemma requires coherent pullback and sheaf cohomology as well. Other hits are Proj constructors, local free loci, projective-object Ext vanishing, cotangent cohomology, scalar-extension module operations and unrelated numerical bounds. None is a one-line specialization giving the new statements. The extra grep queries locating those two ingredients are also recorded in the restriction node.

I searched the entire DAG by the tags 08AG, 08A4, 08AB, 08A0, 089Z and 0EGK, their Stacks labels, and keywords for Euler hyperplane differences, regularity under field extension and kernel H1 estimates, then read the plausible statements. blueprint_refs.py searches for field extension, Hilbert polynomial, hyperplane and regularity covered all imported blueprint chapters. Its field-extension hits concern curves, dimension and arithmetic coefficients; the three Hilbert-polynomial hits concern ample line bundles on proper schemes; its sole hyperplane hit is a Kummer/tower-class statement. None states these extracted lemmas. The inherited blueprint ancestor is null; every new from field copies that exact inherited chain with this item prepended to via, and names the source paragraph it serves. same_as=[] is the result of those searches, not a claim that unrelated keyword hits were absent.

## Not duplicates

lem-sfb-projective-quotient-field-extension vs lem-pc-degree-base-change: the existing node concerns degrees of invertible modules on proper schemes of dimension at most one; this child concerns arbitrary coherent modules on projective n-space.

lem-sfb-projective-quotient-field-extension vs lem-pc-finrank-field-base-change: the existing node is dimension invariance for finite vector spaces, without coherent sheaves, twists, exact quotients or regularity.

lem-sfb-projective-quotient-field-extension vs lem-sc-flat-base-change-coherent: the existing node gives cohomology base change, but not coherent exact quotient transport, twist comparison, Euler invariance and regularity reflection as a geometric package.

lem-sfb-projective-quotient-field-extension vs lem-sfb-coherent-regular-hyperplane-restriction: the existing node chooses a common hyperplane and gives individual multiplication sequences and cohomology comparison; this child does not duplicate that existence assertion and supplies a separate quotient, transport, tail or numerical conclusion.

lem-sfb-projective-quotient-field-extension vs lem-sfb-free-quotient-kernel-regularity-bound: the existing item asserts one regularity bound from n,r,P for every field and quotient; this child is a conditional input with explicitly given geometric data and has no uniform existence conclusion.

lem-sfb-projective-quotient-field-extension vs lem-sfb-hilbert-uniform-section-bound: the existing node concerns ideals in flat projective families and uniform generation with base change; this child concerns a single coherent module or quotient over a field.

lem-sfb-projective-quotient-field-extension vs lem-sfb-m-regular-coherent-sheaf-consequences: the existing node assumes regularity on the ambient projective space and concludes propagation, generation and multiplication; this child does not assume ambient regularity.

lem-sfb-hyperplane-free-quotient-euler-difference vs lem-sc-hilbert-difference: the existing node assumes support equal to X and no embedded associated points and uses regular meromorphic sections and denominator ideals; these hypotheses need not hold for F here, and it does not give the exact restricted free quotient.

lem-sfb-hyperplane-free-quotient-euler-difference vs lem-sfb-coherent-hyperplane-restriction-sequence: the existing node chooses a hyperplane for one module and controls its cohomology sequence and multiplication compatibility; this child does not repeat that choice and has additional quotient, transport, tail or numerical data.

lem-sfb-hyperplane-free-quotient-euler-difference vs lem-sfb-coherent-regular-hyperplane-restriction: the existing node chooses a common hyperplane and gives individual multiplication sequences and cohomology comparison; this child does not duplicate that existence assertion and supplies a separate quotient, transport, tail or numerical conclusion.

lem-sfb-hyperplane-free-quotient-euler-difference vs lem-sfb-free-quotient-kernel-regularity-bound: the existing item asserts one regularity bound from n,r,P for every field and quotient; this child is a conditional input with explicitly given geometric data and has no uniform existence conclusion.

lem-sfb-hyperplane-free-quotient-euler-difference vs lem-sfb-hilbert-uniform-section-bound: the existing node concerns ideals in flat projective families and uniform generation with base change; this child concerns a single coherent module or quotient over a field.

lem-sfb-hyperplane-free-quotient-euler-difference vs lem-sfb-m-regular-coherent-sheaf-consequences: the existing node assumes regularity on the ambient projective space and concludes propagation, generation and multiplication; this child does not assume ambient regularity.

lem-sfb-hyperplane-cohomology-tail-bound vs lem-sfb-coherent-regular-hyperplane-restriction: the existing node chooses a common hyperplane and gives individual multiplication sequences and cohomology comparison; this child does not duplicate that existence assertion and supplies a separate quotient, transport, tail or numerical conclusion.

lem-sfb-hyperplane-cohomology-tail-bound vs lem-sfb-free-quotient-kernel-regularity-bound: the existing item asserts one regularity bound from n,r,P for every field and quotient; this child is a conditional input with explicitly given geometric data and has no uniform existence conclusion.

lem-sfb-hyperplane-cohomology-tail-bound vs lem-sfb-hilbert-uniform-section-bound: the existing node concerns ideals in flat projective families and uniform generation with base change; this child concerns a single coherent module or quotient over a field.

lem-sfb-free-quotient-first-cohomology-estimate vs lem-pqf-finite-free-kernel-h1-vanishing: the existing node assumes H1 vanishing for every quasi-coherent ideal and concerns a map O^I to O; the present numerical estimate allows nonzero H1 and arbitrary coherent quotient F.

lem-sfb-free-quotient-first-cohomology-estimate vs lem-sfb-coherent-regular-hyperplane-restriction: the existing node chooses a common hyperplane and gives individual multiplication sequences and cohomology comparison; this child does not duplicate that existence assertion and supplies a separate quotient, transport, tail or numerical conclusion.

lem-sfb-free-quotient-first-cohomology-estimate vs lem-sfb-free-quotient-kernel-regularity-bound: the existing item asserts one regularity bound from n,r,P for every field and quotient; this child is a conditional input with explicitly given geometric data and has no uniform existence conclusion.

lem-sfb-free-quotient-first-cohomology-estimate vs lem-sfb-hilbert-uniform-section-bound: the existing node concerns ideals in flat projective families and uniform generation with base change; this child concerns a single coherent module or quotient over a field.

## Review by Q40

I re-read the released repair note and the actual returned finding, not merely the successful first dry run. The previous assertion that the sole substantive subargument had been extracted was wrong under this human instruction: the existing local chases and numerical calculation were exactly work the note required spreading. I corrected that by making three further tasks and mapping every original argument to one of four tasks. Each new node is self-contained, introduces its field, dimension, module maps, twists, cohomology and numerical data, and cites definition nodes in its statement. All are statement-only, with real Stacks tags and labels, logged searches, blueprint fields and no proof sketch embedded in the statement. The item is a six-step assembly under 3000 characters. The four statements have roughly comparable lengths and independent proof obligations. None asserts a uniform bound a(n,r,P), so D1/D2 are avoided. Original steps 1 and 10 only contain induction setup and concluding arithmetic; every intervening argument is now assigned to a child and retained verbatim below.

For assembly step 1 I checked simultaneous induction over all r,P and fields and the empty range for n=0. Step 2 uses exactly projective-quotient-field-extension's short exact coherent quotient assertion, its Euler equality for every twist and its regularity equivalence; L=k(u) is a field extension and infinite because its powers of u are distinct. The child does not construct a uniform bound; the assembly does. Step 3 reads the actual common-hyperplane statement: apply its finite family to F,K,O^r,O_X, retaining the Q25 review correction. It supplies all twisted multiplication injections, coherent restrictions and the identification H=P^(n-1). These satisfy the new restricted-quotient lemma's assumptions, in particular regularity of s on F. That lemma explicitly gives the short exact sequence and the finite-difference Euler polynomial, the two facts needed for the induction hypothesis. The m-regular consequences node explicitly works for dimension zero as well, hence raises m' to b even for n=1. No fact is taken from any of these nodes' proof fields.

Assembly step 4 uses both literal clauses of hyperplane-cohomology-tail-bound. The module K is coherent, n>=1, the same nonzero hyperplane is supplied, multiplication on K is injective in every twist, K_H is coherent and b-regular by step 3; these are precisely its hypotheses. Step 5 cites the numerical estimate, not an uncited Euler argument: it has the exact free quotient, b>=1 and the higher vanishing just obtained, and states 0<=dim H1(K(b))<=P(b). The ceiling/max inequality and parameter dependence follow directly. Step 6 checks separately a-1>=b+h_b and a-j>=b for 2<=j<=n. These inequalities feed the two actual tail conclusions, then the field lemma reflects the resulting a-regularity. No uniform Serre-vanishing threshold is assumed. The parameter choices and the final statement remain identical to the accepted Q25 route.

For C4, I opened every cited node's statement (the four children, common-hyperplane, regularity consequences), and citations.json quotes the complete literal statement for each pair. For C1, the item uses no hidden field, exactness, cohomological Euler or plateau lemma; each is now a named task with its exact hypotheses. The full child arguments copied below were also checked against the older generic projective-base-change, finrank, cohomology-finiteness/bound, Serre, twist-cohomology and Euler-additivity statements. Those old citations give exactly the operations used in the preserved arguments: properness for coherent base change, all-degrees base change rather than its O_X special case, finite dimensions for the dimension drop, and H1(O_X)=0 to lift linear forms. Ordinary pullback left exactness is never assumed. The new node statements add no hypotheses to the item because their conditional hypotheses are all established before invocation.

B1-B10: no unsplit proof steps or proof dependencies, every object and notion introduced, TeX serialized once, source tag/label checked in tags/tags, no false Mathlib match or fabricated searches, blueprint ancestry retained, and no completed project declaration overlooked. C1-C8: statement citations checked, proof-dependency union and quotes regenerated, no cycle through an induction hypothesis or source parent, chapter/unit unchanged, and no off-unit proof tool remains in the assembly. D1-D5: four genuinely different tasks, no restatement of the uniform conclusion, complete induction, no loose source paraphrase substituted for the work. E1-E7: tested identity/finite-field extension, P0/P1, zero modules, skyscrapers off/on H and O(-D), with hypotheses and shifts checked as above; preserved the known source-error correction. No item step exceeds 2000 characters. The original 1109-character plateau argument is retained intact as future work for its child, rather than hidden by a shortened item step.

## Original Q25 argument texts retained verbatim

### Original step 1 -> assembly step 1

Prove the assertion by induction on $n$, simultaneously for every $r\geq1$, every rational polynomial $P$, and every field. For $n=0$ the defining range $1\leq j\leq n$ is empty, so take $a=0$. For $n>0$ set $\Delta P(t)=P(t)-P(t-1)$ and choose the integer $m'$ supplied by the induction hypothesis for $(n-1,r,\Delta P)$. Put $b=\max(1,m')$. These choices precede any choice of field or quotient.

Original cited nodes: none (elementary).

### Original step 2 -> lem-sfb-projective-quotient-field-extension

We can work over an infinite extension $L/k$ (use $k(u)$ if necessary). Projective space is proper and commutes with base change. On each standard affine chart, pulling back the quotient sequence is tensoring its module sequence over $k$ with $L$; an exact sequence of $k$-vector spaces splits, so this tensor operation is exact. Finite presentations base change, so the pulled-back modules remain coherent; the transition functions $(T_i/T_j)^d$ show that twists pull back to the same twists. Flat coherent base change gives $H^q(\mathbf P^n_L,E_L(d))\cong H^q(\mathbf P^n_k,E(d))\otimes_kL$. The groups are finite-dimensional by projective coherent finiteness. Dimension invariance under field extension, and vanishing above $n$, show that the Euler polynomial remains $P$ and that every required vanishing descends. Thus a bound established over infinite fields, depending only on $n,r,P$, works over all fields.

Original cited nodes: lemma-nagata-projective-space-base-change-proper, lemma-nagata-projective-space-base-change-pullback, lem-sc-flat-base-change-coherent, lem-pc-finrank-field-base-change, lem-pc-projective-space-coherent-finiteness, lem-pc-projective-space-cohomology-bound.

### Original step 3 -> lem-sfb-hyperplane-free-quotient-euler-difference

Assume now $k$ infinite. Apply the common regular hyperplane lemma to the four coherent modules $\mathcal F,\mathcal K,\mathcal O^{\oplus r},\mathcal O_X$. It gives $i:H\hookrightarrow X=\mathbf P^n_k$, with $H\cong\mathbf P^{n-1}_k$, and, writing $F_H=i^*\mathcal F$, $K_H=i^*\mathcal K$, the twisted multiplication/restriction sequences for all four modules ($\mathcal O_X$ is included for its use at twist $1$ in step 7). Restriction of the original quotient sequence is exact:
$$0\to K_H\to\mathcal O_H^{\oplus r}\to F_H\to0.$$
Indeed, on a stalk trivializing the twists, write the original sequence $0\to A\to B\to C\to0$ and the local equation $x$ of $H$. If $a=xb$ belongs to $A$, the image of $b$ in $C$ is killed by $x$, hence is zero by injectivity of $x$ on $C$, so $a\in xA$. This proves $A/xA\to B/xB$ injective. If the image of $b$ in $C$ is $xc$, lift $c$ to $b'$; then $b-xb'$ lies in $A$, proving exactness in the middle. The quotient map is surjective. These stalk calculations identify the sequence with the indicated pullbacks.

Original cited nodes: lem-sfb-coherent-regular-hyperplane-restriction.

### Original step 4 -> lem-sfb-hyperplane-free-quotient-euler-difference; induction invocation and propagation stay in assembly step 3

The twisted hyperplane sequence for $\mathcal F$ identifies the cohomology of its pushed-forward quotient with the cohomology on $H$. Taking alternating dimensions in its long exact sequence gives
$$\chi(H,F_H(d))=\chi(X,\mathcal F(d))-\chi(X,\mathcal F(d-1))=\Delta P(d).$$
The sums are finite by projective coherent finiteness and the projective cohomology bound on $X$ and $H$. Therefore the induction hypothesis applies to the exact coherent quotient on $H$: $K_H$ is $m'$-regular. Regularity propagation and its positive-cohomology consequence give $H^q(H,K_H(d))=0$ for all $q>0$ and $d\geq b$. These statements also hold for $H=\mathbf P^0_k$ when $n=1$.

Original cited nodes: lem-sfb-coherent-regular-hyperplane-restriction, lem-pc-projective-space-coherent-finiteness, lem-pc-projective-space-cohomology-bound, lem-sfb-m-regular-coherent-sheaf-consequences.

### Original step 5 -> lem-sfb-hyperplane-cohomology-tail-bound

For $j\geq2$ and $d\geq b$, the hyperplane long exact sequence has the segment
$$0=H^{j-1}(H,K_H(d))\longrightarrow H^j(X,\mathcal K(d-1))\xrightarrow{s}H^j(X,\mathcal K(d)).$$
Thus these maps are injective. Serre vanishing makes their targets zero for all sufficiently large twists (the threshold may depend on $\mathcal K$). For any fixed $t\geq b$, compose the injections from twist $t$ up to such a twist. This proves $H^j(X,\mathcal K(t))=0$ for every $j\geq2$ and $t\geq b$.

Original cited nodes: lem-sfb-coherent-regular-hyperplane-restriction, lem-sfb-m-regular-coherent-sheaf-consequences, lem-pc-projective-space-serre-vanishing.

### Original step 6 -> lem-sfb-hyperplane-cohomology-tail-bound

Set $V_t=H^1(X,\mathcal K(t))$ and $h_t=\dim_kV_t$. These dimensions are finite. The hyperplane sequence and $H^1(H,K_H(d))=0$ for $d\geq b$ show that $s:V_{d-1}\to V_d$ is surjective for every $d\geq b$. Consequently $h_{d-1}\geq h_d$ in this range. In the next step we show that a plateau at an index $d>b$ forces both spaces to be zero.

Original cited nodes: lem-sfb-coherent-regular-hyperplane-restriction, lem-sfb-m-regular-coherent-sheaf-consequences, lem-pc-projective-space-coherent-finiteness.

### Original step 7 -> lem-sfb-hyperplane-cohomology-tail-bound

Suppose $d>b$ and $s:V_{d-1}\to V_d$ is injective. Exactness then makes the restriction $\rho_d:H^0(X,\mathcal K(d))\to H^0(H,K_H(d))$ surjective. The restriction $H^0(X,\mathcal O_X(1))\to H^0(H,\mathcal O_H(1))$ is also surjective: apply the hyperplane sequence for $\mathcal O_X$ (one of the four modules of step 3) at twist $1$, whose restriction term is $H^0(H,\mathcal O_H(1))$ by the identification $i^*\mathcal O_X(1)\cong\mathcal O_H(1)$, since $H^1(X,\mathcal O_X)=0$ by the twist cohomology calculation. Because $K_H$ is $d$-regular, its multiplication map from twist $d$ to twist $d+1$ is surjective. Express a section of $K_H(d+1)$ as a finite sum of products of sections in twist $d$ with linear forms. Lift each factor by the two restriction surjections. The sum of the lifted products restricts to the original section, because restriction commutes with multiplication. Thus $\rho_{d+1}$ is surjective, and exactness shows that $s:V_d\to V_{d+1}$ is injective. Repeating this implication gives injections at every subsequent twist. Serre vanishing then implies $V_{d-1}=0$ (and hence $V_d=0$).

Original cited nodes: lem-sfb-coherent-regular-hyperplane-restriction, lem-sfb-m-regular-coherent-sheaf-consequences, lem-pc-projective-space-twist-cohomology, lem-pc-projective-space-serre-vanishing.

### Original step 8 -> lem-sfb-hyperplane-cohomology-tail-bound

For every $d>b$ with $h_{d-1}>0$, the surjection $V_{d-1}\to V_d$ cannot be injective by the preceding step. Finite-dimensional linear algebra therefore gives $h_d\leq h_{d-1}-1$. Inductively $h_{b+t}\leq\max(h_b-t,0)$ for every integer $t\geq0$; once zero occurs all later spaces are zero by surjectivity. In particular $H^1(X,\mathcal K(t))=0$ for all $t\geq b+h_b$.

Original cited nodes: none (elementary).

### Original step 9 -> lem-sfb-free-quotient-first-cohomology-estimate

It remains to bound $h_b$ using only the fixed parameters. Since $b\geq1$, the projective-twist calculation gives $H^q(X,\mathcal O(b))=0$ for $q>0$ and $h^0(X,\mathcal O(b))=\binom{n+b}{n}$ (count degree-$b$ monomials in $n+1$ variables). Tensoring the original exact sequence with the invertible $\mathcal O(b)$ preserves exactness: locally it is the original sequence with a chosen rank-one basis. Additivity of Euler characteristic therefore gives
$$\chi(X,\mathcal K(b))=r\binom{n+b}{n}-P(b).$$
All cohomology of $\mathcal K(b)$ in degrees $\geq2$ is zero by step 5, so $h_b=h^0(X,\mathcal K(b))-\chi(X,\mathcal K(b))$. The injection $\mathcal K(b)\hookrightarrow\mathcal O(b)^{\oplus r}$ induces an injection on sections, hence $h^0(X,\mathcal K(b))\leq r\binom{n+b}{n}$. Combining the two formulas yields $0\leq h_b\leq P(b)$. Define the nonnegative integer $N=\max(0,\lceil P(b)\rceil)$, so $h_b\leq N$.

Original cited nodes: lem-pc-projective-space-twist-cohomology, lem-pc-euler-additive, pqf-def-cohomology.

### Original step 10 -> assembly step 6

Choose $a=b+N+n+1$. Then $a-1\geq b+N\geq b+h_b$, so step 8 gives $H^1(X,\mathcal K(a-1))=0$. For $2\leq j\leq n$ one has $a-j\geq b$, so step 5 gives $H^j(X,\mathcal K(a-j))=0$. This is precisely $a$-regularity. Every number in this construction depends only on $n,r,P$; step 2 descends the same vanishing to the original field. If no quotient with polynomial $P$ exists the assertion is vacuous, and the same formula still defines an integer.

Original cited nodes: none (elementary).

## Retained prior Q40 report (historical, superseded where corrected above)

## Worker report

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-free-quotient-kernel-regularity-bound.json: re-split item, seven steps, 2212 proof-text characters, unchanged statement; no Mathlib match. The existing source correction, searches, blueprint chain, statement dependencies and maintainer fields are preserved.
   - dag/nodes/sec-six-functors-basics/lem-sfb-hyperplane-cohomology-tail-bound.json: one new statement-only node, unsplit, no Mathlib match. It bounds twisted cohomology of an arbitrary coherent module from regularity of its hyperplane restriction and its initial H1 dimension.
   - citations.json: the full verbatim statement for every step/node citation.
2. Attachments: none. Searches of lean/WeilConjectures for the exact item tag and declaration name, Castelnuovo, Mumford, hyperplane and regularity found projective-line resolution statements, not this all-dimensions bound or the extracted cohomology estimate. The existing Sheaf statement ends in sorry and is not an attachment.
3. WANTED: none. The needed Stacks source is local.
4. The live item already had a reviewed Q25 split and an N8 Lean statement. I first preserved it unchanged and submitted the required dry run. The gate rejected it for being unchanged and for violating the human's 2026-10-21 re-split requirement (6671 proof characters, maximum 3000). This delivery follows that explicit diagnostic: it refines the existing argument rather than rebinding the stage-2 declaration. It preserves the correction accepted by the prior review: choose the common hyperplane for F, K, O^r and O_X. The target, item statement, chapter and unit route are unchanged.
5. Unfinished: the new cohomology-tail node is intentionally unsplit for a later stage-1 item. No argument is moved into a proof sketch in its statement.

## Source correction retained

Stacks varieties.tex, Tag 08AG, lemma-bound-quotients-free, closes with the asserted regularity bound m' + dim H1(K(m')). This misses the regularity shift: on P1, take the quotient O -> O_D for a degree-two effective divisor, so K=O(-2); one may take m'=0 on the hyperplane and h1(K)=1, but K is not 1-regular. Also H0(O(0)) is not zero, contrary to the source's sentence treating every nonpositive twist as zero. The existing split already corrected these proof estimates without changing the theorem. I retain b=max(1,m), N=max(0,ceil P(b)), a=b+N+n+1. The extracted node asserts the true cohomology thresholds t>=m for degrees >=2 and t>=m+h1(E(m)) for degree 1, not the source's final regularity estimate. No new statement dispute or change to the item is needed.

## New node, searches, and argument for its truth

I read varieties.tex Tag 08AG in full, particularly the middle paragraphs following the exact hyperplane diagram, as well as 08A3 (definition-regularity), 08A6 (lemma-m-regular-up), 08A7 (lemma-m-regular-multiply), and the hyperplane cohomology comparison in 0EGK. Once the hyperplane is supplied, the middle argument uses an arbitrary coherent E, not its embedding in a free sheaf or a polynomial. Thus the child is a genuine intermediate lemma with different input data. It is not the item's uniform conclusion, nor one of its clauses, and does not involve r or P.

For a regular hyperplane restriction G which is m-regular, propagation gives Hq(G(d))=0 for q>0 and d>=m, and multiplication on sections is onto in these twists. The hyperplane long exact sequence makes Hq(E(d-1))->Hq(E(d)) injective for q>=2; eventual Serre vanishing then gives zero for all twists >=m. For V_d=H1(E(d)), the maps V_(d-1)->V_d are surjective for d>=m. If one is injective for d>m, restriction of sections of E(d) is onto. Restriction of linear forms to H is onto (change linear coordinates so H is a coordinate hyperplane, or use H1(O_X)=0 and the hyperplane exact sequence). Express each section of G(d+1) as a sum of products of sections of G(d) and linear forms; lift both factors and multiply. This proves surjectivity of restriction at d+1 and hence injectivity of V_d->V_(d+1). Iterate and use eventual Serre vanishing to force V_(d-1)=0. Consequently a positive dimension at twist t>=m drops by at least one at twist t+1; after h=dim V_m steps all V_t vanish. This proves exactly the new statement, including its shifts. This argument is documented here for review; the child has no proof fields filled.

The field need not be infinite in the child, because the hyperplane is supplied in its hypotheses. Tested cases: E=0; a skyscraper avoiding H (G=0, all positive cohomology zero); n=1, E=O(-D), any integer m (the threshold m+max(D-m-1,0) is sufficient, including negative m and h=0); and E=O with a coordinate hyperplane. A sheaf with hyperplane torsion is excluded precisely by the injectivity hypothesis. The item retains n=0 separately, handles n=1 using the empty regularity condition on P0, and descends from k(u) for finite fields. F=0, zero kernel, unrealizable P and the length-two example do not change the bound or require another hypothesis.

I searched the full DAG for 08AG, lemma-bound-quotients-free, hyperplane, cohomology tails, plateau and strictly decreasing H1 dimensions, and the imported blueprint using blueprint_refs.py search for 08AG, regularity, Castelnuovo, hyperplane, decreasing, and cohomology.*twist. The matching geometric restriction and regularity-consequences statements were opened and reused. None supplies the conditional tail estimate. The inherited blueprint ancestor is null, as blueprint_refs.py ancestor confirms; the new node retains that chain with the item prepended to via and names the exact middle paragraphs of 08AG in from.place. There is no matching imported blueprint statement, so same_as remains empty.

All new searches ran through msearch.py and are recorded exactly in searches.jsonl and the node. Two semantic phrasings returned projective-object Ext vanishing, derived truncations, regular sequences and restrictions on structure sheaves. Loogle returned cohomology of K-projective complexes; grep in Mathlib/AlgebraicGeometry found no Castelnuovo, Mumford, mRegular or hyperplane hit. These do not state the geometric estimate for coherent sheaves. Fresh item searches also returned Proj constructions, local free loci, polynomial kernels and regular topology, with no uniform coherent-sheaf bound. No service was unavailable. Earlier item searches are retained as earlier evidence, without claiming that Q40 ran them.

## Not duplicates

lem-sfb-hyperplane-cohomology-tail-bound vs lem-sfb-free-quotient-kernel-regularity-bound: the child assumes a regular restriction for an arbitrary coherent module and gives cohomology thresholds in terms of an existing H1 dimension; the item must construct a single bound from n,r,P for all fields and quotients. Hyperplane induction and the numerical polynomial estimate remain in the item.

lem-sfb-hyperplane-cohomology-tail-bound vs lem-sfb-hilbert-uniform-section-bound: the latter concerns ideals in flat projective families over arbitrary schemes, uniform generation and base change; the child concerns a single coherent module over a field with a specified regular hyperplane restriction and no Hilbert polynomial or family.

The other text hits, projective-hilbert-polynomial-representability and coherent-regular-hyperplane-restriction, respectively represent the Hilbert functor and choose a common regular hyperplane; neither estimates the cohomology tail of a module whose restriction is already regular. The regularity-consequences node assumes E itself regular; the child assumes only its restriction regular and allows H1(E(m)) nonzero.

## Review by Q40

I checked B through E of delivery-errors.md against the item, the child and their source. I read the node statements of every citation, not merely their proof fields or tags. The child introduces its field, projective spaces, coherent modules, hyperplane, twists, pullback, integer m, regularity condition and finite H1 dimension, with definition nodes for those notions. Its file is statement-only with an 08AG tag/label source, exact logged searches, inherited blueprint chain and no Lean or compiler work. It is a non-elementary argument (the propagation of a plateau by lifting products), not a few-line corollary of the existing statements. It shares the source of the item but is not a rewording of its uniform conclusion.

Step 1 sets up simultaneous induction and handles the empty n=0 case. Step 2 cites the projective-space base-change identification and properness, the all-degrees flat coherent base-change statement (not just the O_X special case), finite cohomology, the dimension bound and scalar-extension dimension equality. These supply exactly the cohomology dimensions and vanishing descent used there. Tensor exactness follows from split k-vector-space sequences; local finite matrix presentations pull back and twists retain their transition functions. No algebraic closedness or uniform Serre threshold is used. The twist definition is explicitly cited for this last identification.

Step 3 uses the common hyperplane node for all four modules. Its statement gives coherent pullbacks, identification H=P^(n-1), injective multiplication, exact sequences and natural cohomology comparisons. Ordinary pullback is not assumed left exact: in a stalk, if xb is in A, injectivity on C forces b into A, proving A intersect xB=xA; the quotient chase gives the remaining exactness. The node also supplies the injectivity hypothesis needed for E=K in the new lemma.

Step 4 uses the same node's cohomology sequence to take alternating dimensions, with projective finiteness and cohomological boundedness on both X and H. It gets precisely Delta P. The restricted quotient has r free generators, is coherent, and satisfies all induction hypotheses. The regularity-consequences statement applies on H including P0 and permits raising m to b. Step 5 cites the new child's two actual vanishing clauses at b; it does not use any assertion from a proof of that child. The preceding steps establish every one of its hypotheses.

Step 6 uses the twist-cohomology statement at b>=1, giving dimension binomial(n+b,n) and positive-degree vanishing. Cohomology is additive (right derived functors of the additive sections functor), so finite free sums contribute r times this dimension. The locally rank-one twist preserves the quotient's exactness. Euler additivity applies on the proper X supplied in step 2, and pqf-def-cohomology explicitly states the long exact sequence, hence injection on sections. With degree >=2 vanishing from step 5 this yields h=h0-chi<=P(b). Nonnegativity is a dimension fact; N remains defined even for a polynomial with no realizable quotient.

Step 7 checks a-1>=b+h and a-j>=b for 2<=j<=n separately, giving exactly the item's regularity shifts; step 2 descends these same vanishings to the original field. All seven proof steps are below 2000 characters and total 2212, so the remaining elementary stalk, finite exact-sequence Euler sum, tensor and arithmetic arguments are visible. The new node carries the sole substantive extracted subargument. Generic tools retain their split_report.tool_uses justifications. All citations.json quotes are full literal statements of the cited nodes. No field owned by the maintainer is changed, and no node apart from the item and the new child is delivered.
