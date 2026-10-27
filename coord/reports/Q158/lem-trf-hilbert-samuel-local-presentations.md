# Repair of lem-trf-hilbert-samuel-local-presentations

## Files written

- lem-trf-hilbert-samuel-local-presentations: split; unchanged statement, five-step assembly (2288 characters).
- lem-trf-jet-level-topology-reachable-dcc: statement, unsplit, no Mathlib match; no proof steps or proof dependencies.
- lem-trf-common-power-hilbert-marking: statement, unsplit, no Mathlib match; no proof steps or proof dependencies.
- lem-trf-coefficient-test-sequence-propagation: statement, unsplit, no Mathlib match; no proof steps or proof dependencies.
- lem-trf-minimal-envelope-coefficient-comparison: statement, unsplit, no Mathlib match; no proof steps or proof dependencies.

## Attachments

None. The upstream WeilConjectures search for the item tag and Hilbert--Samuel terminology returned no declaration. Read the current Sheaf.AlgebraicGeometry.HilbertSamuelLocalPresentations and HilbertSamuelReachableLevels modules: their numerical and presentation declarations have sorry proofs. They cannot be attached as finished proofs. Existing Lean and maintainer review fields were retained from the current repository baseline. No Lean was written or compiled.

## Wanted sources

WANTED: Bierstone--Milman, Invent. Math. 128 (1997), 207--302, Chapter III, especially Corollary 3.20, Definition 6.2, Theorems 7.20--7.21, 9.2, 9.4, 9.6 and Lemma 9.3, for lem-trf-hilbert-samuel-local-presentations and all four new nodes.

WANTED: Bierstone--Milman--Temkin, arXiv:0905.3580, sections 5.2 and 6.1--6.3, for lem-trf-hilbert-samuel-local-presentations and all four new nodes.

## What was wrong and what changed

The return requests spreading 8619 characters of argument across independently claimable tasks, at least two new nodes, while keeping the parent statement and an assembly of at most 3000 characters. The sandbox contained only dispatch markers, with no retained node, report, citations, PDFs or search log. I copied the current live node into the sandbox and kept an exact original-node.json baseline; its source, citations, old searches and full nine-step proof are retained. Four new nodes have comparable statement sizes (2150, 2437, 2753, 2489 characters) and separate mathematical tasks. None is the whole item. No target, chapter or unit statement changed. No new statement dispute was found.

The source actually available is ILO VIII 2.3.11--2.3.13, printed pp.93--94. I extracted and read it. It refers to BM/BMT rather than proving the coefficient theorem. In particular 2.3.13 warns about equidimensional synchronization. The original claim that detailed BM/BMT PDFs were read in an earlier sandbox cannot be reproduced here: those PDFs are absent. They are WANTED, and the assembly is marked proof_origin.by=agent. The new nodes are statement-only with no proof_origin, as required. No SGA source is used.

## Remaining work

No repair task remains before delivery. The four new unsplit nodes are deliberately future workers' proof tasks, not assertions that their proofs are finished. Maintainer independent review remains the delivery protocol.

## Review by Q158

I read the item, chapter sec-trace-formula, unit sk-i-curve-zero, the recorded blueprint ancestor and the actual ILO referral. The historical desingularization branch remains unchanged. This is a re-split of that existing branch, not a replacement of the active contracting-correspondence proof. For the new numerical node I checked the source referral to BM 9.1--9.3/3.20 and the jet-control, Noetherian finite-type, submodule finiteness and smooth blowup geometry node statements. The matrix must be a presentation matrix, not generators of the module, and the threshold v-c+1 is correct for a v-row target. The finite set must use every coordinate up through a common first-difference bound. The reachable bound covers arbitrary finite histories and plateaus, not just consecutive drops.

For the common-power node I read the regular-coefficient and formal-transform statements in full. All five division/Jacobian hypotheses and the upper-neighbourhood hypothesis are retained through the coefficient datum definition. Positive weights divide b. Orders scale because the smooth associated graded ring is a polynomial domain. Raising e^{-m} times a coefficient to b/m divides by e^b, so no exceptional exponent is lost. I also read the smooth-pair coordinates, blowup-complement and strict-transform-over-complement statements; their precise roles are preserved in the argument allocation below. General locally constant centers are covered pointwise, and no global maximum is assumed for that nonincrease clause.

For the finite-test node I checked the formal-transform criterion: exceptional-intersection blowups require transverse boundary and use total pullback of X, not strict transform. The induction carries boundary equations as W-coordinates on N; it starts with empty boundary, appends each line zero section and each exceptional divisor in order, and preserves the five conditions at retaining-level points. The smooth-normal-form and jet-control statements give the summed level after r variables. The first differing coefficient retains its sign after summation, so equality and lexicographic order are reflected as well as preserved. Open restrictions use r=0. The statement treats different relative-dimension pieces separately.

For the minimal-envelope node I read the smooth-embedding comparison and transverse-suspension statements, not their names alone. Comparison supplies minimal envelopes, the transverse retraction, common etale pointed identifications and specified ideal pullbacks. Suspension supplies the explicit ideal and requires r>0 for exact order b. That positivity is restricted to the singular minimal germ with nonempty Taylor ideal; a regular codimension-zero germ has I=0 and infinite order. Earlier centers are intrinsic history data, not the new test boundary. This preserves the earlier maintainer correction preventing old boundary divisors from being reused as fresh test boundary.

Parent citation check: step 1 takes finite presentations, closed upper sets and reachable DCC exactly from the new jet-level node. Step 2 takes actual regular coefficient data from lem-trf-regular-hilbert-coefficient-data, and coherence, equality and one-step controlled transforms/nonincrease exactly from the common-power node. Step 3 takes all prefix cosupport identities, transverse ordering and smooth-pullback formula exactly from the finite-test node. Step 4 takes envelope existence, singular suspension and intrinsic history comparison exactly from the minimal-envelope node; steps 2--3 are applied within that envelope. Step 5 is a logical consequence of steps 1--3: equality locus empty plus nonincrease implies strict decrease. It hides no resolution existence assertion. citations.json copies the exact full statement used for each citation; no proof internals are substituted for statements.

Edge cases checked: q=0 in jets; c outside the matrix rank range; a singleton finite value set (choose q0=0); empty vertex list gives (0,1) with whole smooth support; the unit ideal has empty cosupport; r=0 suspension gives no finite-order conclusion; r=1 suspension of zero gives a normal generator of exact order b; Spec Q has constant sequence 1, while its line has n+1, so unsummed smooth invariance would be false; empty blowup centers do nothing; components contained in a center may disappear; arbitrary subsequences through plateaus are covered by reachable DCC. I also retained the previous regular/singular, total-transform, boundary-reset and finite-coordinate corrections. Every parent non-elementary step is below 2000 characters; the total is below 3000.

B--E audit: new nodes introduce all data and definition references, are statement-only, and have no proof sketch in their statements. Their sources are precise BM/BMT places behind the available ILO referral; no fabricated Stacks tag. Three search kinds plus LeanSearch and a second semantic phrasing were actually run per node, and every result was read. Hits on analytic Taylor series, general semicontinuity, Weierstrass orders, filtrations, Rees algebras and etale presentations do not state the new assertions. No Mathlib leaf was asserted. Full DAG keyword searches and whole-blueprint searches were made before writing. Existing generalizations were read and retained as the lower-level tools described below, without changing their files. No parent statement dependency points down to a new task, so their statements do not refer circularly to the theorem being split.

## Not duplicates

lem-trf-jet-level-topology-reachable-dcc vs lem-trf-jet-diagram-hilbert-control: the existing node gives finite Taylor modules, diagrams and formal DCC; the new task proves finite matrix presentations/minor loci and passes to local lex topology and all reachable geometric histories.

lem-trf-jet-level-topology-reachable-dcc vs lem-trf-standard-graded-hilbert-function: eventual polynomiality of one graded module does not prove semicontinuity or the reachable geometric diagram bound.

lem-trf-common-power-hilbert-marking vs lem-trf-formal-coefficient-transform-criterion: that node transforms separately weighted functions under five formal conditions; the new task constructs a coherent common-power ideal and its actual controlled transform, including complement and locally constant-center assembly.

lem-trf-common-power-hilbert-marking vs lem-trf-marked-controlled-blowup-charts: generic regular marked-ideal transforms do not identify the Hilbert--Samuel equality locus or provide its nonincrease criterion.

lem-trf-common-power-hilbert-marking vs lem-trf-formal-hilbert-stratum-minors: formal derivative/minor ideal equality is not the coherent common-power ideal and controlled transform package.

lem-trf-coefficient-test-sequence-propagation vs lem-trf-formal-coefficient-transform-criterion: one-step formal formulas do not supply induction through all mixed finite tests, boundary transversality at every prefix, and arbitrary smooth relative-dimension pieces.

lem-trf-coefficient-test-sequence-propagation vs lem-trf-logarithmic-coefficient-test-equivalence: that theorem compares a logarithmic coefficient ideal on a chosen hypersurface with a maximal-order marked ideal; it does not identify Hilbert--Samuel retained levels for division-adapted Taylor coefficient data.

lem-trf-minimal-envelope-coefficient-comparison vs lem-trf-smooth-embedding-etale-comparison: ambient germ comparison alone does not suspend the coefficient ideal or compare marked presentation classes along histories.

lem-trf-minimal-envelope-coefficient-comparison vs lem-trf-marked-ideal-transverse-suspension: a generic supplied transverse pair is suspended there; the new task proves essential rank positivity in minimal singular envelopes and combines suspension with coefficient and history comparisons.

Blueprint searches: Hilbert, coefficient ideal, test sequences, minimal envelope, 0905.3580, 00FP and 0FUE; full outputs retained in sandbox. The broad coefficient query found unrelated coefficient-ring nodes; narrower coefficient ideal, test sequences and minimal envelope found none. Source-tag searches for existing auxiliary tools were read; no new node claims a Stacks tag.

## Allocation of the original argument (verbatim)

The exact original nine steps follow. Their proof obligations are assigned as stated, not discarded by shortening the parent. Supporting citations remain the original lower lemmas for the new workers; these are guidance in the report, not a forbidden proof field in an unsplit node.

### Original step 1 → lem-trf-jet-level-topology-reachable-dcc

Work in an affine etale chart of the smooth ambient. By [lem-trf-jet-diagram-hilbert-control], each $H_X(x)(n)$ is a finite Taylor-module fibre dimension and is the count of missing monomials in its diagram. The diagrams take finitely many values locally, so $H_X$ does also. Its possible values in any fixed number of ambient variables satisfy the descending-chain condition. The same ambient variable bound works along blowups, whose charts have the same dimension; thus this condition also applies to values encountered later, rather than just to the initial finite image.

Cited nodes: lem-trf-jet-diagram-hilbert-control.

Source: BMT 6.1; BM 1997, Corollary 3.20 and Lemma 9.3.

### Original step 2 → lem-trf-jet-level-topology-reachable-dcc

On an affine chart, the coordinate ring is Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian] (a field has only the ideals zero and one). A finite Taylor module has a finite presentation since its relation module is a submodule of a finite free module [lem-trf-noetherian-submodule-finitely-presented]. For a matrix with $v$ target rows, fibre dimension at least $c$ means that all $(v-c+1)$-minors vanish: this follows by row reduction over the residue field. Thus each coordinate $H_X(\cdot)(n)$ is upper semicontinuous. On the finite set of local sequence values from [lem-trf-jet-diagram-hilbert-control], choose $n_1$ at least the first index at which any two of these values differ. Intersect the neighbourhoods where each coordinate $n\le n_1$ is at most its value at $a$. If $H_X(x)\ne H_X(a)$ there, they first differ at some $n\le n_1$, where $H_X(x)(n)<H_X(a)(n)$; so the neighbourhood has $H_X(x)\le H_X(a)$ lexicographically. Applying this at each point of a strict lower-level set proves that every lexicographic upper-level set is closed.

Cited nodes: lem-weil-pbc-finite-type-algebra-noetherian, lem-trf-noetherian-submodule-finitely-presented, lem-trf-jet-diagram-hilbert-control.

Source: BM 1997, Remarks 9.1, Theorem 9.2 and Lemma 9.3; finite-matrix argument written out.

### Original step 3 → lem-trf-common-power-hilbert-marking

Apply [lem-trf-regular-hilbert-coefficient-data] after the preceding shrinking. It gives a smooth $N$, regular coefficients $c_{i\gamma}$ and positive weights $m_{i\gamma}=d_i-|\gamma|$ for $|\gamma|<d_i$. Choose a positive common multiple $b$ of these finitely many weights and set $I=\sum_{i,\gamma}(c_{i\gamma}^{\,b/m_{i\gamma}})$ on $N$; if the list is empty take $b=1$ and $I=0$. In a smooth Taylor ring the order of a nonzero product is the sum of its orders, since its first nonzero homogeneous terms multiply to a nonzero polynomial. Consequently $\operatorname{ord} I\ge b$ is exactly the set of all the coefficient inequalities. The initial-stratum assertion of [lem-trf-formal-coefficient-transform-criterion] identifies this set with the $H_X(a)$ equality locus. Coherence of this finite generated ideal and of its finite free relation modules follows from [lem-trf-noetherian-submodule-finitely-presented]. This is a construction of the ideal, not a choice from a bare existence theorem.

Cited nodes: lem-trf-regular-hilbert-coefficient-data, lem-trf-formal-coefficient-transform-criterion, lem-trf-noetherian-submodule-finitely-presented.

Source: BM 1997, Theorems 9.4 and 9.6; BMT 6.2, combining marked functions by common powers.

### Original step 4 → lem-trf-common-power-hilbert-marking

Take a smooth center contained in this equality locus and in normal crossings with the boundary. The normal coordinates for its inclusion in the smooth ambient are supplied by [lem-pur-smooth-pair-local-coordinates]. The formulas of [lem-trf-formal-coefficient-transform-criterion] give $c'_{i\gamma}=e^{-m_{i\gamma}}\sigma^*c_{i\gamma}$ on the strict transform of $N$. Taking the powers used above gives $(c'_{i\gamma})^{b/m_{i\gamma}}=e^{-b}\sigma^*(c_{i\gamma}^{b/m_{i\gamma}})$; hence the transformed coefficient ideal is precisely the controlled transform of $I$. The same theorem gives $H_{X'}(a')\le H_X(a)$ and characterizes equality by these coefficient inequalities, with the five division/Jacobian conditions retained at equality points. Away from the center the blowup is an isomorphism by [thm-nagata-global-blowup-complement], and the strict transform restricts to the original scheme by [lemma-nagata-strict-transform-over-complement]. Shrinking around any point of a locally $H$-constant center proves the stated nonincrease for all such blowups.

Cited nodes: lem-pur-smooth-pair-local-coordinates, lem-trf-formal-coefficient-transform-criterion, thm-nagata-global-blowup-complement, lemma-nagata-strict-transform-over-complement.

Source: BM 1997, Theorems 7.20 and 9.4; Stacks 0FUE for smooth-pair coordinates.

### Original step 5 → lem-trf-coefficient-test-sequence-propagation

The other formulas of [lem-trf-formal-coefficient-transform-criterion] use ordinary pullback for an exceptional intersection blowup; $X$ is then a total transform, not an arbitrarily stipulated strict transform. For a line product the Taylor count in [lem-trf-jet-diagram-hilbert-control] replaces $H$ by $\Lambda H$. Adjoin the horizontal zero section to the ordered boundary. Induct on the length of a test sequence, carrying also the claim that every boundary component is transverse to the current $N$ (its equation is a coordinate of $N$ in the coordinates $(W,Z)$): the boundary is empty at length zero; an admissible center lies in the cosupport, hence in $N$, so in each chart meeting the strict transform of $N$ the exceptional equation and the strict transforms of earlier boundary coordinates are $W$-coordinates; a line zero section and the exceptional divisor of a blowup of two such boundary hyperplanes are again given by $W$-coordinates. This is the transversality hypothesis of the exceptional-intersection formula. For length zero the initial equality criterion was proved in step 3. For an admissible blowup apply step 4 and retain the division data at equality points; for the other two operations use the just cited formulas. Thus at each stage the two cosupports coincide and allow exactly the same next smooth center. This proves equality of all test sequences, with the specified exceptional ordering.

Cited nodes: lem-trf-formal-coefficient-transform-criterion, lem-trf-jet-diagram-hilbert-control.

Source: BM 1997, Definition 6.2, formulas (6.1), Theorems 7.20--7.21; BMT 5.2.

### Original step 6 → lem-trf-minimal-envelope-coefficient-comparison

First choose a minimal smooth envelope by [lem-trf-smooth-embedding-etale-comparison], and perform step 3 there. At a singular point its Taylor ideal is nonzero, so the construction uses at least one essential transverse variable: otherwise the diagram would be empty and the local scheme would be the smooth envelope. The smooth pair has etale transverse retraction coordinates by the same comparison node. Apply [lem-trf-marked-ideal-transverse-suspension] to $(N,I,b)$ in those coordinates. Its explicit ideal $J=(z_1^b,\ldots,z_r^b)+p^*I$ has the same test sequences, is on the whole envelope, and has order exactly $b$ along cosupport since $r\ge1$. For a regular codimension-zero germ take $N=Z$, $I=0$, $b=1$; the equality/test description still holds, while order is infinite. This explains the necessary singular-point restriction on the maximal-order clause.

Cited nodes: lem-trf-smooth-embedding-etale-comparison, lem-trf-regular-hilbert-coefficient-data, lem-trf-marked-ideal-transverse-suspension.

Source: BMT 6.2, minimal embedding and maximal-order paragraph; explicit regular-germ exception.

### Original step 7 → lem-trf-coefficient-test-sequence-propagation

A smooth morphism is locally etale over an affine-space projection by [sbc-thm-etale-local-normal-form]. The Taylor-module identities of [lem-trf-jet-diagram-hilbert-control] are invariant under that etale localization, and adjoining $r$ free variables gives $H_Y=\Lambda^rH_X$ on a piece of relative dimension $r$. For two different sequences the first nonzero coefficient of their difference is also the first nonzero coefficient of its partial sum, with the same sign. Thus $\Lambda^r$ preserves and reflects lexicographic inequalities and equality. Pull back the coefficient construction; its test-transform identities remain the identities in step 4, now in the pulled-back coordinates. Therefore it is a presentation of the summed level. This is a local assertion on each relative-dimension piece; it does not synchronize the numerical maxima of different pieces.

Cited nodes: sbc-thm-etale-local-normal-form, lem-trf-jet-diagram-hilbert-control, lem-trf-formal-coefficient-transform-criterion.

Source: BMT 6.3, line-product formula and smooth functoriality; BM 1997, Definition 6.2.

### Original step 8 → lem-trf-minimal-envelope-coefficient-comparison

Any two coefficient constructions in a fixed envelope present the same intrinsic retaining-level test data by step 5; hence their sequences agree, which is exactly equivalence. Two minimal envelopes have a common etale comparison identifying their closed copies of $X$ by [lem-trf-smooth-embedding-etale-comparison]. On that comparison apply the preceding observation. This identifies classes, not a uniquely chosen coefficient ideal. The comparisons pull back every specified earlier center ideal. Repeating the retaining-level criterion of step 5 after each center therefore also identifies the induced ordered boundary and subsequent transformed presentations. Restriction is obtained by applying the very same formulas in a smaller open neighbourhood. This proves the claimed intrinsic dependence for these admissible histories, without a new assertion about arbitrary ambient histories.

Cited nodes: lem-trf-smooth-embedding-etale-comparison, lem-trf-formal-coefficient-transform-criterion.

Source: BM 1997, Remarks 6.3 and Definition 6.4; BMT 6.2--6.3.

### Original step 9 → lem-trf-jet-level-topology-reachable-dcc (geometric preservation and reachable DCC); parent step 5 (conditional disappearance)

Suppose the presentation is of the maximum level $H_0$ and an admissible sequence empties its cosupport. At each preceding stage the equality criterion of step 5 says that every point with value $H_0$ is in that cosupport, while nonincrease in step 4 rules out values above $H_0$. Thus no final point has value $H_0$. The diagram descending-chain condition of [lem-trf-jet-diagram-hilbert-control] applies at every stage in the same ambient dimension; it rules out infinitely many strict drops. The ambient and strict transform remain smooth and reduced, respectively, by [lem-trf-smooth-center-blowup-geometry], after restriction to finite-type separated smooth charts. Induction therefore reapplies the construction at every admissible history. No resolution engine is invoked to turn this conditional disappearance statement into an assertion of a completed tower.

Cited nodes: lem-trf-jet-diagram-hilbert-control, lem-trf-formal-coefficient-transform-criterion, lem-trf-smooth-center-blowup-geometry.

Source: BMT 6.1 and first paragraph of 6.3; BM 1997, presentation criterion.

## Original supporting citation audit

lem-pur-smooth-pair-local-coordinates: Let $S$ be a scheme [def-pc-scheme], let $X\to S$ and $Y\to S$ be smooth morphisms [def-sbc-smooth-morphisms], and let $i:Y\hookrightarrow X$ be a closed immersion over $S$ [def-weil-closed-immersion]. For every $y\in Y$ there are integers $a,b\geq0$, an open neighbourhood $U\subseteq X$ of $i(y)$ [def-weil-open-immersion], and an etale $S$-morphism $h:U\to\mathbf A^{a+b}_S$ [def-weil-etale-morphism, def-sbc-affine-space], such that $V=Y\times_XU$ is the scheme-theoretic inverse image of the coordinate subspace $\mathbf A^a_S\subseteq\mathbf A^{a+b}_S$ given by the last $b$ coordinates equal to zero, and $V\to\mathbf A^a_S$ is etale [def-pc-base-change]. The ideal sheaf of $V$ [def-sbc-closed-immersion-ideal-sheaf] is generated by the pullbacks of those last $b$ coordinate functions, which form a regular sequence (each is a nonzerodivisor modulo its predecessors).

lem-trf-formal-coefficient-transform-criterion: Let $X\hookrightarrow M$ be a closed finite-type scheme in a smooth scheme over a characteristic-zero field. Fix a point $a$ and its Taylor ideal $K\subset L[[W,Z]]$, where $L=\kappa(a)$. Suppose there are regular coefficient models and generators $f_i=\sum_\gamma c_{i\gamma}(W)Z^\gamma$ with orders $d_i$ satisfying all five division and Jacobian conditions explicitly stated in [lem-trf-regular-hilbert-coefficient-data]. Write $H_K(n)=\dim_L L[[W,Z]]/(K+(W,Z)^{n+1})$, the extended function computed by the Taylor module. The local equality locus for the extended Hilbert--Samuel function through $a$ is cut out, as a set, by $Z=0$ and the inequalities $\operatorname{ord}c_{i\gamma}\ge d_i-|\gamma|$ for $|\gamma|<d_i$; this assertion also applies to the regular coefficient models of that node.
Let $C$ be a smooth coordinate center contained in this germ, let $\sigma$ be its blowup [def-nagata-global-blowup], and transform the ideal $K$ by saturation of its total transform by the exceptional equation, so as to define scheme-theoretic strict transform [def-nagata-strict-transform]. At a point $a'$ of the exceptional fibre, $H_{K',a'}\le H_K$. Equality holds if and only if $a'$ belongs to the strict transform of $Z=0$ and, in its nonempty charts with exceptional coordinate $e$,
$$\operatorname{ord}_{a'}c'_{i\gamma}\ge d_i-|\gamma|,\qquad c'_{i\gamma}=e^{-(d_i-|\gamma|)}\sigma^*c_{i\gamma}.$$
The quotients in this formula are regular. At equality points the transformed $f_i$ satisfy the same five conditions with the same vertex diagram, and have coefficients $c'_{i\gamma}$. For the blowup of an intersection of two boundary coordinate hyperplanes transverse to $Z=0$, use total transform of $K$ and ordinary pullback $c'_{i\gamma}=\sigma^*c_{i\gamma}$; the same five conditions persist and the Hilbert--Samuel function is unchanged at corresponding closed points. Adjoining an independent formal variable takes ordinary pullbacks of the coefficients and sums the Hilbert--Samuel function once. These formulas hold over residue-field extensions and for regular coefficient models after etale localization.

lem-trf-jet-diagram-hilbert-control: Let $k$ be a field of characteristic zero. For a finitely generated $k$-algebra $A$, put $J=\ker(A\otimes_k A\to A)$ and $P^n_{A/k}=(A\otimes_k A)/J^{n+1}$, viewed as an $A$-module through the first factor. These are finite $A$-modules. At $x\in\operatorname{Spec}A$, put $t_x=\operatorname{trdeg}_k\kappa(x)$, $h_x(n)=\operatorname{length}(A_x/\mathfrak m_x^{n+1})$ and $\Lambda f(n)=\sum_{i=0}^n f(i)$ [def-weil-pbc-module-length] [def-weil-residue-field] [def-kun-transcendence-degree]. Then
$$\dim_{\kappa(x)}(P^n_{A/k}\otimes_A\kappa(x))=(\Lambda^{t_x}h_x)(n).$$
For an etale chart $U\to\mathbf A^d_k$ in a smooth ambient scheme and a coherent ideal defining a closed subscheme $X\subset U$ [def-weil-etale-morphism] [def-sbc-smooth-morphisms] [def-weil-closed-immersion] [pqf-def-coherent], for $x\in X$, Taylor expansion of that ideal at $x$ gives an ideal $K_x\subset\kappa(x)[[T_1,\ldots,T_d]]$ whose quotient by $(T)^{n+1}$ has dimension equal to this same fibre dimension. For a formal ideal $K\subset L[[T_1,\ldots,T_d]]$, order exponents first by total degree and then lexicographically, let $\mathcal N(K)$ be the exponents of first nonzero monomials of its elements, and let its vertices be the finite minimal set $V$ with $\mathcal N(K)=V+\mathbf N^d$. More explicitly, choose nonzero $G_i\in K$ representing ordered vertices $\alpha_i$ of $\mathcal N(K)$, put $E_i=(\alpha_i+\mathbf N^d)\setminus\bigcup_{j<i}(\alpha_j+\mathbf N^d)$, $\Delta_i=E_i-\alpha_i$, and $E_0=\mathbf N^d\setminus\mathcal N(K)$. Every series $F$ has a unique expression $F=\sum_iQ_iG_i+R$ with $\operatorname{supp}Q_i\subseteq\Delta_i$ and $\operatorname{supp}R\subseteq E_0$, and
$$\dim_L L[[T]]/(K+(T)^{n+1})=\#\{\alpha\notin\mathcal N(K):|\alpha|\le n\}.$$
The Taylor diagrams $\mathcal N(K_x)$ take only finitely many values locally on $U$. The set of all functions $n\mapsto\#\{\alpha\notin D:|\alpha|\le n\}$, with $D+\mathbf N^d=D$, has no infinite strictly decreasing sequence in lexicographic order. Formation of $P^n$, Taylor expansion, and these dimension identities commutes with etale localization. Adjoining $r$ free variables replaces these functions by their $r$fold iterated sums.

lem-trf-marked-ideal-transverse-suspension: Let $N\hookrightarrow Z$ be a smooth closed pair of finite-type schemes over a field of characteristic zero, and let $E$ be an ordered list of smooth hypersurfaces with normal crossings, transverse to $N$ [def-sbc-smooth-morphisms] [def-weil-closed-immersion] [def-weil-finite-type-morphism]. Suppose that, after etale localization [def-weil-etale-morphism], a retraction $p:Z\to N$ and transverse parameters $z_1,\ldots,z_r$ identify this pair with an etale neighbourhood of the zero section of $N\times\mathbf A^r$, compatibly with the boundary coordinates. For a coherent ideal $I\subset\mathcal O_N$ and $b\ge1$ [pqf-def-coherent], put
$$J=(z_1^b,\ldots,z_r^b)+p^*I\subset\mathcal O_Z.$$
The order cosupport of $(J,b)$ on $Z$ equals that of $(I,b)$ on $N$, where order is the largest $q$ with the stalk ideal contained in the $q$th maximal-ideal power, or infinity for zero. The two marked ideals have the same finite test sequences: smooth centers in cosupport transverse to the ordered boundary, products with a line (adjoining its zero section to the boundary), and blowups of intersections of boundary components. For the first operation take strict transform of the smooth support and divide the ideal's total transform by the $b$th exceptional power; for the other two take ordinary pullback [def-nagata-global-blowup] [def-nagata-strict-transform]. On a nonempty admissible chart the new normal parameters are $z_j/e$, and the new suspended ideal is generated by $(z_j/e)^b$ and the controlled transform of $I$; in charts missing the strict transform of $N$ the cosupport is empty. For $r\ge1$, the order of $J$ is exactly $b$ throughout its cosupport. For $r=0$ the assertion is only equivalence, with $J=I$.

lem-trf-noetherian-submodule-finitely-presented: Let $R$ be a Noetherian commutative ring [def-weil-pbc-noetherian-ring], let $F$ be a finitely generated $R$-module [def-weil-finitely-generated-module], and let $G\subseteq F$ be any $R$-submodule. Then $G$ is finitely generated and finitely presented as an $R$-module [def-sc-finitely-presented-module].

lem-trf-regular-hilbert-coefficient-data: Let $X\hookrightarrow M$ be a reduced closed subscheme of a smooth scheme of finite type over a characteristic-zero field $k$ [def-pc-reduced-scheme] [def-weil-closed-immersion] [def-sbc-smooth-morphisms] [def-weil-finite-type-morphism]. At any point $a$, etale-locally after shrinking, there exist a smooth closed $N\subset M$, coordinates $w$ on $N$, formal transverse coordinates $Z$, a finite diagram $D=V+\mathbf N^n$, and formal generators
$$f_i(W,Z)=\sum_\gamma c_{i\gamma}(W)Z^\gamma$$
of the Taylor ideal of $X$ at $a$. Each coefficient is the Taylor expansion of a regular function $c_{i\gamma}$ on $N$. The transverse variables $Z$ are precisely the variables occurring to positive power in the vertex monomials; the vertices have zero $W$ components. Write the ordered vertices as $\alpha_i$, $d_i=|\alpha_i|$, and partition $D$ into disjoint sets $\alpha_i+\Delta_i$ by assigning each exponent to its first vertex. The data satisfy the following conditions, also after Taylor expansion at every point of the coefficient order locus $\{x\in N:\operatorname{ord}_x c_{i\gamma}\ge d_i-|\gamma|\ (|\gamma|<d_i)\}$:
(1) $\operatorname{ord} f_i=d_i$.
(2) For every degree bound $q$, the homogeneous polynomials have unique division by the initial forms of the $f_i$ with $d_i\le q$, quotients supported in $\Delta_i$, and remainder supported outside the diagram generated by those vertices.
(3) Every element $f$ of the Taylor ideal has an expansion $f=\sum q_i f_i$ with $\operatorname{supp}q_i\subset\Delta_i$.
(4) Group the vertices into blocks of equal total degree, and let $Z^\ell$ be the variables occurring in the first $\ell$ blocks. For each such variable $Z_j$, choose $\alpha_{i(j)}=\beta_j+e_j$ in those blocks. The derivatives $g_j=\partial_Z^{\beta_j}f_{i(j)}$ belong to $(Z^\ell)$ and their Jacobian in the variables of $Z^\ell$ is invertible at the point.
(5) For any fixed $Q\ge\max d_i-1$, the generators in later blocks satisfy $\partial_{Z^\ell}^{\beta}f_i\in(Z^\ell)$ for $|\beta|\le Q$ lying in the diagram of the first $\ell$ blocks, restricted to its essential variables.
The subscheme $N$ is cut out by regular equations with the invertible Jacobians in (4). The coefficient functions and these equations are defined on one common etale neighbourhood. One can shrink so that the extended Hilbert--Samuel function throughout it is at most its value at $a$. Order means containment in powers of the local maximal ideal, with infinite order for zero. The number of eliminated variables may be zero. This is existence of specially chosen division-adapted generators; it does not assert algebraization of an arbitrary formal standard basis.

lem-trf-smooth-center-blowup-geometry: Let $P$ be smooth, separated and of finite type over $\mathbf Q$, and let $C\hookrightarrow P$ be a smooth closed subscheme [def-sbc-smooth-morphisms, def-weil-closed-immersion, def-weil-proper-morphism, def-weil-finite-type-morphism]. Then $P^+=\operatorname{Bl}_C(P)$ [def-nagata-global-blowup] is smooth, separated and of finite type over $\mathbf Q$. The empty center is allowed. If $X\hookrightarrow P$ is any reduced closed subscheme [def-pc-reduced-scheme], its scheme-theoretic strict transform in $P^+$ is reduced [def-nagata-strict-transform]. These assertions do not require the center to be a maximum stratum or to be contained in $X$.

lem-trf-smooth-embedding-etale-comparison: Let $X$ be a scheme of finite type over a characteristic-zero field $k$ and $x\in X$ [def-weil-finite-type-morphism]. A minimal smooth envelope at $x$ means a local closed embedding $X\hookrightarrow M$ into a smooth $k$-scheme for which the induced map
$$\Omega_{M/k}\otimes\kappa(x)\longrightarrow\Omega_{X/k}\otimes\kappa(x)$$
is an isomorphism; $\Omega$ denotes the module generated by symbols $da$ with additivity, the Leibniz rule, and $dc=0$ for $c\in k$ [def-weil-pbc-kahler-differentials]. Such envelopes exist after restriction and etale localization. Any smooth local envelope contains a minimal smooth closed envelope through $X$. Given two minimal envelopes of the same scheme germ, there is a common etale neighbourhood of the pointed closed pairs, identifying the induced neighbourhoods of $X$ by their given identification. Equivalently their henselian ambient germs are isomorphic by an isomorphism inducing the given quotient isomorphism. A smooth closed pair $N\hookrightarrow M$ admits, etale-locally along $N$, a retraction onto an etale neighbourhood of $N$ and transverse regular parameters: locally the pair is the zero section in an etale neighbourhood of $N\times\mathbf A^r$. These comparisons allow adjoining and eliminating transverse regular parameters and respect pullback of specified ideal sheaves on $X$.

lem-weil-pbc-finite-type-algebra-noetherian: Let $R$ be a Noetherian ring [def-weil-pbc-noetherian-ring] and $R\to S$ a ring map of commutative rings of finite type, i.e. $S\cong R[x_1,\dots,x_n]/\mathfrak a$ as $R$-algebras for some $n\ge0$ and some ideal $\mathfrak a$. Then $S$ is a Noetherian ring.

lemma-nagata-strict-transform-over-complement: Let $f\colon Y\to X$, let $\mathcal I$ be a finite-type quasi-coherent
ideal, and put $X'=\operatorname{Bl}_{\mathcal I}(X)$. Over
$U=X\setminus V(\mathcal I)$, the strict transform is canonically
$Y\times_XU$, and its map to $Y$ is the ordinary pullback isomorphism.

sbc-thm-etale-local-normal-form: Let $g:Y'\to Y$ be
smooth at $y'\in Y'$. After
replacing $Y,Y'$ by affine neighbourhoods, there are $d\geq0$ and an
etale morphism

$$
e:Y'\longrightarrow\mathbf A^d_Y
$$

such that $g$ is $e$ followed by the projection
$p_d:\mathbf A^d_Y\to Y$ of [def-sbc-affine-space].
(*Stacks Project, Morphisms, [Tag `054L`](https://stacks.math.columbia.edu/tag/054L) = Lemma
29.37.21.*)

thm-nagata-global-blowup-complement: Let $U=X\setminus V(\mathcal I)$. The restriction

$$
b_{X,\mathcal I}^{-1}(U)\longrightarrow U
$$

is an isomorphism.
