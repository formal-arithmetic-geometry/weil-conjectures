# Repair report: lem-per-gabber-abelian-stage-toric-chart

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-abelian-stage-toric-chart.json`: twelve proof steps; original statement, statement dependencies, creation stamp and ancestry retained.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-tame-invariants-arbitrary-base-change.json`: statement-only generic Reynolds/base-change lemma; searched, not a Mathlib leaf.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-inert-etale-quotient-comparison.json`: statement-only generic inert etale quotient/descent lemma; searched, not a Mathlib leaf.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-g-cover-fs-base-change.json`: statement-only generic Kummer-cover stability lemma; searched, not a Mathlib leaf.
- `citations.json`: sandbox validation artifact. The delivery tool commits nodes and this report, not that artifact; the exact citation records are reproduced in the appendix below so the delivered evidence is complete.

Three new nodes, zero Mathlib leaves. No Lean was written and no compiler, Lake or build command was run.

## Attachments

None. The retained search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by blueprint id and invariant-monoid/abelian-toric notions found no exact declaration. I repeated the concept search there and inspected the invariant/representation-related source hits; they concern ordinary Galois inertia and representations, not this logarithmic local construction. The master reference checkout is not treated as a finished proof.

## WANTED

No newly needed source document. ILO and the Stacks source are present. The already-existing `lem-per-local-cyclotomic-group-algebra-split` records Serre 1978, chapters 12--13, as WANTED; this repair cites that existing statement and the integral representation input explicitly referenced by ILO X 1.2, rather than creating another eigenbasis lemma or claiming Serre was read.

## What was wrong and how each return was repaired

1. Original Step 2 incorrectly applied a sharp strictly-local lemma to a global non-sharp monoid. New Steps 3--4 never use that lemma: they calculate the Reynolds operator on each monomial, prove finite generation by coordinate remainders modulo N, prove group completion equals ker chi by shifting the nonnegative coordinates, and prove saturation in that kernel lattice. The quotient is the actual invariant monoid algebra, not a hypothetical sharp invariant chart.
2. Original Step 3 substituted existence of an unspecified projective resolution for the fourth stage's functorial tower, and used a theorem over Q without the monoid comparison. New Steps 5--6 cite the existing functorial fan desingularization, strict fan-chart comparison, monoidal-resolution tower and descent statements. Saturated affine charts come from the stated chart construction; every group-completion map is unchanged. Toric-monoid comparison (i)--(iii) is cited only for the actual monoid/toric bridge and its Q interpretation; the proof does not apply a Q-scheme resolution theorem to Lambda-schemes. The arbitrary projective-resolution and toric-normalized-desingularization citations are removed.
3. Original Step 4 omitted the zero-locus argument. New Step 7 uses f=(z1...zr)^N in Lambda[R], proves T1=V(f) set-theoretically by quotient orbit fibres, and pulls that equation back to a monomial on the resolved chart. Its positive exponents select exactly the retained coordinate divisors. The regular-boundary-divisorial-chart statement gives the smaller log chart. New Step 8 separately proves nu(R) lies in R' by pulling back monomial zero sets. No inference from an arbitrary closed subset to a divisor is used.
4. Original Step 6 silently commuted quotient and non-flat base change and asserted quotient etaleness of an inert comparison. New Step 10 cites the new arbitrary-base-change lemma. New Step 11 cites the new inert-etale quotient comparison, including strictness, and the new Kummer-cover fs-base-change lemma for the different operation of pulling a cover back along the log resolution. The latter is kept separate because Reynolds alone does not justify a saturated fs fibre product. Step 12 uses only the fourth-stage functoriality, independence and gluing actually in the parent statement.
5. Minor Step 1: removed the sharp-chart citation entirely. The existing local cyclotomic group-algebra splitting gives scalar summands when G is abelian; the finite-projective free-cover statement justifies the further coefficient localization. The unit part of P is retained. Added the short regularity check for Lambda and all polynomial/Laurent charts before applying a regular-boundary or log-regular quotient lemma.
6. C8: neither top-level `tool_uses` nor `split_report.tool_uses` is written. The off-unit generic tools are requested for the maintainer's decision below. The report no longer relies on a citations file absent from the commit: its complete verbatim evidence is embedded here.

Compared the retained sandbox against the current shared node before editing. The shared node is still unsplit; its statement and imported ancestry agree. The earlier dry-run receipt applies to the old returned split only; this repair changes every faulty argument and requires a new dry run.

## Not duplicates

lem-per-tame-invariants-arbitrary-base-change vs lem-per-finite-quotient-strict-local-invariants: the existing 0BRH citation is a flat strict-local quotient comparison for a given finite scheme quotient and invariant log stalk; the new statement concerns arbitrary scalar extension of any linear tame representation and any algebra, without flatness or geometry.

lem-per-tame-invariants-arbitrary-base-change vs lem-per-very-tame-quotient-log-regular: the existing statement concludes fs log regularity of a very tame quotient; it does not state arbitrary base change of invariants or the Reynolds splitting.

lem-per-tame-invariants-arbitrary-base-change vs lem-per-nodal-quotient-normalized-base-refinement: the existing statement refines a particular nodal curve/Galois alteration by normalization and decomposition groups; it does not identify arbitrary tensor base changes of invariants.

The inert comparison is not a duplicate of fixed-locus-log-chart: that statement supplies an equivariant etale comparison and blowup equations, not etaleness on quotient schemes or the cartesian quotient square. The new Kummer-cover lemma is not very-tame-log-quotient: the latter constructs a quotient on a log regular source, whereas the new fact identifies quotients after arbitrary fs base change, even when the base is not log regular. None of the three children states the invariant-monoid chart, retained boundary, affine-space map or functorial tower that the item proves.

## Generic tool requests for the maintainer

The fan-resolution, monoidal-resolution, strict-fan comparison, fan-chart blowup, coherent log-ideal chart construction, toric-monoid comparison and tower descent nodes are generic monoidal geometry used exactly along ILO VIII's route. The finite-free subgroup and finite-projective localization nodes are ordinary algebra. Standard-etale/standard-smooth, localization-regularity, polynomial-regularity and smooth-ascent nodes justify only the coefficient rings and coordinate charts. These uses replace no step of the perverse/Fourier unit by a theorem of another unit. The already-reviewed closure checks in the return accepted the generic log/fan route; no trace-formula, Poincare duality, nt-assume or SGA result is introduced. I leave recording accepted tool uses to the maintainer.

## What could not be finished

No unresolved stage-1 mathematical claim in the item's proof beyond its cited statement nodes. The three new generic statements deliberately remain unsplit, as required. The final required delivery invocation is the only publication step.

## Review by Q06

I read ILO VIII 5.3.6--5.5.5 (printed pp.124--129) and X 1.8--1.9 (pp.146--148), including the invariant monoids and diagrams (1.a)--(1.d), and consulted VIII 3.3.8--3.3.15 and X 1.2 for the functorial charts and integral representation input. The item's statement is unchanged and still states only the fourth-stage local model, not the stronger relative smoothness assertion proved later in X. There is no statement dispute or unit-route departure.

For the new invariant/base-change node I read Stacks more-algebra.tex, 0H36 (remark-when-iso), 0BRG and 0BRH (functor-invariants-tensor and base-change-invariants). The no-flatness conclusion uses invertible group order: e is a projection and M=M^G direct sum ker e; tensoring this split decomposition preserves its summands, and the averaged operator after tensoring is 1 tensor e. Thus its image is B tensor M^G and also the invariant module. In the algebra case the comparison is the natural multiplicative map. The new statement is not the false assertion that invariants always commute with non-flat extension. I checked the trivial group, zero module, zero scalar ring, and non-flat extension Z[1/2] -> F3. In characteristic dividing the group order the excluded hypothesis is essential.

For the inert quotient node I read Stacks groupoids.tex, Tag 0DT9 (lemma-etale), including its strict-henselian splitting proof and cartesian-square conclusion. For constant finite action groupoids the source and target diagrams are cartesian automatically; equality of geometric stabilizers gives the stabilizer square, so the hypotheses really hold. The affine conclusion glues over invariant affine neighborhoods. The inert locus is open: for each g, failure is h^{-1}(U^g) minus V^g; V^g is relatively open there since the etale diagonal is open, so failure is closed in V (the fixed loci of separated schemes are closed). Finite intersection gives the claimed open. I read ILO VIII 5.4.2 for log strictness. Tested the identity map, free actions, and an etale cover where a stabilizer drops; the latter must be removed before applying the theorem. This is a generic quotient statement, not a clause of the target toric chart.

For the Kummer-cover node I read ILO VIII 5.3.8 and X 1.8's explicit arbitrary-fs-base-change assertion and diagrams, together with VI 3.2's quotient/G-cover interface. Its definition makes the fs torsor square explicit, rather than silently using an ordinary scheme torsor. Both log etaleness and the torsor square survive fs pullback, and the resulting cover has the stated quotient. I checked a trivial cover, a disjoint ordinary etale G-torsor, and the tame one-variable Kummer chart with a log-point base change; a non-strict base change must use the fs product. The order and local-Noetherian hypotheses are retained.

I opened every cited node's statement, not only its title or proof. Step 1 takes the fixed unit/eigenparameter chart and actual representation from fixed-locus-log-chart; local-cyclotomic-group-algebra-split supplies full matrix factors, and commutativity forces them to be scalar. Finite-projective-standard-free-cover justifies the eigenbasis localization. Step 2 checks the regular base hypothesis before regular-boundary-divisorial-chart, using the cyclotomic derivative and the exact standard-smooth and regularity statements quoted below. Step 3 uses only the projection conclusion of the new invariant lemma and a written monomial character sum. Step 4 is elementary coordinate arithmetic and does not borrow the sharp local-Kummer theorem.

Step 5 uses the functorial fan theorem's ordered centers and composition comparisons, fan-chart-blowup(ii)'s strict-base-change statement, strict-fan-chart-local-comparison's actual fan isomorphisms, and the stated descent hypotheses. Their hypotheses (finite chart covers, fs and torsion-free characteristics) follow from Step 4. The monoidal-resolution statement is used for free final characteristics, not for an unstated canonical tower. Step 6 takes the precise saturated chart rings and group completions from coherent-log-ideal-chart-construction and the free final fan stalks from the fan definition, then splits units using the subgroup-free statement. Toric-monoid-comparison is used with its field hypothesis respected.

Step 7 takes orbit fibres from very-tame-log-quotient and the actual divisorial-chart theorem after Step 2 verifies regularity and after its monomial equation verifies strict normal crossings. Step 8's containment is written in zero sets and nonnegative exponents; orbit fibres are the only non-elementary quotient input, and it is cited. Step 9 is the monoid-ring polynomial identity. Step 10 applies the new invariant comparison with A=Lambda[Q], with trivial base action and invertible group order, never with an assumed flat map. Its tower comparison uses the explicit strict-base-change clause of fan-chart-blowup.

Step 11 checks log regularity of the enlarged base-changed model using the existing invertible-torsion log-smooth regularity statement and the actual Q -> Pbar chart. Diagonal inertia fixes every residual stratum; generically free follows on the inert neighborhood from original freeness. These are the hypotheses of very-tame-log-quotient. The new Kummer statement supplies the fs-pullback quotient, while the new inert statement supplies etaleness and log strictness of comparisons. Retained boundary strictness follows by inverse-image coordinate divisors. Step 12 takes the parent's stated fourth-stage independence and strict-inertia functoriality, not any construction hidden in its proof.

All new nodes are self-contained statements with empty proof/proof_deps and no proof sketch. Every definition dependency is either cited or defined inline. Whole-DAG searches by keywords and Stacks tags and whole-blueprint searches (Reynolds, invariant base change, finite group invariants, stabilizer preserving, inert, 0DT9, 0H36, Kummer etale, Kummer cover) found no existing statement giving these interfaces. The exact Mathlib searches are in searches.jsonl and copied to the node records; I read the returned hits. averageMap_invariant, averageMap_id and isProj_averageMap in Mathlib/RepresentationTheory/Invariants.lean:129--145 give only the Reynolds projection; the tensor comparison is not a one-line specialization of a returned declaration. Other hits are ordinary etale stability, set quotients, or field Galois groups. The Kummer log search had a second retained phrasing, whose hits are also ordinary etale facts. No unavailable service is recorded as a negative result, and no search record is invented.

I retested c=0, c=b, b=0, trivial G, r=0 (the original boundary is empty, f=1, c=0), s=0 and N=1. In each case the monoid inclusions, zero sets, and affine relative dimension have the asserted values. For a nontrivial check take G=mu2 acting by -1 on z,y: Rbar has the parity-even lattice, R consists of even z powers, and the pullback of z^2 selects the retained divisors; the extra y boundary is not silently retained. Each non-elementary step is under 2000 characters, and no child carries one of the item's own geometric clauses. proof_deps is exactly the union of uses. The artifact quotes and the committed appendix below are generated from the same verbatim cited statements.

## Citation evidence (committed copy of citations.json)

```json
[
 {
  "step": 1,
  "node": "lem-per-gabber-fixed-locus-log-chart",
  "quote": "Let $f:(X,Z)\\to(S,D)$ be a log smooth morphism of Noetherian fs log regular pairs [def-trf-fs-log-blowup], [def-per-fs-log-smooth-etale], with $X$ regular and $Z$ a $G$-strict strict normal crossings divisor. $G$-strict means that distinct translates of any irreducible boundary component are disjoint. A log regular pair means its fs log structure is $\\mathcal O\\cap j_*\\mathcal O^\\times$ for the boundary complement $j$; strict normal crossings means locally a product of distinct regular parameters, with regular global components and regular intersections of the expected codimension. Let a finite group $G$ act tamely over $S$, trivially on $S$. Fix a geometric point $\\bar x$ and replace $G$ by its inertia group there. For any subgroup $H\\le G$, etale locally near this point and its image there is a strict equivariant etale comparison from $X$ to the pullback over $S$ of\n$$Y=\\operatorname{Spec}\\Lambda[u_1^{\\pm1},\\ldots,u_t^{\\pm1},z_1,\\ldots,z_r,y_1,\\ldots,y_s]\\longrightarrow\\Sigma=\\operatorname{Spec}\\Lambda[Q].$$\nHere $Q$ is a sharp fs chart of $S$, $\\Lambda$ is a localization of $\\mathbf Z[1/N,\\mu_N]$ with $N$ invertible at the point, $N$ annihilates the inertia group, $\\mu_N$ denotes the $N$th roots of unity, $P=\\mathbf Z^t\\oplus\\mathbf N^r$ is a chart for the boundary $T=(z_1\\cdots z_r=0)$, and the map is induced by $\\gamma:Q\\to P$ with injective group completion and finite invertible torsion in its cokernel. The $u_j$ are fixed by inertia, each $z_j$ is an eigenvector, and the $y_j$ span a finite free inertia representation. Coordinates for the latter may be chosen after restriction to $H$ so that\n$$Y^H=V(z_1,\\ldots,z_m,y_1,\\ldots,y_n)$$\nfor some $0\\le m\\le r$, $0\\le n\\le s$. If $H$ acts trivially, its fixed subscheme is the whole scheme and is omitted from the blowup procedure."
 },
 {
  "step": 1,
  "node": "lem-weil-pbc-finite-projective-standard-free-cover",
  "quote": "Let $A$ be a commutative ring and $M$ an $A$-module which is a direct summand of a finite free $A$-module (equivalently, $M$ is finite projective). Then there are finitely many elements $f_1,\\dots,f_r\\in A$ generating the unit ideal such that for every $i$ the localization $M_{f_i}$ is a finite free $A_{f_i}$-module."
 },
 {
  "step": 1,
  "node": "lem-per-local-cyclotomic-group-algebra-split",
  "quote": "Let $N\\geq1$ and let $G$ be a finite group with $g^N=1$ for every $g\\in G$. Fix a primitive complex $N$th root of unity $\\zeta_N$, put $A=\\mathbf Z[1/N,\\zeta_N]$, and let $\\Lambda=A_{\\mathfrak p}$ for a prime ideal $\\mathfrak p\\subset A$ [def-weil-pbc-localization-at-prime]. Define the group algebra $\\Lambda[G]$ to be the free $\\Lambda$-module on symbols $[g]$, with multiplication $[g][h]=[gh]$ extended bilinearly. There are an integer $r\\geq1$, integers $d_1,\\ldots,d_r\\geq1$, and a $\\Lambda$-algebra isomorphism\n$$\\Lambda[G]\\cong\\prod_{i=1}^{r}M_{d_i}(\\Lambda).$$\nHere $M_d(\\Lambda)$ is the ring of $d$ by $d$ matrices [def-weil-matrix] with the usual matrix addition and multiplication."
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-standard-etale-monic-derivative",
  "quote": "Let $S$ be a commutative ring, $Q\\in S[T]$ a monic polynomial with derivative $Q'$, and $S'=S[T][Y]/(Q,\\,YQ'-1)$ (that is, $S[T]_{Q'}/(Q)$), with $x\\in S'$ the class of $T$. Then (1) $\\operatorname{Spec}S'\\to\\operatorname{Spec}S$ is etale [def-weil-etale-morphism]; (2) for every $S$-algebra $L$ and every $b\\in L$ with $Q(b)=0$ and $Q'(b)$ a unit of $L$ there is exactly one $S$-algebra map $S'\\to L$ sending $x$ to $b$."
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-regular-ring-smooth-ascent",
  "quote": "Let $\\varphi:R\\to S$ be a homomorphism of commutative rings which is a smooth ring map [def-weil-pbc-smooth-ring-map], and assume $R$ is a regular ring [def-weil-regular-scheme] (Noetherian, with every localization at a prime ideal a regular local ring). Then $S$ is a regular ring."
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-localization-of-regular-ring",
  "quote": "Let $R$ be a regular ring [def-weil-regular-scheme] (Noetherian, with every localization at a prime ideal a regular local ring), let $M\\subseteq R$ be a multiplicative subset ($1\\in M$, $st\\in M$ for $s,t\\in M$), and let $\\varphi:R\\to R'$ be a homomorphism of commutative rings which is a localization of $R$ at $M$: (a) $\\varphi(s)$ is a unit for every $s\\in M$; (b) every element of $R'$ is $\\varphi(r)\\varphi(s)^{-1}$ with $r\\in R$, $s\\in M$; (c) $\\varphi(r)=0$ implies $sr=0$ for some $s\\in M$ (for instance $R'=M^{-1}R$). Then $R'$ is a regular ring."
 },
 {
  "step": 2,
  "node": "lem-trf-polynomial-ring-regular-base",
  "quote": "Let $C$ be a commutative regular ring [def-weil-regular-scheme] and let $s\\ge0$. Then the polynomial ring $C[z_1,\\ldots,z_s]$ is a regular ring [def-weil-regular-scheme]."
 },
 {
  "step": 2,
  "node": "lem-per-regular-boundary-divisorial-chart",
  "quote": "Let $Y$ be a regular Noetherian scheme [def-weil-regular-scheme, pqf-def-locnoeth] and $T\\subset Y$ a strict normal crossings boundary [def-trf-strict-normal-crossings-boundary], allowing $T=\\varnothing$. Put $V=Y\\setminus|T|$. The divisorial log structure $M_Y=\\mathcal O_Y\\cap j_*\\mathcal O_V^\\times$, where $j:V\\hookrightarrow Y$, makes $(Y,M_Y)$ a locally Noetherian fine saturated log scheme [def-trf-fs-log-blowup] with triviality locus $V$. At each geometric point $\\bar y$, with strict local ring $A$, it admits a pointed etale-local chart $\\mathbf N^r\\to M_Y$ identifying $\\mathbf N^r$ with its characteristic monoid at $\\bar y$. The standard generators map to $t_1,\\ldots,t_r$ forming part of a regular system of parameters of $A$ [def-weil-pbc-regular-system-of-parameters]. In this chart the ideal generated by nonunits of $M_{Y,\\bar y}$ is $(t_1,\\ldots,t_r)$, its quotient is regular, and $\\dim A=\\dim A/(t_1,\\ldots,t_r)+r$. In particular $(Y,T)$ is a log regular pair [def-trf-log-regular-pair]. No field base or excellence assumption is imposed."
 },
 {
  "step": 2,
  "node": "def-weil-pbc-standard-smooth-algebra",
  "quote": "Let $R$ be a commutative ring and $A$ a commutative $R$-algebra. A *standard smooth presentation* of $A$ over $R$ consists of integers $n\\ge c\\ge0$, polynomials $f_1,\\dots,f_c\\in R[x_1,\\dots,x_n]$ and an isomorphism of $R$-algebras $\\alpha:R[x_1,\\dots,x_n]/(f_1,\\dots,f_c)\\xrightarrow{\\sim}A$ such that the image in $A$ (under $R[x_1,\\dots,x_n]\\to R[x_1,\\dots,x_n]/(f_1,\\dots,f_c)\\xrightarrow{\\alpha}A$) of the determinant $g=\\det\\bigl(\\partial f_j/\\partial x_i\\bigr)_{1\\le i,j\\le c}$ of the $c\\times c$ matrix of formal partial derivatives of $f_1,\\dots,f_c$ with respect to the first $c$ variables is a unit of $A$. The integer $n-c$ is the *relative dimension* of the presentation. The $R$-algebra $A$ (or the ring map $R\\to A$) is *standard smooth* if it has a standard smooth presentation."
 },
 {
  "step": 2,
  "node": "lem-weil-pbc-standard-smooth-is-smooth",
  "quote": "Let $R$ be a commutative ring and $A$ an $R$-algebra which is standard smooth [def-weil-pbc-standard-smooth-algebra]. Then $A$ is a smooth $R$-algebra [def-weil-pbc-smooth-ring-map]."
 },
 {
  "step": 3,
  "node": "lem-per-tame-invariants-arbitrary-base-change",
  "quote": "Let $A$ be a commutative ring, $G$ a finite group of order $d$ with $d\\in A^\\times$, and $M$ an $A$-module with an $A$-linear $G$-action. Write $M^G=\\{m:g(m)=m\\text{ for every }g\\in G\\}$. The $A$-linear operator $e_M=d^{-1}\\sum_{g\\in G}g$ is idempotent, has image $M^G$, and restricts to the identity on $M^G$. For every commutative $A$-algebra $B$, the natural map\n$$B\\otimes_A M^G\\longrightarrow(B\\otimes_A M)^G$$\nis an isomorphism of $B$-modules, with $G$ acting trivially on $B$. It is natural in equivariant module maps and in $B$. If $M=C$ is a commutative $A$-algebra on which $G$ acts by $A$-algebra automorphisms, this comparison is an isomorphism of $B$-algebras\n$$B\\otimes_A C^G\\simeq(B\\otimes_A C)^G.$$\nNeither $B$ nor $C$ is required to be flat over $A$. Tensor products are those of [def-weil-pbc-module-tensor-product]."
 },
 {
  "step": 5,
  "node": "lem-trf-functorial-fan-desingularization",
  "quote": "There exists a smooth-functorial saturated desingularization $\\mathcal R$ of fine torsion-free fans with finite affine covers [def-trf-fine-fan-blowup]. Thus $\\mathcal R(F)$ is a finite tower of saturated blowups along nonempty coherent monoid ideals with smooth last fan, and for a smooth morphism $g:G\\to F$, $\\mathcal R(G)$ is canonically the contraction of $g^*\\mathcal R(F)$, retaining the centers and their order. The identifications respect composition and apply also to open localizations, isomorphisms, and inclusions into finite disjoint unions."
 },
 {
  "step": 5,
  "node": "lem-trf-log-fan-chart-blowup",
  "quote": "(ii) Given any fan chart $c$ of an fs log scheme $(V,N)$ and any finite saturated blowup tower $F_\\bullet\\to F$, there exists a tower $c^*F_\\bullet$ of saturated log blowups of $(V,N)$. At a stage with center $J\\subset\\mathcal P_{F_i}$ its log center is the inverse image in $N_i$ of the ideal generated by $c_i^{-1}J$ in $\\overline N_i$. There are fan charts $c_i:(V_i,\\overline N_i)\\to(F_i,\\mathcal P_{F_i})$ at every level. In particular $\\overline N_{i,\\bar v}\\simeq\\mathcal P_{F_i,c_i(\\bar v)}$. Nonempty coherent centers pull back to nonempty coherent log ideals. These constructions are compatible with composition of fan blowup towers and with strict base change of log schemes; the latter is taken in the fs category."
 },
 {
  "step": 5,
  "node": "lem-trf-strict-fan-chart-local-comparison",
  "quote": "Let $f:(Y,N)\\to(X,M)$ be a strict morphism of fs Zariski log schemes [def-trf-fs-log-blowup, lem-trf-log-fan-chart-blowup], and let $d:(Y,\\overline N)\\to G$ and $c:(X,\\overline M)\\to F$ be fan charts to fine fans [def-trf-fine-fan-blowup]. For each point $y\\in Y$ there is a Zariski neighborhood $U$ of $y$, contained in the inverse images of the affine fan localizations $G_{d(y)}$ and $F_{c(f(y))}$, and an isomorphism of these localized fans $\\lambda:G_{d(y)}\\xrightarrow{\\sim}F_{c(f(y))}$, such that $c\\circ f|_U=\\lambda\\circ d|_U$. Here $F_z$ denotes the affine open subfan of generalizations of $z$, whose sharp monoid of sections is $\\mathcal P_{F,z}$. The induced map on monoids of sections is the map obtained from $\\mathcal P_{F,c(f(y))}\\simeq\\overline M_{f(y)}\\simeq\\overline N_y\\simeq\\mathcal P_{G,d(y)}$."
 },
 {
  "step": 5,
  "node": "lem-trf-functorial-log-blowup-etale-descent",
  "quote": "Consider quasi-compact locally Noetherian fs log schemes [pqf-def-locnoeth, def-trf-fs-log-blowup] with torsion-free characteristic group completions. Suppose a rule $\\mathcal T$ is given on the members admitting a global fan chart [lem-trf-log-fan-chart-blowup]. It assigns a finite ordered tower of saturated log blowups with nonempty coherent log ideal centers. Assume that the assignment is independent of the chosen fan chart, and for every strict etale morphism between these members its source tower is canonically the contracted pullback of its target tower. Here pullback recursively blows up pulled-back ideals and contraction deletes only centers equal to the whole log monoid sheaf. Assume that these comparisons preserve centers and order, respect identities and composition, and that the rule is defined also on finite disjoint unions with the same compatibilities for the component inclusions. Then $\\mathcal T$ extends, uniquely up to the canonical isomorphisms of contracted towers with centers, to all the indicated fs log schemes, with the same strict etale pullback compatibility. The extension is a finite saturated log blowup tower, and its centers are nonempty coherent ideals. Its contracted pullback to each chart neighborhood is the prescribed tower there."
 },
 {
  "step": 5,
  "node": "lem-trf-monoidal-resolution-tower",
  "quote": "Let $(X,M)$ be a fine saturated log scheme [def-trf-fs-log-blowup] whose underlying scheme is quasi-compact and locally Noetherian [pqf-def-locnoeth]; quasi-compact means every open cover has a finite subcover. Suppose every group $\\overline M_{\\bar x}^{\\rm gp}$ is torsion free. Then there exist an integer $n\\geq0$ and a finite tower $(X_n,M_n)\\to\\cdots\\to(X_0,M_0)=(X,M)$ of saturated log blowups along nonempty coherent log ideals such that every characteristic monoid $\\overline M_{n,\\bar x}$ is isomorphic to $\\mathbf N^{r(\\bar x)}$ for some finite integer $r(\\bar x)\\geq0$. This assertion requires neither log regularity nor regularity of the strata."
 },
 {
  "step": 5,
  "node": "lem-per-gabber-absolute-equivariant-modification",
  "quote": "The fourth is the abelian-inertia rigidification construction of VIII 5.3.8--5.5.5: enlarge the boundary locally to a very tame strict normal crossings boundary, resolve its quotient by functorial saturated log blowups, pull back in fs log schemes, and retain only the inverse image of the original boundary. This construction is independent of the auxiliary enlarged boundary and is compatible with strict inertia-preserving morphisms, so the local fourth-stage modifications glue. Strict means the source log structure is pulled back from the target; inertia-preserving means an isomorphism on geometric stabilizers."
 },
 {
  "step": 6,
  "node": "lem-trf-coherent-log-ideal-chart-construction",
  "quote": "Let $(Y,N)$ be a locally Noetherian fs log scheme and $\\mathcal H\\subset N$ a nonempty coherent log ideal [def-trf-fs-log-blowup, pqf-def-locnoeth]. Its algebraized ideal $K=\\alpha(\\mathcal H)\\mathcal O_Y$ is a finite-type quasi-coherent ideal [pqf-def-coherent], and on every strict etale chart $\\operatorname{Spec}A\\to Y$ with fine saturated monoid chart $P\\to A$ and $\\mathcal H$ generated by a finite nonempty set $E\\subset P$, its pullback is $(\\alpha(e):e\\in E)\\subset A$. Use additive notation for $P$, and put $Q_e=\\langle P,h-e\\ (h\\in E)\\rangle\\subset P^{\\mathrm{gp}}$ and $Q_e^{\\mathrm{sat}}=\\{q\\in P^{\\mathrm{gp}}:nq\\in Q_e\\text{ for some }n>0\\}$. Both $Q_e$ and $Q_e^{\\mathrm{sat}}$ are finitely generated integral monoids with group completion $P^{\\mathrm{gp}}$. For a monoid $T$, $\\mathbf Z[T]$ denotes the ring of finite sums of symbols $z^t$ with $z^tz^{t'}=z^{t+t'}$. The fine log schemes with charts\n$$\\operatorname{Spec}(A\\otimes_{\\mathbf Z[P]}\\mathbf Z[Q_e])$$\nglue on their common localizations, and descend along strict etale covers, to a fine log scheme $Y_0\\to Y$ universal for making $\\mathcal H$ locally principal among fine log schemes. Replacing every $Q_e$ by $Q_e^{\\mathrm{sat}}$ gives compatible charts that glue and descend to an fs log scheme $Y_s\\to Y$ with the corresponding universal property among fs log schemes. There is a canonical morphism $s:Y_s\\to Y_0$; it is finite on underlying schemes (preimages of affine opens are spectra of finite algebras). These constructions commute with strict etale restriction. Tensor products are those of [def-weil-pbc-module-tensor-product]. Here a fine log scheme has etale-local charts by finitely generated integral monoids, without a saturation requirement; a log morphism is strict when its source log structure is the one associated to the inverse image of the target log structure and its structure map."
 },
 {
  "step": 6,
  "node": "def-trf-fine-fan-blowup",
  "quote": "A fine fan $(F,\\mathcal P_F)$ is a topological space with a sheaf of sharp monoids locally isomorphic to $(\\operatorname{Spec}_{\\mathrm{mon}}P,\\overline{\\widetilde P})$ for fine $P$; these local models are its affine charts. A morphism $f:(G,\\mathcal P_G)\\to(F,\\mathcal P_F)$ consists of a continuous map and homomorphisms $\\mathcal P_F(U)\\to\\mathcal P_G(f^{-1}U)$ compatible with restrictions, such that the induced homomorphisms on stalks are local. A homomorphism $h:P\\to Q$ is local if $h^{-1}(Q^\\times)=P^\\times$. The fan is torsion free if every group $\\mathcal P_{F,z}^{\\mathrm{gp}}$ has $ng=0$, $n>0$, only for $g=0$; saturated if every stalk is saturated; and smooth if every stalk is isomorphic to $\\mathbf N^r$ for some finite $r\\geq0$. A fan morphism is smooth if every stalk map identifies with the inclusion $P\\to P\\oplus\\mathbf N^r$ for some finite $r\\geq0$."
 },
 {
  "step": 6,
  "node": "lem-weil-subgroup-finite-free-abelian-group-free",
  "quote": "Let $J$ be a finite set and $\\mathbf Z^J$ the free abelian group of functions $J\\to\\mathbf Z$. Every subgroup $N\\subseteq\\mathbf Z^J$ is a free abelian group of finite rank $r\\leq|J|$: there are $e_1,\\ldots,e_r\\in N$ such that every element of $N$ is $\\sum_ia_ie_i$ for unique $a_1,\\ldots,a_r\\in\\mathbf Z$. Consequently an abelian group isomorphic to a subgroup of $\\mathbf Z^J$ is free of finite rank."
 },
 {
  "step": 6,
  "node": "lem-trf-toric-monoid-comparison",
  "quote": "Let $M$ be a fine torsion-free monoscheme with a finite affine cover, let $k$ be a field, and put $X=k[M]$ [def-trf-monoscheme-toric-realization]. On each connected component use its torus $T$. Then:\n\n(i) The map $I\\mapsto k[I]$ is a bijection between coherent monoid ideals of $M$ and coherent $T$-equivariant ring ideals of $X$, allowing the empty monoid ideal to correspond to the zero ring ideal. It commutes with localization and pullback along monoscheme morphisms. The ideal $k[I]$ is the whole structure sheaf exactly when $I=\\mathcal M$, and it is nonzero on a connected component exactly when $I$ is nonempty there.\n\n(ii) For a coherent monoid ideal $I$ nonempty on every component, there is a canonical torus-equivariant identification $\\operatorname{Bl}_{k[I]}(k[M])^\\nu\\simeq k[\\operatorname{Bl}_I(M)^{\\rm sat}]$, with the original dense torus unchanged. The saturated monoscheme blowup is again fine, torsion free and admits a finite affine cover. The identification respects localization and smooth pullback.\n\n(iii) A smooth morphism $N\\to M$ of fine monoschemes induces a smooth morphism $k[N]\\to k[M]$ of schemes. If $k[M]\\to\\operatorname{Spec}k$ is smooth, then $M$ is smooth. In particular, if $k=\\mathbf Q$ and $\\mathbf Q[M]$ is regular, then every stalk of $M$ is $\\mathbf N^r\\oplus\\mathbf Z^t$ for finite $r,t\\ge0$."
 },
 {
  "step": 7,
  "node": "lem-per-very-tame-log-quotient",
  "quote": "Let $(X,M)$ be a Noetherian fs log regular scheme [def-trf-fs-log-blowup] with an admissible, generically free action of a finite group $G$. Admissible means that $X$ is covered by $G$-invariant affine opens; generically free means free on a dense invariant open. Assume the action is very tame: each geometric inertia group has order invertible in the residue field and acts trivially both on the characteristic monoid and on the strict local log stratum $\\operatorname{Spec}(\\mathcal O^{\\rm sh}_{X,\\bar x}/I_{\\bar x})$, with $I_{\\bar x}$ generated by nonunit log sections. Then the scheme quotient $q:X\\to Y=X/G$ exists, is finite surjective with orbit geometric fibres and invariant structure sheaf, and\n$$M_Y=(q_*M)^G$$\nis an fs log regular structure. The log morphism $q$ is Kummer etale: it is log etale in [def-per-fs-log-smooth-etale], and its characteristic monoid maps are injective with every target element having a positive multiple in the image. Etale locally on strict localizations at $\\bar x$ and its image this map is the strict base change of $\\operatorname{Spec}\\mathbf Z[B]\\to\\operatorname{Spec}\\mathbf Z[A]$, for an injective map of fs monoids $A\\to B$ with every element of $B$ having a positive multiple in $A$ and with finite group cokernel annihilated by an integer invertible on the base. If $X\\to S$ is an invariant log morphism, it factors uniquely through $Y\\to S$."
 },
 {
  "step": 7,
  "node": "lem-per-regular-boundary-divisorial-chart",
  "quote": "Let $Y$ be a regular Noetherian scheme [def-weil-regular-scheme, pqf-def-locnoeth] and $T\\subset Y$ a strict normal crossings boundary [def-trf-strict-normal-crossings-boundary], allowing $T=\\varnothing$. Put $V=Y\\setminus|T|$. The divisorial log structure $M_Y=\\mathcal O_Y\\cap j_*\\mathcal O_V^\\times$, where $j:V\\hookrightarrow Y$, makes $(Y,M_Y)$ a locally Noetherian fine saturated log scheme [def-trf-fs-log-blowup] with triviality locus $V$. At each geometric point $\\bar y$, with strict local ring $A$, it admits a pointed etale-local chart $\\mathbf N^r\\to M_Y$ identifying $\\mathbf N^r$ with its characteristic monoid at $\\bar y$. The standard generators map to $t_1,\\ldots,t_r$ forming part of a regular system of parameters of $A$ [def-weil-pbc-regular-system-of-parameters]. In this chart the ideal generated by nonunits of $M_{Y,\\bar y}$ is $(t_1,\\ldots,t_r)$, its quotient is regular, and $\\dim A=\\dim A/(t_1,\\ldots,t_r)+r$. In particular $(Y,T)$ is a log regular pair [def-trf-log-regular-pair]. No field base or excellence assumption is imposed."
 },
 {
  "step": 8,
  "node": "lem-per-very-tame-log-quotient",
  "quote": "Let $(X,M)$ be a Noetherian fs log regular scheme [def-trf-fs-log-blowup] with an admissible, generically free action of a finite group $G$. Admissible means that $X$ is covered by $G$-invariant affine opens; generically free means free on a dense invariant open. Assume the action is very tame: each geometric inertia group has order invertible in the residue field and acts trivially both on the characteristic monoid and on the strict local log stratum $\\operatorname{Spec}(\\mathcal O^{\\rm sh}_{X,\\bar x}/I_{\\bar x})$, with $I_{\\bar x}$ generated by nonunit log sections. Then the scheme quotient $q:X\\to Y=X/G$ exists, is finite surjective with orbit geometric fibres and invariant structure sheaf, and\n$$M_Y=(q_*M)^G$$\nis an fs log regular structure. The log morphism $q$ is Kummer etale: it is log etale in [def-per-fs-log-smooth-etale], and its characteristic monoid maps are injective with every target element having a positive multiple in the image. Etale locally on strict localizations at $\\bar x$ and its image this map is the strict base change of $\\operatorname{Spec}\\mathbf Z[B]\\to\\operatorname{Spec}\\mathbf Z[A]$, for an injective map of fs monoids $A\\to B$ with every element of $B$ having a positive multiple in $A$ and with finite group cokernel annihilated by an integer invertible on the base. If $X\\to S$ is an invariant log morphism, it factors uniquely through $Y\\to S$."
 },
 {
  "step": 10,
  "node": "lem-per-tame-invariants-arbitrary-base-change",
  "quote": "Let $A$ be a commutative ring, $G$ a finite group of order $d$ with $d\\in A^\\times$, and $M$ an $A$-module with an $A$-linear $G$-action. Write $M^G=\\{m:g(m)=m\\text{ for every }g\\in G\\}$. The $A$-linear operator $e_M=d^{-1}\\sum_{g\\in G}g$ is idempotent, has image $M^G$, and restricts to the identity on $M^G$. For every commutative $A$-algebra $B$, the natural map\n$$B\\otimes_A M^G\\longrightarrow(B\\otimes_A M)^G$$\nis an isomorphism of $B$-modules, with $G$ acting trivially on $B$. It is natural in equivariant module maps and in $B$. If $M=C$ is a commutative $A$-algebra on which $G$ acts by $A$-algebra automorphisms, this comparison is an isomorphism of $B$-algebras\n$$B\\otimes_A C^G\\simeq(B\\otimes_A C)^G.$$\nNeither $B$ nor $C$ is required to be flat over $A$. Tensor products are those of [def-weil-pbc-module-tensor-product]."
 },
 {
  "step": 10,
  "node": "lem-trf-log-fan-chart-blowup",
  "quote": "(ii) Given any fan chart $c$ of an fs log scheme $(V,N)$ and any finite saturated blowup tower $F_\\bullet\\to F$, there exists a tower $c^*F_\\bullet$ of saturated log blowups of $(V,N)$. At a stage with center $J\\subset\\mathcal P_{F_i}$ its log center is the inverse image in $N_i$ of the ideal generated by $c_i^{-1}J$ in $\\overline N_i$. There are fan charts $c_i:(V_i,\\overline N_i)\\to(F_i,\\mathcal P_{F_i})$ at every level. In particular $\\overline N_{i,\\bar v}\\simeq\\mathcal P_{F_i,c_i(\\bar v)}$. Nonempty coherent centers pull back to nonempty coherent log ideals. These constructions are compatible with composition of fan blowup towers and with strict base change of log schemes; the latter is taken in the fs category."
 },
 {
  "step": 11,
  "node": "lem-per-very-tame-log-quotient",
  "quote": "Let $(X,M)$ be a Noetherian fs log regular scheme [def-trf-fs-log-blowup] with an admissible, generically free action of a finite group $G$. Admissible means that $X$ is covered by $G$-invariant affine opens; generically free means free on a dense invariant open. Assume the action is very tame: each geometric inertia group has order invertible in the residue field and acts trivially both on the characteristic monoid and on the strict local log stratum $\\operatorname{Spec}(\\mathcal O^{\\rm sh}_{X,\\bar x}/I_{\\bar x})$, with $I_{\\bar x}$ generated by nonunit log sections. Then the scheme quotient $q:X\\to Y=X/G$ exists, is finite surjective with orbit geometric fibres and invariant structure sheaf, and\n$$M_Y=(q_*M)^G$$\nis an fs log regular structure. The log morphism $q$ is Kummer etale: it is log etale in [def-per-fs-log-smooth-etale], and its characteristic monoid maps are injective with every target element having a positive multiple in the image. Etale locally on strict localizations at $\\bar x$ and its image this map is the strict base change of $\\operatorname{Spec}\\mathbf Z[B]\\to\\operatorname{Spec}\\mathbf Z[A]$, for an injective map of fs monoids $A\\to B$ with every element of $B$ having a positive multiple in $A$ and with finite group cokernel annihilated by an integer invertible on the base. If $X\\to S$ is an invariant log morphism, it factors uniquely through $Y\\to S$."
 },
 {
  "step": 11,
  "node": "lem-per-kummer-g-cover-fs-base-change",
  "quote": "Let $C,D,E$ be locally Noetherian fs log schemes [def-trf-fs-log-blowup], let $G$ be a finite group of order invertible on $D$, and let $q:C\\to D$ be a Kummer etale $G$-cover. Here Kummer etale means log etale [def-per-fs-log-smooth-etale] with injective characteristic monoid maps for which every element of the target has a positive multiple in the image. A $G$-cover means that $G$ acts over $D$, $q$ is finite surjective, and the canonical map $\\coprod_{g\\in G}C\\to C\\times_D^{\\rm fs}C$, given on the $g$th copy by $(1,g)$, is an isomorphism. The superscript fs denotes the fibre product in the category of fs log schemes. For any morphism $E\\to D$ for which $C_E=C\\times_D^{\\rm fs}E$ is locally Noetherian, $C_E\\to E$ is again a Kummer etale $G$-cover. Its underlying scheme has quotient $E$: the map is finite surjective with orbit geometric fibres and\n$$\\mathcal O_E\\simeq(q_{E*}\\mathcal O_{C_E})^G.$$\nThe quotient log structure is $M_E\\simeq(q_{E*}M_{C_E})^G$. The constructions and identifications commute with composition of fs base changes. No flatness of $E\\to D$ and no triviality of its log structure is assumed. In particular, the very tame finite quotient of [lem-per-very-tame-log-quotient], when the action is free on the log-triviality locus, is a Kummer etale $G$-cover in this sense, so these conclusions apply to its fs base changes."
 },
 {
  "step": 11,
  "node": "lem-per-inert-etale-quotient-comparison",
  "quote": "Let $G$ be a finite group acting on separated locally Noetherian schemes $U,V$, each covered by invariant affine opens, and let $h:V\\to U$ be a $G$-equivariant etale morphism [def-weil-etale-morphism]. For a geometric point $v$ put $G_v=\\{g:g\\circ v=v\\}$. The locus on which $G_v=G_{h(v)}$ is an invariant open subset of $V$. Restrict to this locus (so $h$ is called inert). Suppose $q_U:U\\to U/G$ and $q_V:V\\to V/G$ are finite surjective scheme quotients with orbit geometric fibres and invariant structure sheaves. Then $\\bar h:V/G\\to U/G$ is etale, and\n$$V\\simeq U\\times_{U/G}(V/G)$$\ncompatibly with the quotient maps and $G$-actions. These assertions hold locally on the quotients, so apply to pointed etale neighborhoods and are compatible with composition.\n\nIn addition suppose $M_U,M_V$ are fs log structures [def-trf-fs-log-blowup], $h$ is strict, both actions are very tame, and their quotient log structures are $N_U=(q_{U*}M_U)^G$ and $N_V=(q_{V*}M_V)^G$. Here strict means that the source log structure is pulled back from the target; very tame means that geometric stabilizers have invertible order and act trivially on the characteristic monoid and the strict local log stratum (the quotient of the strict local ring by the images of nonunit log sections). Then $\\bar h$ is strict for $N_V,N_U$."
 },
 {
  "step": 11,
  "node": "lem-per-log-smooth-invertible-torsion-log-regular",
  "quote": "Let $f:(X,M_X)\\to(Y,M_Y)$ be a morphism of locally Noetherian fine saturated log schemes in the sense of [def-trf-fs-log-blowup]. Suppose $(Y,M_Y)$ is log regular in the stratum and dimension sense of that definition. Assume that etale locally on source and target there are compatible fs charts $A\\to M_Y$, $B\\to M_X$ and a homomorphism $h:A\\to B$ for which $h^{\\rm gp}$ is injective, the torsion subgroup of its cokernel is finite of order invertible on the source, and the induced scheme morphism $X\\to Y\\times_{\\operatorname{Spec}\\mathbf Z[A]}\\operatorname{Spec}\\mathbf Z[B]$ is smooth [def-sbc-smooth-morphisms]. Here $\\mathbf Z[C]$ denotes the monoid ring, free as an abelian group on symbols $z^c$ with $z^cz^{c\\prime}=z^{c+c\\prime}$. This is the chart meaning of log smooth in this statement. Then $(X,M_X)$ is log regular in the same sense. In particular the cokernel in the chart condition is allowed to have nonzero torsion of invertible order; it need not be torsion-free."
 },
 {
  "step": 12,
  "node": "lem-trf-log-fan-chart-blowup",
  "quote": "(ii) Given any fan chart $c$ of an fs log scheme $(V,N)$ and any finite saturated blowup tower $F_\\bullet\\to F$, there exists a tower $c^*F_\\bullet$ of saturated log blowups of $(V,N)$. At a stage with center $J\\subset\\mathcal P_{F_i}$ its log center is the inverse image in $N_i$ of the ideal generated by $c_i^{-1}J$ in $\\overline N_i$. There are fan charts $c_i:(V_i,\\overline N_i)\\to(F_i,\\mathcal P_{F_i})$ at every level. In particular $\\overline N_{i,\\bar v}\\simeq\\mathcal P_{F_i,c_i(\\bar v)}$. Nonempty coherent centers pull back to nonempty coherent log ideals. These constructions are compatible with composition of fan blowup towers and with strict base change of log schemes; the latter is taken in the fs category."
 },
 {
  "step": 12,
  "node": "lem-per-inert-etale-quotient-comparison",
  "quote": "Let $G$ be a finite group acting on separated locally Noetherian schemes $U,V$, each covered by invariant affine opens, and let $h:V\\to U$ be a $G$-equivariant etale morphism [def-weil-etale-morphism]. For a geometric point $v$ put $G_v=\\{g:g\\circ v=v\\}$. The locus on which $G_v=G_{h(v)}$ is an invariant open subset of $V$. Restrict to this locus (so $h$ is called inert). Suppose $q_U:U\\to U/G$ and $q_V:V\\to V/G$ are finite surjective scheme quotients with orbit geometric fibres and invariant structure sheaves. Then $\\bar h:V/G\\to U/G$ is etale, and\n$$V\\simeq U\\times_{U/G}(V/G)$$\ncompatibly with the quotient maps and $G$-actions. These assertions hold locally on the quotients, so apply to pointed etale neighborhoods and are compatible with composition.\n\nIn addition suppose $M_U,M_V$ are fs log structures [def-trf-fs-log-blowup], $h$ is strict, both actions are very tame, and their quotient log structures are $N_U=(q_{U*}M_U)^G$ and $N_V=(q_{V*}M_V)^G$. Here strict means that the source log structure is pulled back from the target; very tame means that geometric stabilizers have invertible order and act trivially on the characteristic monoid and the strict local log stratum (the quotient of the strict local ring by the images of nonunit log sections). Then $\\bar h$ is strict for $N_V,N_U$."
 },
 {
  "step": 12,
  "node": "lem-trf-functorial-log-blowup-etale-descent",
  "quote": "Consider quasi-compact locally Noetherian fs log schemes [pqf-def-locnoeth, def-trf-fs-log-blowup] with torsion-free characteristic group completions. Suppose a rule $\\mathcal T$ is given on the members admitting a global fan chart [lem-trf-log-fan-chart-blowup]. It assigns a finite ordered tower of saturated log blowups with nonempty coherent log ideal centers. Assume that the assignment is independent of the chosen fan chart, and for every strict etale morphism between these members its source tower is canonically the contracted pullback of its target tower. Here pullback recursively blows up pulled-back ideals and contraction deletes only centers equal to the whole log monoid sheaf. Assume that these comparisons preserve centers and order, respect identities and composition, and that the rule is defined also on finite disjoint unions with the same compatibilities for the component inclusions. Then $\\mathcal T$ extends, uniquely up to the canonical isomorphisms of contracted towers with centers, to all the indicated fs log schemes, with the same strict etale pullback compatibility. The extension is a finite saturated log blowup tower, and its centers are nonempty coherent ideals. Its contracted pullback to each chart neighborhood is the prescribed tower there."
 },
 {
  "step": 12,
  "node": "lem-per-gabber-absolute-equivariant-modification",
  "quote": "The fourth is the abelian-inertia rigidification construction of VIII 5.3.8--5.5.5: enlarge the boundary locally to a very tame strict normal crossings boundary, resolve its quotient by functorial saturated log blowups, pull back in fs log schemes, and retain only the inverse image of the original boundary. This construction is independent of the auxiliary enlarged boundary and is compatible with strict inertia-preserving morphisms, so the local fourth-stage modifications glue. Strict means the source log structure is pulled back from the target; inertia-preserving means an isomorphism on geometric stabilizers."
 }
]
```
