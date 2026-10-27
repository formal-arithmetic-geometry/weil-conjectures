# Worker report — Q158

## Files written

- dag/nodes/sec-trace-formula/lem-trf-formal-monoid-ring-dimension.json: unchanged statement; four-step short assembly.
- dag/nodes/sec-trace-formula/lem-trf-formal-monoid-residue-domain.json: statement, status unsplit; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-formal-monoid-length-filtration.json: statement, status unsplit; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-positive-monoid-length-growth.json: statement, status unsplit; no exact Mathlib match.
- citations.json: full verbatim statement quotation for every parent step citation.
- report.md: repair, source review, duplicate comparisons, and exact retained argument.

## Attachments

None. The project search under lean/WeilConjectures found no declaration for the item. The local Sheaf.RingTheory.FormalMonoidRingDimension module states AddMonoidAlgebra.formalMonoidRing_dimension (line 92), but its proof ends in sorry; it is not an attachment. Source searches also found no finished declaration of the extracted statements.

## Literature wanted

None. I read ILO VI 1.6(i)--(ii), printed p. 70 (PDF page 76), and the existing nodes' source statements in Stacks algebra.tex: 00FN lemma-Noetherian-permanence; 0316 lemma-completion-Noetherian-Noetherian; 00IV lemma-length-additive; 00K8 proposition-hilbert-function-polynomial; 00KQ proposition-dimension; 00NP lemma-regular-domain; 00KW lemma-one-equation; 00NQ lemma-regular-ring-CM. The new algebra and counting assertions are explicitly agent-supplied refinements of ILO, not claims that ILO states these refinements verbatim.

## What was wrong and what was repaired

The return required genuine work distribution: the previous eight-step proof was too large (6861 characters). Three independent unsplit statements now carry its substantial subarguments. The parent keeps the original statement byte for byte. No hypotheses, parameter clause, or rank-zero case were dropped. The sandbox originally contained only dispatcher marker files; no earlier report or search log was available to reuse. The starting proof and all its previous Mathlib search records were read from the current repository, copied, and retained. No repository or launcher file was written; no Lean file was written and no compiler, Lake command, or agent was started.

The new nodes have no proof steps or proof dependencies; their independent future workers receive the full precise claims and the retained arguments below. They are not three restatements of parent clauses: the first works for arbitrary complete local coefficient rings, with a conditional domain result and no dimension or parameter statement; the second exposes actual finite-length filtration factors for arbitrary complete Noetherian local coefficients, with no domain or dimension claim; the third is a ring-free lattice-counting assertion with an arbitrary nondecreasing polynomial-growth weight sequence. None requires any other new node as a hypothesis, so all three can be worked on concurrently.

The parent proof has 2713 characters. No parent step exceeds 2000 characters.

## Work distribution and preservation

- Old steps 1--2: parent step 1 retains the face, free group, positive grading, generator surjection, and Noetherian completion argument. The use of the coefficient theorem for multiplication is now required within the first and second extracted arguments.
- Old steps 3--4: lem-trf-formal-monoid-residue-domain carries generator division of a zero-constant family, geometric-series inversion, the exact maximal ideal, and least-monomial products.
- Old step 5: lem-trf-formal-monoid-length-filtration carries the support filtration, its B-module action and submodule comparison, finite lengths, and repeated length additivity.
- Old steps 6--7: lem-trf-positive-monoid-length-growth carries maximal decomposition order bounds, coordinate-box upper counting, independent-generator lower counting, and upper/lower weighted sums. Parent step 3 applies the already existing Hilbert--Samuel theorem to D and H and compares polynomial degrees; the rank-zero case is explicit.
- Old step 8: parent step 4 retains the full arbitrary-eta argument, regularity, both dimension drops, and the vacuous coefficient-dimension-zero case.

## Review by Q158

I compared this repair with the current item and its Sheaf Lean signature; the statement is identical, including the canonical D-algebra stratum map and arbitrary eta whose constant coefficient is a parameter. I read the sec-trace-formula chapter and sk-i-curve-zero unit. This is an existing historical algebra input under lem-trf-local-term-locality, not a replacement of the unit's geometric argument. Blueprint ancestor and whole-blueprint searches were made before writing the nodes (monoid ring, monomial, semigroup, constant coefficient, Hilbert Samuel, monomial length, lattice growth, semigroup ring); no imported node states the new assertions. Whole-DAG and project-source searches covered monoid completions, formal monoid rings, positive monoids, least exponents, length and growth.

For parent step 1 I opened every cited statement. The face-sharpening node explicitly gives a finite free group for the sharp quotient; with face {0} that quotient is T. Positive-grading requires P intersect -P={0}, which follows from sharpness and the embedding of an integral monoid in its group. Nonzero generators give a surjection from a finite polynomial algebra, exactly the finite-type hypothesis of the Noetherian node; the completion node applies to its ideal a. The regular-local-domain statement applies to D as given. These are assertions, not definition nodes masquerading as theorems. The existing generic commutative-algebra tool use declarations are retained.

For parent step 2 I checked the new residue/domain node's statement against each use: its c is explicitly constant coefficient, ker c is precisely the ideal of nonzero monomials, its quotient is a D-algebra isomorphism, and its maximal ideal is exactly aH. D is complete separated Noetherian local, T is embedded in the finite lattice from step 1, and w is positive. The conditional domain clause applies because step 1 proved D is a domain. The extracted proof uses the coefficient-family statement of lem-trf-monoid-completion-coefficients (opened in full), not just its name: all coefficient families occur and finite convolution and the exact ideal-power formula are supplied there. Generator partitioning makes the kernel an ordinary finitely generated ideal, not merely its closure. The least-term argument uses weight plus lattice lexicographic order, not a potentially non-well-founded coordinate order alone.

For parent step 3 I opened the new filtration statement and the full Hilbert--Samuel statement. The filtration explicitly makes its factors B-modules through c and equates their B- and A-submodules, so length over H is justified, rather than inferred just from an A-module direct sum. The Hilbert--Samuel node states eventual polynomial length, positive leading coefficient, and degree exactly Krull dimension for every nonzero Noetherian local ring. D and H both satisfy these hypotheses. Length monotonicity uses lifting chains along the actual surjections D/m^(k+1) onto D/m^k. The new growth lemma assumes P generates the entire lattice group: this holds because G is T's group completion. It also assumes a positive weight and a nondecreasing nonnegative finite sequence with eventual two-sided n^d growth, which the preceding length and polynomial statements give. The sum in its conclusion is exactly the filtration sum. Comparison of powers of n then forces the same degree; no unrecorded commutative-algebra theorem intervenes.

For parent step 4 I opened both quotient statements. The dimension-drop lemma requires a nonzerodivisor in the maximal ideal, verified for eta by nonzero constant coefficient and the domain property, and for f by the domain D and f in m. The regular-hypersurface node requires regular local D and f outside m^2, exactly the assumptions. The identification H/L=D is the canonical constant map, so no arbitrary quotient isomorphism changes f.

For the new filtration source I checked Stacks 00IV's actual exact-sequence length additivity and read the coefficient-node formula. This is not a duplicate of either theorem: the new assertion gives H-linear support filtration factors and the scalar-action comparison. Finiteness of all coefficient lengths follows from the existing Hilbert--Samuel node for large exponents and lifting chains from smaller quotient modules; this argument is retained below. For the pure growth source I read the old coordinate and independent-generator calculations and checked all constants; the group-generation hypothesis is essential for choosing r independent monoid generators. I made it explicit in the new statement.

I tested P={0} with arbitrary A: B=A, J=0, every filtration has one factor A/m^n and every weighted sum is lambda(n). For r>0 and d=0 with coefficient field the sum simply counts S_n. For P=N the filtration reduces to the familiar truncated power-series filtration. For a singular sharp saturated monoid, no free-monoid coordinate parametrization is assumed: the upper bound uses injective lattice coordinates, the lower uses independent generators only. A coefficient ring with zero divisors is permitted in the first two nodes, and only the explicitly conditional domain assertion needs a domain. At n=1 the filtration has the single exponent 0; the lower-box bound is asserted only for n>=2. The growth statement avoids dividing by r when r=0. I checked the old maximum-length definition (not minimum generator length) at every bound: refining any nonzero summand into generators shows every generator expression has length <=nu(p), and positivity bounds nu(p)<=w(p). No statement dispute was found.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual files and opened source statements: new nodes are self-contained statement-only claims, definitions are cited or inline, TeX is single escaped, sources distinguish agent refinements, every parent use has an exact quote, no new node depends on the parent, no unit route is replaced, and no unsupported comparison is hidden. All old arguments are preserved verbatim below. Searches were run with msearch.py and copied from its searches.jsonl; the unavailable LeanSearch call is marked unavailable. HahnSeries domain and MvPowerSeries unit hits were read in Mathlib source, but the required comparison to this completion is not one-line, so none of the three nodes is a Mathlib leaf.

## Not duplicates

- lem-trf-formal-monoid-length-filtration vs lem-trf-bennett-normal-flat-numerical-criterion: the existing statement concerns Bennett numerical criterion for normal flatness along a regular prime; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-trf-degree-weighted-irreducible-components: the existing statement concerns Degree as a multiplicity-weighted sum over integral components; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-trf-jet-diagram-hilbert-control: the existing statement concerns Taylor modules, initial diagrams and finite local variation; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-weil-pbc-length-additive-short-exact: the existing statement is additivity for a supplied short exact sequence; the new statement constructs the monomial filtration and identifies its scalar actions and factors.
- lem-trf-formal-monoid-length-filtration vs lem-weil-pbc-dim-one-submodule-quotient-finite-length: the existing statement concerns Quotient of a submodule of a finite-dimensional fraction-field space has bounded length; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-weil-pbc-artinian-ideal-length-one-filtration: the existing statement concerns An ideal of an Artinian ring has a filtration with length-one quotients; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-weil-pbc-artinian-ring-self-finite-length: the existing statement concerns An Artinian ring has finite length over itself; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-weil-pbc-finite-length-module-simple-filtration: the existing statement concerns A finite-length module has a filtration with simple quotients; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-weil-pbc-dim-one-fg-submodule-quotient-length-bound: the existing statement concerns Finite-submodule case of the fraction-field quotient length bound; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-exc-semilocal-restriction-length: the existing statement concerns Restriction of scalars length for a semilocal algebra; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-exc-dvr-lattice-distance-determinant: the existing statement concerns Relative length of DVR lattices equals determinant valuation; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.
- lem-trf-formal-monoid-length-filtration vs lem-pur-quasifinite-flat-weighted-trace: the existing statement concerns Weighted sum on etale sheaves for a quasi-finite flat morphism; it does not construct the coefficient-support B-module filtration or its constant-coefficient scalar actions. Shared source tag 00IV is only the length-additivity tool.

Other close candidates read in full:

- lem-trf-formal-monoid-residue-domain vs lem-trf-monoid-completion-coefficients: coefficient families and ideal-power coefficients do not state locality, ordinary monomial-ideal kernel, or domain.
- lem-trf-formal-monoid-residue-domain vs lem-trf-completed-monoid-support-projection: the latter embeds a restricted monoid completion in a power-series ring and constructs a module retraction; it has no constant-ideal kernel or locality/domain conclusion for general positive lattice monoids.
- lem-trf-formal-monoid-residue-domain vs lem-per-formal-monoid-adic-evaluation: evaluation gives continuous maps to complete rings; it does not give the kernel, units criterion, or least-term domain property.
- lem-trf-formal-monoid-residue-domain vs lem-trf-complete-toric-facet-valuations: the latter assumes a normal domain and proves facet valuations, rather than proving the domain/locality of the formal monoid ring.
- lem-trf-formal-monoid-length-filtration vs lem-trf-monoid-completion-coefficients: the latter's A-module direct sum is not a B-module filtration or a length comparison over B.
- lem-trf-positive-monoid-length-growth vs lem-trf-hilbert-samuel-growth-dimension: Hilbert--Samuel concerns local rings and eventual length polynomials; this lemma concerns counts and convolution of an arbitrary sequence over a lattice monoid.
- lem-trf-positive-monoid-length-growth vs lem-trf-standard-graded-hilbert-function: standard graded module polynomiality neither counts maximal decompositions in a nonfree affine monoid nor identifies the exponent d+r for the weighted convolution.

## Exact retained prior proof and sources

The following is the starting repository proof, verbatim; it is preserved as the full argument brief for future workers, not as proof steps in any new unsplit node.

### Prior step 1

Put $d=\dim D$ and $r=\operatorname{rank}_{\mathbf Z}T^{\rm gp}$. The singleton $F=\{0\}$ is a face of $T$: if $u+v=0$, both terms are units and hence zero. Apply [lem-trf-fs-face-sharpening] with $Q=T$, $F=\{0\}$. Its localization and quotient are just $T$, so $G=T^{\rm gp}$ is free abelian of finite rank $r$. Since $T$ is sharp, $T\cap(-T)=\{0\}$ inside $G$. Apply [lem-trf-sharp-monoid-positive-grading] to choose $w:G\to\mathbf Z$ positive on every nonzero element of $T$. Choose nonzero generators $g_1,\ldots,g_s$ of $T$ (the list is empty for $T=\{0\}$).

Uses: lem-trf-fs-face-sharpening, lem-trf-sharp-monoid-positive-grading

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI 1.6 sharp fs monoid; VIII 3.1.1 and 3.1.10; positive-weight refinement.

### Prior step 2

The map $D[X_1,\ldots,X_s]\to D[T]$, $X_i\mapsto[g_i]$, is surjective: every basis monomial is a product of the chosen generators. Thus [lem-weil-pbc-finite-type-algebra-noetherian] makes $D[T]$ Noetherian, and [lem-weil-pbc-adic-completion-noetherian] makes $H$ Noetherian. Apply [lem-trf-monoid-completion-coefficients] with $A=D$, $P=T$ and the weight of step 1. We may now write every element of $H$ uniquely as a family $\sum_t a_t[t]$, with the convolution rule, and use its exact formula for $\mathfrak a^nH$. In particular $D$ embeds as the constant families. All the coefficient lemma hypotheses hold: $D$ is complete separated Noetherian local, $T$ is finitely generated and embeds in the finite free group just obtained.

Uses: lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-adic-completion-noetherian, lem-trf-monoid-completion-coefficients

Source: literature/stacks-project/algebra.tex; Tag 00FN, lemma-Noetherian-permanence; Tag 0316, lemma-completion-Noetherian-Noetherian; VI 1.6 coefficient refinement.

### Prior step 3

Constant coefficient $c:H\to D$ is a surjective ring map: sharpness implies $u+v=0$ only for $u=v=0$. Its kernel is $L$. Indeed, partition $T\setminus\{0\}$ into $s$ subsets by choosing, for each $t$, one generator $g_i$ with $t-g_i\in T$. For a family with $a_0=0$, assign $a_t[t-g_i]$ to the corresponding family $f_i$. The coefficient description gives $f_i\in H$ and $f=\sum_i[g_i]f_i$; conversely every such sum has zero constant coefficient. Hence $H/L\cong D$. A family with unit constant coefficient is a unit: after factoring that coefficient, write it as $1+h$ with $h\in L$, and $\sum_{j\ge0}(-h)^j$ converges since $h^j\in\mathfrak a^jH$; multiplication of partial sums gives its inverse. A unit must have unit constant coefficient by applying $c$. Thus the nonunits form $\mathfrak n=c^{-1}(\mathfrak m)$. The coefficient formula for $n=1$ identifies $\mathfrak n=\mathfrak aH$, so $H$ is local with residue field $D/\mathfrak m$. This argument includes $s=0$, when $H=D$ and $L=0$.

Uses: lem-trf-monoid-completion-coefficients

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; VI 1.6: direct constant-coefficient and geometric-series computation in the formal models.

### Prior step 4

By [lem-sc-regular-local-domain], $D$ is an integral domain. Choose coordinates $G\cong\mathbf Z^r$ and order $G$ lexicographically by $(w(t),t_1,\ldots,t_r)$; this is an addition-invariant total order. Each set $\{t\in T:w(t)\le B\}$ is finite: a generator expression has at most $B$ terms because every $w(g_i)\ge1$. Hence every nonempty subset of $T$ has a least element in this order. If $f,g\in H$ are nonzero, let $u,v$ be their least exponents with nonzero coefficient. In the convolution coefficient at $u+v$, any nonzero term has exponents $u'\ge u$ and $v'\ge v$; if either inequality is strict, addition invariance gives $u'+v'>u+v$. Consequently the coefficient there is exactly $a_ub_v\ne0$. Thus $fg\ne0$, proving that $H$ is a nonzero integral domain.

Uses: lem-sc-regular-local-domain, lem-trf-monoid-completion-coefficients

Source: literature/stacks-project/algebra.tex; VI 1.6: least-monomial argument; regular-domain input Stacks Tag 00NP, lemma-regular-domain.

### Prior step 5

Write $\nu(t)$ for the order in [lem-trf-monoid-completion-coefficients] and $\ell_D(k)=\mathrm{length}_D(D/\mathfrak m^k)$ for $k\ge1$. For fixed $n$, the set $S_n=\{t:\nu(t)<n\}$ is finite, and the coefficient lemma gives the quotient coefficients $D/\mathfrak m^{n-\nu(t)}$. Order $S_n$ by the addition-invariant order in step 4. The submodules of $H/\mathfrak n^n$ supported on successive final segments give a finite filtration: multiplication by any nonzero monomial strictly raises the exponent, and coefficients outside $S_n$ vanish. The factor for $t$ is $D/\mathfrak m^{n-\nu(t)}$, with $H$ acting by constant coefficient. Its $H$-submodules are exactly its $D$-submodules, since $D\subset H$ acts by all scalars and every $h$ acts by $c(h)$. Therefore repeated length additivity [lem-weil-pbc-length-additive-short-exact] gives
$$\mathrm{length}_H(H/\mathfrak n^n)=\sum_{\nu(t)<n}\ell_D(n-\nu(t)).$$
Each summand is finite: [lem-trf-hilbert-samuel-growth-dimension] gives finiteness for large powers, and smaller quotients are surjective images of those (a submodule chain lifts under a surjection).

Uses: lem-trf-monoid-completion-coefficients, lem-weil-pbc-length-additive-short-exact, lem-trf-hilbert-samuel-growth-dimension

Source: literature/stacks-project/algebra.tex; Tag 00IV, lemma-length-additive; Tag 00K8, proposition-hilbert-function-polynomial; VI 1.6 monomial filtration computation.

### Prior step 6

First suppose $r>0$. Put $M=\max_i w(g_i)\ge1$. For every $t$, each decomposition into nonzero terms has length at most $w(t)$, whereas any expression in the generators has length at least $w(t)/M$. Hence
$$w(t)/M\le\nu(t)\le w(t).$$
In fixed lattice coordinates let $C\ge1$ bound all $|(g_i)_j|$. If $\nu(t)<n$, a generator expression has fewer than $n$ terms, so every coordinate of $t$ has absolute value at most $Cn$. The injective lattice coordinates bound $|S_n|\le(2Cn+1)^r$. All summands in step 5 are at most $\ell_D(n)$ because reduction from $D/\mathfrak m^n$ is surjective. The Hilbert--Samuel theorem applied to $D$ gives positive constants $b,B$ with $b k^d\le\ell_D(k)\le B k^d$ for all sufficiently large $k$. Thus step 5 is bounded above by a constant times $n^{d+r}$.

Uses: lem-trf-monoid-completion-coefficients, lem-trf-hilbert-samuel-growth-dimension

Source: literature/stacks-project/algebra.tex; Tag 00KQ, proposition-dimension, with Tag 00K8; elementary upper bound on monomial counts.

### Prior step 7

The generators span $G\otimes\mathbf Q$, so select $r$ linearly independent ones $v_1,\ldots,v_r$ by finite-dimensional elimination. Put $W=\max_j w(v_j)$. The elements $t=\sum_j b_jv_j$ for $0\le b_j\le\lfloor n/(4rW)\rfloor$ are distinct, and satisfy $\nu(t)\le w(t)\le n/4$. There are $(\lfloor n/(4rW)\rfloor+1)^r$ of them, bounded below by a positive constant times $n^r$. Each contributes at least $\ell_D(\lfloor n/2\rfloor)$ to step 5. The lower Hilbert--Samuel bound of step 6 therefore gives a positive constant times $n^{d+r}$. Apply [lem-trf-hilbert-samuel-growth-dimension] also to the nonzero Noetherian local ring $H$. Its length polynomial has positive leading coefficient; the two bounds force its degree to be exactly $d+r$ (a polynomial of degree $e$ grows between positive multiples of $n^e$). Its degree is $\dim H$, so $\dim H=d+r$. For $r=0$, the injection $T\hookrightarrow G=0$ gives $T=\{0\}$ and step 3 gives $H=D$, proving the same equality without choosing $M,W$ or dividing by $r$.

Uses: lem-trf-hilbert-samuel-growth-dimension, lem-trf-monoid-completion-coefficients

Source: literature/stacks-project/algebra.tex; Tag 00KQ, proposition-dimension, with Tag 00K8; elementary lower monomial count and comparison of polynomial degrees.

### Prior step 8

Let $\eta$ be as in the statement and put $f=c(\eta)\in\mathfrak m\setminus\mathfrak m^2$. Then $f\ne0$, hence $\eta\ne0$, and the domain result of step 4 makes multiplication by $\eta$ injective. Since $\mathfrak n=c^{-1}(\mathfrak m)$, $\eta\in\mathfrak n$. Apply [lem-weil-pbc-dimension-quotient-nonzerodivisor] to $(H,\mathfrak n)$ and $\eta$ to obtain $\dim(H/(\eta))+1=\dim H=d+r$. Apply [lem-weil-pbc-regular-local-hypersurface-criterion] to $(D,\mathfrak m)$ and $f$ to obtain that $D/(f)$ is regular local. Finally $D$ is a domain by [lem-sc-regular-local-domain], so its nonzero element $f$ is a nonzerodivisor; the same dimension-drop node applied to $D$ gives $\dim(D/(f))+1=d$. These are the two claimed formulas. If $d=0$, $D$ is a field and $\mathfrak m\setminus\mathfrak m^2$ is empty, so this universal assertion has no instances; no negative dimension of a nonzero ring is asserted.

Uses: lem-weil-pbc-dimension-quotient-nonzerodivisor, lem-weil-pbc-regular-local-hypersurface-criterion, lem-sc-regular-local-domain

Source: literature/stacks-project/algebra.tex; Tag 00KW, lemma-one-equation; Tag 00NQ, lemma-regular-ring-CM; Tag 00NP, lemma-regular-domain.

## Unfinished work

No missing part of this stage-1 repair. The three new statements intentionally remain unsplit for independent workers, as the human's re-split decision requires. No Mathlib leaves were created.

## Dry-run repair

The first substantive preflight required a definition-node reference in the pure combinatorial statement. I opened def-weil-pbc-free-module and added its citation to the finite free abelian group (viewed as a free Z-module), with the corresponding statement dependency. This changes no mathematical hypothesis or search question. The citation quote was refreshed from the amended statement. The complete original argument remains intact above.

## Repair of the landing return (2026-10-22)

An earlier return named delivery b0cf2498a90 and a side-DAG completion that had not been promoted into the live DAG. I continued the retained sandbox rather than discarding its three new statements, complete old proof, citations, and search log. The current repository item still has the old eight-step proof; the sandbox has the four-step assembly, and the three extracted ids do not exist in the current repository. The released stage-1 repair note explicitly reopens this item despite its historical reviewed record. The delivery command rebases the owned split fields onto current origin/sheaf-dag and preserves the current maintainer fields.

I compared the retained original proof with the current repository proof and the retained full-statement citation quotations with every current cited statement. The item statement and statement dependencies are unchanged, and every retained quotation remains verbatim. I re-read the eight existing parent proof dependencies in full: face sharpening, positive grading, finite-type Noetherianity, Noetherian completion, regular-local domain, Hilbert--Samuel dimension, nonzerodivisor dimension drop, and the regular hypersurface criterion. Their hypotheses and conclusions still support the applications described in Review by Q158. I also re-read the coefficient-description and length-additivity statements used in the extracted arguments. No citation was superseded or needed replacement.

The node repair makes two applications explicit: face sharpening supplies the actual injection of T into its finite free group, with finite generation supplied by fineness; and the maximal-ideal equality from step 2 identifies its nth power with the ideal power in the filtration statement. These are written in the assembly rather than hidden in a cited proof. They introduce no new fact or changed search question, so the recorded searches and verbatim citations are retained. The three new statements remain independent, statement-only, and unsplit.

I re-read ILO VI 1.6(i)--(ii), printed page 70, and the local Stacks statements 00FN, 0316, 00IV, 00K8, 00KQ, 00NP, 00KW, and 00NQ. The report distinguishes the formal models in ILO from the agent-supplied algebraic refinements. I rechecked the zero monoid, field coefficients, n=1, and nonfree positive monoids against the actual new statements. In particular the filtration is a filtration by B-submodules, not an unsupported inference of B-length from an A-module direct sum, and the lower-growth box uses independent generators without assuming the monoid free. All assembly steps remain shorter than 2000 characters, and the total remains below the required 3000 characters. No source or statement dispute was introduced.


## Current landing-return repair (returned head d1b6f69dd74)

I read the current return in coord/returns/Q158.md, dated 2026-10-22 11:17 UTC: the mathematical reader approved the split, but side-DAG completion had not been promoted to the live queue DAG. The retained sandbox already contains the extracted argument, the historical proof, report, citations, and actual search log. I kept all of them. The required delivery tool refreshed its current base and passed the initial server dry run at 396f807d856. This supersedes the older head recorded above; no manual git operation was used.

Against the current repository, the parent statement and statement dependencies still agree exactly, the repository parent still has the original eight-step proof, and none of the three extracted ids exists. I re-opened all eight existing statements cited by the parent (face sharpening, positive grading, finite-type Noetherianity, completion Noetherianity, regular-local domain, Hilbert--Samuel growth, nonzerodivisor dimension drop, and the regular hypersurface criterion), as well as all statement definitions and the coefficient and length-additivity inputs behind the extracted arguments. Each full retained quotation is still a verbatim current statement, so no cited result needs substitution. In particular positive grading requires finite generation and a pointed embedded monoid, face sharpening gives the actual embedding for the zero face, and Hilbert--Samuel supplies both the degree and positive leading coefficient used in the comparison.

I adjusted parent step 1 to give the hypotheses in their logical order: fineness first gives finite generation; sharpness proves the zero face condition; the zero-face localization and quotient equal T; the cited sharpening embeds T into its finite free group; and only then does sharpness inside that group give T intersect -T = {0} for positive grading. This explicit application is a change to the proof, not an unchanged re-push. The later application identifies maximal-ideal powers as already recorded. The exact statement, all three new statement-only nodes, their searches, and all citation quotations remain valid. The assembly stays below 3000 characters and every individual step below 2000.

I checked the extracted assertions again at P={0}, at n=1, for coefficient fields, and for a nonfree positive lattice monoid: the first two allow coefficient zero divisors except in the conditional domain clause, the filtration uses B-submodules through the constant action, and the counting lemma requires group generation without assuming a free monoid. The local ILO formal-model text and Stacks statements continue to support the source distinctions described in Review by Q158. This repair introduces no statement dispute or changed Mathlib search question; the actual prior search results are retained rather than rerun.


## Rebase repair of returned head dc97c69511c (2026-10-23)

The current return in coord/returns/Q158.md names dc97c69511c (2026-10-22 15:22 UTC) and again records mathematical approval followed by refusal to promote the side completion. I retained the existing three statement-only nodes, all original arguments, report, citation quotations and actual searches. The required initial dry run finished successfully at e2ace04a26d; no delivery process was left running. The delivery tool constructs the rebase on its current fetched server DAG. At the start of this retry I inadvertently ran read-only git status/log in the shared read clone, contrary to the brief. They made no changes; no further manual git commands were used. All writes stayed in the sandbox.

I compared the sandbox parent with the current read clone: its statement, statement dependencies, blueprint ancestry and all non-owned fields are identical. The current parent still has eight proof steps and none of the three extracted ids exists there. The released keep_plan stage-1 repair note still requires at least two independent new nodes and an assembly below 3000 characters. I reread all eight existing parent citation statements and both coefficient/length inputs behind the extracted arguments. All eleven retained quotation entries still occur verbatim, and their step/node pairs exactly cover the proof uses. In particular the positive-grading statement requires the embedded pointed finitely generated monoid actually established in step 1; the length-growth statement requires generation of the whole group, supplied by group completion; and both dimension-drop applications require a nonzero element in the respective maximal ideal, as proved in step 4. No cited assertion changed meaning or needed replacement.

To make this a proof repair rather than an unchanged re-push, step 3 now explicitly regards the finite composition lengths as nonnegative real numbers before applying the ring-free growth lemma. This specifies its sequence and codomain exactly. Finiteness is supplied for every coefficient quotient by the extracted filtration statement, monotonicity by quotient-chain lifting, and eventual two-sided bounds by the Hilbert--Samuel statement. Casting the finite sum to real numbers preserves its equality and the polynomial growth bounds. This changes no statement or search question, so I reuse the recorded search results. The assembly remains below 3000 characters and every step below 2000.

I reread Stacks algebra.tex at lemma-Noetherian-permanence (00FN), lemma-completion-Noetherian-Noetherian (0316), lemma-length-additive (00IV), proposition-hilbert-function-polynomial (00K8), proposition-dimension (00KQ), lemma-one-equation (00KW), lemma-regular-domain (00NP), and lemma-regular-ring-CM (00NQ). These support exactly the algebraic tools used here. The retained ILO reading supplies the formal-model motivation, while the extracted coefficient and combinatorial refinements remain explicitly agent-written. I rechecked the zero monoid, n=1, field coefficients, arbitrary coefficient zero divisors in the first two nodes, and nonfree positive monoids. No statement dispute was found. The existing Sheaf formalMonoidRing_dimension theorem still ends in sorry and the project-source search found no finished WeilConjectures attachment.
