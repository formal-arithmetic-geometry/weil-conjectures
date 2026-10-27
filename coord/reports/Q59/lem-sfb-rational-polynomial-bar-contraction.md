# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-rational-polynomial-bar-contraction.json: item, same statement; four-step assembly.
- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-bar-coface-retraction-identities.json: statement, unsplit, no Mathlib match; five logged searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-bar-divided-monomial-normalization.json: statement, unsplit, no Mathlib match; five logged searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-ordered-composition-complex-homology.json: statement, unsplit, no Mathlib match; five logged searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-based-retract-universal-homotopy.json: statement, unsplit, no Mathlib match; five logged searches.

## Attachments

None. Searched lean/WeilConjectures for the item tag and polynomial-bar terminology: no matching declaration. Read lean/Sheaf/Paper/RationalPolynomialBarContraction.lean: differential_squared and contraction both contain sorry, so neither is an attachment. No Lean was edited or compiled.

## WANTED

WANTED: a symmetric-coalgebra cobar/Koszul reference for the rational polynomial additive-bar contraction with these ordered representatives, and an exact reference for the proper-product-interval calculation. The source's paragraph (3) contains only the open-direct-image preservation assertion; it does not supply this algebraic proof. The construction remains honestly agent-formulated. Stacks Tag 017P (simplicial.tex, definition-split, lines 1767 onward) was read for the actual splitting definition, not misused as a homotopy theorem. The existing splitting homotopy leaf is Mathlib SplitSimplicialObject.lean:307–312.

## Repair of the returned delivery

The sandbox initially contained only dispatcher markers, with no node or report to continue. The current read-only repository item carries exactly the eight returned steps (6922 characters) and the recorded Lean module. It supplies the repair baseline. All existing fields, including the statement, source, searches, Lean declaration and audit/review metadata, are preserved except the authorized proof, proof_deps, status and split_report. The delivery tool rebases onto the current server state.

The human return requests real parallel tasks, at least two, and an assembly of at most 3000 characters. There are four new unsplit tasks with empty proof/proof_deps and null proof_origin. They are comparable in argument size: old steps 1–2 (1511 characters), 3–4 (2022), 5 plus the dimension part of 6 (about 1500), and 7–8 (1727). The small last part of step 6 is the elementary dimension argument in parent step 3. No whole-item alias was introduced. The old proof is reproduced below verbatim; no argument is discarded or blurred. The normalization node owns the actual polynomial-to-simplicial splitting, the composition node owns the sign/shift identification and dual rank argument, and the last node owns the fixed-kernel construction and its finite-matrix extension.

## Searches and nonduplication

Before writing nodes, searched the whole DAG with rg for polynomial.bar, divided.monomial, zero.block, squarefree homology, ordered compositions, cochain retractions, acyclic contractibility, rational homotopies and column-finite matrices. Also parsed every node's statement to filter concept matches. Searched all imported blueprint nodes using tools/blueprint_refs.py search with polynomial bar, polynomial, divided, multidegree, ordered decomposition, cochain retract, acyclic, retraction, and contracting homotopy. The ancestor command returns None; this is the existing rootless created-node ancestry, retained exactly, with the item prepended to via on each new task. No blueprint node states a new task. No relevant project declaration was found.

Each task has LeanFinder, Loogle, LeanSearch and grep searches, with a second semantic phrasing; exact queries and responses' summaries/digests are in searches.jsonl and the node records. Read the hits: group cochains are arbitrary functions, not polynomial cochains; Dold–Kan provides the general normalization theorem but not the divided-monomial data; scalar compositions do not supply ordered vector-composition homology; null-homotopy results require K-projectivity/K-injectivity and do not state the specified based retraction construction or universal extension. None is a one-line specialization covering the task. No unavailable service was recorded as no match.

## Not duplicates

lem-sfb-polynomial-bar-divided-monomial-normalization vs lem-sfb-split-simplicial-nondegenerate-homotopy: the existing statement assumes a supplied simplicial splitting; the new statement constructs that splitting from divided monomials, identifies the projected merging differential, and dualizes it. The old leaf is an input to the future proof, not a replacement.

lem-sfb-polynomial-bar-divided-monomial-normalization vs lem-cbc-normalized-alternating-homotopy-equivalence: general Moore normalization does not construct this polynomial multidegree splitting or determine its nonzero-block differential.

lem-sfb-ordered-composition-complex-homology vs lem-sfb-product-chain-proper-interval-homology: the existing node computes augmented interval-chain homology; the new node identifies the different ordered-vector-composition complex with it, proves the shift/sign comparison, and computes the dual cohomology. It also handles m=0, outside the existing node's nonzero-m hypothesis.

lem-sfb-rational-based-retract-universal-homotopy vs lem-trf-field-complex-cohomology-splitting: the old node gives homotopy equivalence with cohomology and derived morphism calculations; it does not prescribe a homotopy for the supplied i,p, with the specified complement formula, grading and universally extended based matrix. It can supply part of a future proof.

lem-sfb-rational-based-retract-universal-homotopy vs lem-wf-bounded-free-complex-projective-cohomology-splitting: the old node assumes a bounded finite-free complex; the new statement has no boundedness or finite-basis hypothesis and includes fixed retract and universal based scalar-extension data.

lem-sfb-rational-based-retract-universal-homotopy vs lem-trf-vector-subspace-complement: existence of one vector-space complement is only an input; the new obligation is acyclic-kernel differential inversion, the fixed homotopy and universal extension.

lem-sfb-polynomial-bar-coface-retraction-identities vs lem-sfb-rational-polynomial-bar-contraction: the first task asserts only coface and representative identities, not cohomology or a contracting homotopy. Its detailed cancellation argument is a genuine part of the returned proof that the human specifically asks to spread.

## Review by Q59

I read the current item, its complete eight-step proof, the current blueprint direct-images proof paragraph (3), the main-20261015 unit section and the recorded chapter/unit routes. The source does not contain the algebraic calculation; the old agent proof and the owning Lean docstrings are therefore the immediate mathematical source of all four extracted tasks. Their source records name the precise returned steps, without attributing a new theorem to the blueprint. The item statement and every coefficient, degree and edge case remain unchanged.

For new task 1 I checked the two outer cofaces and alternating inner cofaces, the sorted monomial sign, and p^0=1. The task includes both the cochain identities and multidegree preservation, not a hidden assumption about them. Old step 2 proves pd=0 by cancellation of the two orders of distinct coordinates; repeated indices project to zero. For task 2 I read the statement of the splitting leaf: it requires the actual direct-sum decomposition indexed by surjections, not merely a simplicial module. That decomposition, finiteness of each divided basis, the projected differential and finite dualization are explicit new obligations. Stacks 017P defines only the splitting, and Mathlib's homotopyEquivNondegComplex supplies the general homotopy equivalence once supplied; the new node is not labeled mathlib.

For task 3 I read the full statement of lem-sfb-product-chain-proper-interval-homology: it assumes r>=1 and m nonzero, computes reduced augmented homology in degree s-2, and includes s=1. The new comparison uses it only when m!=0 (which forces r>=1). A tuple of n nonzero blocks has n-1 partial-sum vertices, hence chain degree n-2; merging the a-th pair has sign (-1)^a versus deletion sign (-1)^(a-1). Multiplication by (-1)^n makes the comparison an actual chain isomorphism. The new statement includes this chain/derived comparison, not just separate isomorphisms of groups. The finite-dual rank equality belongs to this task; it does not assume exactness of duals over general rings.

For task 4 I read lem-trf-vector-subspace-complement and both existing general splitting statements listed above. Complements exist over a field without finite-dimensionality. The new task assumes the cohomology isomorphism, not the desired homotopy, so its acyclic-kernel argument is noncircular. On C, d is bijective from L^n onto Z^(n+1); the inverse has the required degree -1. Z^0=0 follows from acyclicity and zero negative degrees. The homotopy is zero on i(K) and on L, giving dh+hd=1-ip, hi=ph=h^2=0. Based rational matrices have finite columns even for an infinite basis, so finite sums define their extension over every Q-algebra; no nonzero-ring or tensor-exactness hypothesis is smuggled in. The explicit constant-complex homotopy from old step 8 is retained in task 4.

Parent step 1 uses exactly task 1's displayed cochain identities and multigrading. Parent step 2 uses task 2's homotopy equivalence to the precisely stated V_m^*, then task 3's cohomology-dimension formula for that same merge boundary. Parent step 3 uses task 1's pi=1 and only the already established dimensions to show that the prescribed maps are inverse on cohomology: it is elementary linear algebra in dimensions zero and one. Parent step 4 checks every hypothesis of task 4: rational based spaces, direct-sum grading, zero differential on K, chain-map retraction and cohomology isomorphism. Its extension maps agree with the parent's formulas on each monomial, including degree zero. The citations.json quotes are literal portions of these four statements, one entry for each use in each parent step. No step borrows a construction from another node's proof.

I tested r=0, m=0, m=(1), m=(2), m=(1,1), q>r, negative degrees, and the zero coefficient algebra. For m=(1), V has one generator in degree 1 and the interval has only its empty-chain generator in degree -1. For m=(2), V_2→V_1 is multiplication by -1, so acyclic. For m=(1,1), V_2 has the two ordered decompositions and boundary [-e_1-e_2] from either; its kernel is the alternating one-dimensional line. On the polynomial side the sorted inclusion projects to +e_{1,2}. For r=0 the alternating constant differential and the stated even-degree h give identity in all positive degrees and zero on degree zero. No statement dispute was found.

B–E audit: all new statements introduce their objects and either define chain/homotopy notions inline or cite definition nodes that actually define them. All are TeX with single decoded backslashes; proof and proof_deps are empty. None introduces a hollow definition, a whole-item replacement, a new axiom, a new route or SGA. The parent has no step above 2000 characters and its total proof is below 3000. This repair corrects the single numbered return: all eight old arguments are now independently allocated, not merely shortened. No independent second review is claimed.

## Preserved returned arguments and task allocation

### Former step 1 — lem-sfb-polynomial-bar-coface-retraction-identities

Work first over $\mathbf Q$. The coface substitutions are the ones from addition with unit $0$: omitting an outer variable and replacing adjacent variables by their sum. Applying two substitutions in either possible order agrees by associativity of addition and by its unit law; equivalently, for cofaces $\delta^a$, $\delta^b\delta^a=\delta^a\delta^{b-1}$ when $a<b$. In the expansion of $d^2$, each such composite occurs twice with opposite signs, so $d^2=0$. In degree zero $d=0$ as stipulated. Polynomial substitution and comparison on variables are legitimate by [def-weil-pbc-mv-polynomial-ring].

### Former step 2 — lem-sfb-polynomial-bar-coface-retraction-identities

For $i(e_I)$, expand each substitution of $x_a+x_{a+1}$ by linearity of the single coordinate occurring in that block. The term choosing the right variable at position $a$ cancels the term choosing the left variable at position $a+1$; the two end terms cancel the first and last remaining terms. Hence $di=0$. To check $pd=0$, express $p^q(f)$ as the alternating wedge of the coefficient of degree one in each of the $q$ blocks, identifying the basis wedge with $e_I$. Outer cofaces omit a block and contribute zero. An inner coface can contribute only from degree two in its merged block and degree one in every other block. The two orders of two distinct coordinates have equal coefficients and opposite wedge signs; a repeated coordinate wedges to zero. Thus every contribution vanishes. Finally $pi(e_I)=e_I$, including the empty subset. These are coefficient calculations, so already hold over every $B$.

### Former step 3 — lem-sfb-polynomial-bar-divided-monomial-normalization

For a multi-index $m\in\mathbf N^r$, let $P_m^n$ be the span of monomials whose total exponent in coordinate $i$ across all blocks is $m_i$. All cofaces preserve $m$, and every polynomial is a finite sum of such homogeneous parts. In $P_m^n$ use the divided-monomial basis
$$b_{\alpha_1,\ldots,\alpha_n}=\prod_{a,i}x_{a,i}^{\alpha_{a,i}}/\alpha_{a,i}!,\qquad \sum_a\alpha_a=m.$$
This is a finite basis in each degree. The binomial formula says that the middle coface replaces $\alpha_a$ by all pairs $\beta+\gamma=\alpha_a$, each with coefficient $1$ in this basis; the two outer cofaces insert a zero block. The codegeneracies set one block equal to zero, killing its positive-degree monomials and deleting its zero block. The addition and zero identities give the cosimplicial identities. Therefore the finite rational duals $U_{m,n}=(P_m^n)^*$ form a simplicial module. Its degeneracies insert zero blocks. Every tuple has a unique ordered list of nonzero blocks, so insertion of its zero blocks gives exactly the direct-sum decomposition indexed by order-preserving surjections required by [lem-sfb-split-simplicial-nondegenerate-homotopy]. The nondegenerate summand $V_{m,n}$ is the span of dual tuples with every block nonzero (and the empty tuple for $m=0,n=0$).

### Former step 4 — lem-sfb-polynomial-bar-divided-monomial-normalization

Apply [lem-sfb-split-simplicial-nondegenerate-homotopy] to this splitting over $R=\mathbf Q$, and dualize the chain maps and homotopies. Every term is finite dimensional, so the double dual identifies with the original polynomial component. Thus $P_m$ is cochain homotopy equivalent to $V_m^*$. The projected differential in $V_m$ merges two adjacent nonzero blocks with sign $(-1)^a$ for $1\leq a\leq n-1$; the end faces of a nonzero-block tuple are zero, since the dual outer cofaces have zero blocks. Consequently $V_m^*$ is the polynomial subcomplex $N_m$ spanned by the divided monomials with no zero block: its differential splits one block into two nonzero blocks with sign $(-1)^a$. There are no terms in $N_m^n$ for $n>\sum_i m_i$ when $m\ne0$.

### Former step 5 — lem-sfb-ordered-composition-complex-homology

For $m\ne0$, send a nonzero-block tuple $(\alpha_1,\ldots,\alpha_n)$ to its cumulative partial sums
$$v_a=\alpha_1+\cdots+\alpha_a,\qquad1\leq a<n.$$
These are precisely the strict chains $0<v_1<\cdots<v_{n-1}<m$ in the coordinatewise interval; differences recover the tuple, so this is a bijection of bases, including $n=1$ and the empty chain. Merging blocks $a,a+1$ deletes $v_a$. The vertex-deletion sign is $(-1)^{a-1}$, whereas the merging sign is $(-1)^a$. Hence the differential on $V_{m,n}$ is the negative of the differential on $A(m)_{n-2}$ in [lem-sfb-product-chain-proper-interval-homology]. This minus sign does not change kernels or images. The lemma gives homology zero unless $m$ is squarefree, and in that case dimension one only for $n=\sum_i m_i$.

### Former step 6 — lem-sfb-ordered-composition-complex-homology

A finite rational matrix and its transpose have the same rank (row and column reduction both reduce it to an identity block and zeros). In degree $n$, the homology dimension of $V_m$ and the cohomology dimension of $V_m^*$ are therefore both $\dim V_{m,n}-\operatorname{rank}\partial_n-\operatorname{rank}\partial_{n+1}$. With the preceding homotopy equivalence, $H^n(P_m)$ has the dimensions just found. For $m=0$, the nondegenerate complex has only $\mathbf Q$ in degree zero, so the same equivalence gives $H^0(P_0)=\mathbf Q$ and zero in other degrees. Give $e_I$ multidegree $1_I$. Since $pi=1$ and $i,p$ are cochain maps, their induced maps on each multidegree have composite the identity; in each nonzero cohomology degree both sides have dimension one, and in every other degree both sides vanish. Hence $p:P_m\to K_m$ induces an isomorphism in every degree, with inverse induced by $i$.

### Former step 7 — lem-sfb-rational-based-retract-universal-homotopy

Put $C_m=\ker(p:P_m\to K_m)$. The equations $pi=1$, $di=0$, $pd=0$ give a direct-sum decomposition of complexes $P_m=i(K_m)\oplus C_m$. For a cycle $c\in C_m^n$, the cohomology isomorphism proved above gives $c=db$ in $P_m$; replacing $b$ by $b-ipb$ puts it in $C_m$ and leaves $db$ unchanged. Thus $C_m$ is acyclic. Let $Z_m^n=\ker(d:C_m^n\to C_m^{n+1})$. By [lem-trf-vector-subspace-complement], choose $L_m^n$ with $C_m^n=Z_m^n\oplus L_m^n$. The restriction $d:L_m^n\to Z_m^{n+1}$ is injective because $L_m^n\cap Z_m^n=0$, and surjective because $Z_m^{n+1}=dC_m^n=dL_m^n$. For $z+l\in Z_m^n\oplus L_m^n$ define $h(z+l)$ as the unique inverse image of $z$ in $L_m^{n-1}$. In degree zero $Z_m^0=0$ by acyclicity and $C_m^{-1}=0$, so this prescription gives $h^0=0$. It satisfies $dh(z+l)=z$ and $hd(z+l)=l$. Set $h=0$ on $i(K_m)$ and take the direct sum over $m$. Then $dh+hd=1-ip$ on $P_{\mathbf Q,r}$.

### Former step 8 — lem-sfb-rational-based-retract-universal-homotopy

Each basis monomial belongs to one $P_m^n$, and its image under $h$ is an element of the ordinary polynomial space $P_m^{n-1}$, hence a finite rational linear combination of monomials. Use the same coefficient matrices over every commutative $\mathbf Q$-algebra $B$: multiply the rational entries by the given coefficient in $B$. The differential, $i$, and $p$ have the same monomial formulas, so the rational identities remain equalities of finite coefficient sums over $B$. No exactness of scalar extension is needed. This also treats the zero algebra. If $r=0$, all terms are $B$, $d^n=0$ for even $n$ and $d^n=1$ for odd $n$. One may take $h^n=1$ for even $n\geq2$ and $h^n=0$ otherwise; then $dh+hd=1-ip$ in positive degrees and both sides vanish in degree zero. Thus the stated constant-complex edge case is included.

The final inference of former step 6 (pi=1 plus equal dimensions) remains explicit as parent step 3; the finite transpose-rank comparison is assigned to the composition/dual-cohomology task. The old cited inputs remain future-proof guidance, not proof_deps on unsplit nodes.

## Unfinished work

The four new tasks are intentionally statement-only for other workers. Their full inherited arguments are preserved above. No mathematical issue remains unresolved in the parent assembly.

Parent proof characters: 1916.

## Dry-run repair

The first preflight required an explicit definition-node citation on the general based-retract task. Added def-weil-pbc-module-chain-complex-homology to its statement and stmt_deps, explicitly through cochain reindexing; its kernel/image definition was read and agrees. This changes no mathematical hypothesis or claim. All original arguments and the parent statement remain intact.


## Repair of the 2026-10-22 landing refusal

The return in coord/returns/Q59.md identifies returned head fb41440c050 and asks for a rebase onto the current DAG, re-reading changed cited nodes and adjusting the split. This retry began with the retained five node files, report, citations and searches, rather than discarding the previous work. The first required dry run completed successfully at 29216582a97; deliver.py rebuilt it on current origin/sheaf-dag and preserved origin's maintainer-owned fields. The earlier side-completion refusal is recorded here for the maintainer; this worker does not promote side completion or change queue/review metadata.

I compared the retained returned item against the current read-only item. Its statement, stmt_deps, source, blueprint ancestry, mathlib_searches, Lean declarations, Lean review and audit all agree. The only differing fields were proof, proof_deps and split_report: the live item still has the eight-step 6922-character proof, while the retained delivery supplies the four-step assembly and four new tasks. None of those four task ids exists in the current live DAG, so they remain new obligations. The released stage-1 keep_plan repair note still explicitly requires this re-split. The chapter and unit records and direct-images paragraph (3) were re-read; no change to their route is needed.

For this retry I re-read the entire statement of each cited task, not just its previous review. Step 1 obtains precisely the coface identities, prescribed i,p and multidegree preservation from the coface task. Step 2 uses the normalization task's actual cochain homotopy equivalence and the ordered-composition task's dimensions for the same adjacent-merge boundary. I adjusted step 2 to show explicitly why the homotopy equivalence transports cohomology: on a cocycle the homotopy identity is a boundary dH(z). This is the only mathematical exposition change needed after rebasing. Step 3 then uses pi=1 and equal dimensions, and step 4 applies the fixed-retract task with the established cohomology isomorphism and monomial/subset bases. Its universal matrix extension agrees with the specified maps, including degree zero, zero coefficients and r=0. All six citations.json entries are still exact substrings of the statements.

I also re-read the current definition statements for polynomial rings, simplicial objects, and kernel/image homology; each supplies exactly the notion named by the four new tasks. As future proof guidance I re-read the current split-simplicial homotopy leaf, proper-product-interval homology statement and vector-subspace-complement leaf. The interval lemma applies only for m nonzero (thus r at least 1); its augmented degree s-2 becomes degree s after the two-degree shift, and the (-1)^n factor corrects the negative boundary. The split-simplicial leaf requires the supplied surjection decomposition, which the normalization task explicitly asserts. The complement leaf has no finite-dimensionality assumption. None of these current statements invalidates the retained split.

The existing search log was read in full and reused because no searched statement or search question changed. Current DAG and blueprint searches found no replacement for the four task statements; the already recorded nonduplication distinctions still apply. Each new task remains unsplit with empty proof/proof_deps, and no parent step exceeds 2000 characters. The exact parent statement and all inherited arguments remain preserved. This retry changes the assembly and its split_report as well as documenting the rebase; it is not an unchanged re-push.
