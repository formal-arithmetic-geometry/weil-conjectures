# Stage-1 repair: lem-sfb-bicosimplicial-shuffle-totalization

## Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bicosimplicial-shuffle-totalization.json`: unchanged statement, four-step assembly, 2,213 proof characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-free-bisimplex-projective-resolutions.json`: statement, unsplit; no Mathlib match. Takes the representable construction and pointwise resolution arguments of old steps 1–3.
- `dag/nodes/sec-six-functors-basics/lem-sfb-universal-shuffle-homotopy-inverse.json`: statement, unsplit; no Mathlib match. Takes the universal signed chain map and natural inverse arguments of old steps 4–5.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-representable-matrix-totalization.json`: statement, unsplit; no Mathlib match. Takes contravariant evaluation and the internal-differential homotopies of old steps 6–7.
- `citations.json`: verbatim statement quotations for all four step/node citations.

Three new nodes, zero Mathlib leaves. Sandbox-only scripts, the original-node snapshot and search output are working material, not project changes. No Lean files or compilation tools were used.

## Attachments

None. I searched the blueprint tag and bicosimplicial/shuffle/Eilenberg–Zilber/Alexander–Whitney terminology under `lean/WeilConjectures/`. The only potentially similar source hits were finite-projective internal-Hom evaluation, Koszul signs and Godement cup pairings; they do not state this comparison. The existing `lean/Sheaf/Algebra/Homology/BicosimplicialShuffleTotalization.lean` states the complete parent but its `exists_shuffle` proof ends in `sorry`. It is not an attachment. Its nine-step docstring agrees with the returned DAG proof.

## Wanted literature

WANTED: C. Weibel, *An Introduction to Homological Algebra*, §8.5, the Eilenberg–Zilber comparison and unnormalized shuffle, for the parent and universal-shuffle child. The retained NY report already requests it. No download was made. The blueprint paragraph (3) supplies the geometric application, not this algebraic proof; the parent remains explicitly agent-written. The new unsplit nodes do not pretend that the source proves more than it says.

## Issues and return repair

The sandbox initially contained only dispatcher briefs, no nodes, report or search log. I copied the current shared-repository parent, which has the returned nine-step proof, retained its statement, citations, source, Mathlib searches, blueprint data, Lean records and review metadata. The old report was recovered read-only from `coord/reports/NY/` and is preserved below as historical material. No branch command or repository write was used.

The sole return asks to spread an 8,202-character proof over at least two comparable statement-only tasks, without losing arguments. I created three tasks. Their statements have 2,347, 1,681 and 2,091 characters; their old argument allocations have 3,134, 1,622 and 2,049 characters. This distributes the actual work across construction/exactness, universal comparison, and matrix/totalization arguments. The parent's derived localization and strict degree-zero augmentation are short assembly. Each old proof paragraph is copied verbatim below with its destination: nothing has been silently compressed out of the work specification.

The projective-resolution child asserts the exactness, projectivity, generator identification and explicit pointwise contraction identities that its worker must establish; it does not contain proof steps. The universal-shuffle child asserts the fixed formula, chain map, augmentation and natural inverse/homotopies; it does not merely restate the parent for arbitrary coefficients. The matrix child is a general theorem for an arbitrary small indexing category and arbitrary complexes of finite lists of representables, not the bicosimplicial comparison itself. All are `unsplit`, with empty proof/proof_deps, null proof_origin, sources, inline meanings and definition dependencies.

The inherited ancestor command returns None. I retained this honest origin, prepended the parent to each child's via chain and specified the current blueprint's paragraph (3) application and particular argument. The historical unit JSON belongs to the older six-functors chapter, whereas the current item belongs to six-functors-basics; I followed the current source and changed no chapter/unit record. No statement dispute or mathematical source error was found. The existing accepted tool_uses field on the parent was preserved; the new parent proof no longer directly invokes the generic uniqueness tool. The old generic comparison arguments belong to the universal-shuffle task and are retained in its work brief below.

## Mathlib searches

For each new node I ran two distinct LeanFinder formulations, LeanSearch, Loogle and two source grep queries using the required msearch.py. The universal-shuffle node also records a third, targeted grep in CategoryTheory/Abelian/Projective that returned lift and liftHomotopy declarations. Every exact query and returned digest is in searches.jsonl and in the corresponding node. LeanSearch for free-bisimplex resolutions was rate-limited and is recorded as unavailable. All other searches returned actual results or no hits. Raw hit statements are preserved in search-output.jsonl and were read.

I opened Generator/Presheaf.lean (freeYoneda and freeYonedaHomEquiv), Abelian/Projective/Resolution.lean (lift, liftHomotopy and homotopyEquiv), Algebra/Homology/Homotopy.lean (mapHomotopy and mapHomotopyEquiv), BifunctorHomotopy.lean, ExtraDegeneracy.lean and DoldKan/HomotopyEquivalence.lean. The product-simplex hits identify weakly increasing coordinate strings; they do not assert our augmented free projective resolutions. ProjectiveResolution.homotopyEquiv selects its own lift; it does not assert the specific signed shuffle is a chain map or that this prescribed map has a homotopy inverse. mapHomotopyEquiv assumes an additive functor, whereas the matrix child must construct the contravariant evaluation and its signed total extension. These are useful ingredients for future workers, not one-line matches for any entire new statement.

## Not duplicates

lem-sfb-free-bisimplex-projective-resolutions vs lem-sfb-simplex-lattice-shuffle-boundary: the existing node defines strings and proves the shuffle boundary identity, but has no functor-category projectivity, enough projectives, exact augmented resolutions or cone contractions.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-sfb-simplex-lattice-shuffle-boundary: the existing identity provides the universal chain-map calculation, but neither a natural homotopy inverse in the diagram category nor the two homotopies. It will be reused by the new node's worker.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-weil-pbc-injective-resolution-lift-exists: the existing node gives a lift for injective resolutions, not this explicit free-simplex shuffle chain map and its homotopies. It is the reusable opposite-category existence input, not the entire new statement.

lem-sfb-universal-shuffle-homotopy-inverse vs new-t4-augmented-resolution-lift-homotopy: the existing node is uniqueness of arbitrary augmented lifts up to homotopy; it does not construct or verify this shuffle or its inverse. It remains the generic comparison tool in the allocated proof.

lem-sfb-free-bisimplex-projective-resolutions vs lem-sfb-bicosimplicial-shuffle-totalization: the parent compares totals in an arbitrary abelian coefficient category; this child only constructs auxiliary projective resolutions in Fun(Delta x Delta,Ab), with no shuffle or arbitrary-coefficient evaluation.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-sfb-bicosimplicial-shuffle-totalization: this child concerns a fixed universal chain map of free diagram resolutions, with no internal complex or arbitrary-coefficient totalization or strict augmentation from M.

lem-sfb-finite-representable-matrix-totalization vs lem-sfb-bicosimplicial-shuffle-totalization: the child assumes given chain maps/homotopies on finite representables and proves their evaluation/totalization rule for any small I; it asserts no shuffle chain map or existence of universal homotopies.

lem-sfb-finite-representable-matrix-totalization vs lem-pod-point-dualizing-complex: that keyword hit identifies an exceptional dualizing object and derived dual at a coefficient point; it gives no free-representable matrix evaluation.

Whole-DAG statement searches found no representable-projectivity or simplex-contraction statement duplicating these nodes. Broad free-representable hits concern sheaf/cohomology class realization, not free simplex diagram resolutions. Whole-blueprint searches for bicosimplicial, shuffle, projective resolution, homotopy, matrix and simplex found no equivalent node. I also searched the three proposed ids in the DAG and project Lean source before creating them.

lem-sfb-universal-shuffle-homotopy-inverse vs def-sf-open-reduction-coefficient-mate: the existing node concerns Finite coefficient reduction and the open scalar mate; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-coef-tower-natural-currying: the existing node concerns Natural tower currying isomorphism; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-coef-locally-cofibrant-dg-restriction: the existing node concerns Restriction along a locally cofibrant dg quasi-equivalence; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-coef-brown-left-fractions: the existing node concerns Left fractions and localized retractions in a Brown cofibration category; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-coef-enriched-fixed-set-model: the existing node concerns Restriction along object functions of fixed-object dg categories is right Quillen; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-trf-finite-map-dualizing-transfer: the existing node concerns Transfer of a dualizing complex along a finite ring map; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-trf-relative-dualizing-pair-rigidity: the existing node concerns Rigidity of already given coherent relative dualizing pairs; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-pc-split-top-differential-cancellation: the existing node concerns Cancellation of one split top differential; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-sc-smooth-proper-curve-dualizing-exterior-one: the existing node concerns First exterior sheaf is the original sheaf; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-pc-split-top-differential-cancellation-homotopy: the existing node concerns Canonical split top cancellation homotopy; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-pc-perfect-descend-morphisms: the existing node concerns Descent of morphisms between perfect complexes; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-pc-split-top-differential-cancellation-properties: the existing node concerns Flat quasi-coherent finite-presentation sheaves are closed under retracts; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs def-sp-double-complex-total: the existing node concerns First-quadrant double complexes, total complex and the two filtrations; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-weil-pbc-henselian-finite-type-product-decomposition: the existing node concerns Over a henselian local ring a finite type algebra splits off its finite local factors (Stacks 04GJ); its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

lem-sfb-universal-shuffle-homotopy-inverse vs lem-pur-compact-support-integral-coefficient-comparison: the existing node concerns Integral compact support under finite free coefficient extension; its statement does not assert the specified signed shuffle between the free diagonal and separate simplex resolutions, with its natural inverse and both homotopies.

## Review by Q23

I read the current direct-images proof paragraph (3), the item's chapter and unit records, the current parent and its Lean docstring, and the entire B–E delivery-errors checklist. For the free-bisimplex node I read Stacks Tag 08Q3, `simplicial.tex`, label `example-simplex-contractible`: the source uses the last vertex for its simplicial homotopy and mentions the first-vertex direction. The new statement explicitly asserts the first-vertex chain contraction and tensor identity, rather than attributing them wholesale to that tag. I verified the pointwise, not natural, status of these contractions. Pointwise kernels and cokernels give exactness in the functor category, and the generator formula gives projectivity there; no arbitrary target category is assumed to have infinite sums. The indexing category is small, so the auxiliary coproduct over (i,x) is legitimate. I checked the degree-zero augmentation separately from the positive-degree contraction and verified that E is zero in positive degree.

For the universal-shuffle node I read Stacks Tags 0649 and 064A at `lemma-morphisms-lift-projective` and `lemma-morphisms-equal-up-to-homotopy-projective`, and opened `lem-weil-pbc-injective-resolution-lift-exists` and `new-t4-augmented-resolution-lift-homotopy`. The free model is nonnegative chain-graded, hence bounded above on conversion to cochains. The opposite-category application in the retained argument takes Q-op before P-op, giving tau:P->Q. The auxiliary category has enough projectives, so its opposite satisfies the enough-injectives convention. Both composites have the same augmentation as the identities, and d_1 followed by augmentation vanishes. I read `lem-sfb-simplex-lattice-shuffle-boundary`: its statement explicitly includes the boundary sign, preservation of the vertex augmentation, and naturality for all monotone postcompositions. These are exactly the inputs that assemble sigma; none is inferred merely from its definition. Alpha_mu has target [a] and alpha_nu target [b], so the specified generator is in R_(n,n)(a,b), and evaluation reverses sigma:Q->P into S:D->T.

For the matrix-totalization node the source is openly agent-formulated below the current blueprint paragraph (3). I checked Nat(R_i,R_j)=Z[Hom(j,i)] and matrix transposition, including identities and composition: evaluation sends a composite to the reverse product of evaluated matrices by functoriality and bilinearity. Nonnegative P and internal r give finitely many summands for each m=n+r; the empty finite list gives zero. All matrix entries are finite integral combinations, so all constructions exist in any abelian C. A chain homotopy raises n before contravariant evaluation and lowers n afterwards. Its internal cross terms have opposite signs (-1)^(n-1) and (-1)^n; no choice of a different inverse or homotopy for each r is permitted. The theorem quantifies one universal map/homotopy and evaluates it in all internal degrees, ensuring commutation with d_r and naturality in X. Its derived statement is an isomorphism of derived objects, not just per-degree cohomology claims.

Parent step 1 uses the exact resolution conclusion of the free-bisimplex node and the explicitly prescribed sigma, tau, h_P,h_Q conclusion of the universal-shuffle node. All these are statements, not constructions hidden in their proofs. Step 2 uses the matrix node's contravariant evaluation, preservation of maps/homotopies and total signs; substituting the two explicit finite lists from step 1 gives precisely D and T. The signed generator determines the desired S, so the application does not replace S by an unspecified equivalent map. The hypothesis C abelian and internal degrees nonnegative are the original hypotheses. Step 3 uses the equivalently-from-K(A) localization clause of `def-weil-abstract-derived-category`, which I opened; inverse homotopy classes stay inverse under a functor. Step 4 is the written degree-zero coface calculation, using commutation of the directions and the two hypotheses on i, followed by the unique empty shuffle. It establishes the strict equality, not merely a homotopic square. The parent proof has no step longer than 2,000 characters and totals 2,213 characters.

I generated citations.json only after reading these exact statements and checked every quote as a literal substring of the cited statement. New statement dependencies point only to definitions or the previously existing string lemma and the smaller free-resolution task; no child depends on the parent. The parent statement is byte-identical to the repository version. No hypothesis on the characteristic, normalization, nonconstant directions, enough injectives/projectives of C, or infinite sums of C has been added. The zero diagram, all constant cases, p=0 or q=0, degree n=0 and the empty-list matrix case are included. I ran the sandbox-only integer checker: 802 pair-string cone and 988 tensor-cone identities passed for p,q<=2 and total string degree<=3, retaining repetitions. The n=0 shuffle is the identity; for a=b=1 the two paths have opposite signs, matching the boundary node. These checks support the sign and small-case audit; the new lemmas remain unproved stage-1 tasks.

The return was repaired by creating three independent proof obligations with concrete interfaces, preserving all old arguments below, and reducing only the assembly. None of these new tasks moves the whole parent into a single node, restates one of its arbitrary-coefficient clauses, or promotes a two-line elementary consequence. Every new node has its own logged three-kind search, complete statement, source and blueprint data, and deliberately no proof steps. Nothing is silently dropped or declared proved.

## Unfinished work

The three new nodes are intentionally statement-only work for later workers, not completed proofs or Mathlib leaves. The existing simplex shuffle boundary node remains an independent obligation. No part of this one-level repair is left unspecified.

## Preserved argument allocation

The following paragraphs are copied verbatim from the returned head, not replaced by summaries. They are work briefs for later splitting/proving, not proof steps stored in the unsplit nodes. Old steps 8–9 remain parent assembly; the new step 4 uses the same explicit calculation with the commuting g_0 moved to its well-typed side.

### Old step 1 → lem-sfb-free-bisimplex-projective-resolutions

Put $I=\Delta\times\Delta$, working with small abelian groups in a universe containing this countable category. In $\mathcal E=\operatorname{Fun}(I,\mathrm{Ab})$ define $R_i(j)=\mathbf Z[\operatorname{Hom}_I(i,j)]$, with postcomposition on generators. This category is abelian: kernels are pointwise kernel subgroups, cokernels are pointwise quotient groups, their structure maps are induced by the naturality squares, and image equals coimage pointwise. Thus these constructions satisfy exactly [def-sp-abelian]. A natural transformation $R_i\to F$ is uniquely specified by $x\in F(i)$: its value on a generator $\alpha:i\to j$ must be $F(\alpha)x$. Hence maps from $R_i$ lift through every pointwise surjection, by lifting $x$. Finite sums of the $R_i$ are projective by lifting each component. Also $\bigoplus_{(i,x),\ x\in F(i)}R_i\to F$, sending the distinguished generator to $x$, is pointwise surjective and its source projective (choose lifts for all its generators). Thus $\mathcal E$ has enough projectives. Monomorphisms, epimorphisms and exactness in $\mathcal E$ are detected pointwise by the displayed kernel and cokernel constructions.

Uses: def-sp-abelian.

### Old step 2 → lem-sfb-free-bisimplex-projective-resolutions

Define nonnegative chain complexes in $\mathcal E$ by $P_n=R_{(n,n)}$ and $Q_n=\bigoplus_{a+b=n}R_{(a,b)}$. On $P$, the boundary precomposes a pair of monotone maps by each diagonal coface, with alternating signs. On the $(a,b)$ summand of $Q$, take alternating precomposition in the first variable and $(-1)^a$ times alternating precomposition in the second; omit a direction in degree zero. Two deletions in one variable cancel in opposite orders, and the two cross terms have coefficients $(-1)^{a-1}$ and $(-1)^a$, so both boundaries square to zero. Both augment to the constant functor $\mathbf Z$ by sending each vertex generator to $1$. At $(p,q)$ these are exactly $P(p,q)=V(p,q)$ and $Q(p,q)=\operatorname{Tot}(U(p)\otimes U(q))$, with the strings, boundaries and augmentations of [lem-sfb-simplex-lattice-shuffle-boundary].

Uses: lem-sfb-simplex-lattice-shuffle-boundary.

### Old step 3 → lem-sfb-free-bisimplex-projective-resolutions

For $P(p,q)$, prepend the minimum vertex $(0,0)$ to every string, obtaining $h_n:P_n(p,q)\to P_{n+1}(p,q)$. Let $e:\mathbf Z\to P_0(p,q)$ send $1$ to that vertex. Deleting the prepended entry gives the original string; deleting any other entry cancels the corresponding term of $h\partial$. Consequently $\partial h+h\partial=1$ in positive degrees and $\partial h=1-e\epsilon$ in degree zero. Thus the augmentation is surjective and the augmented complex is exact. Identical formulas, prepending $0$, give contractions $h_p,h_q$ and projections $E_p=e_p\epsilon_p,E_q=e_q\epsilon_q$ of $U(p),U(q)$, with $E$ zero in positive degree. On $Q(p,q)$ put $H(u\otimes v)=h_pu\otimes v+(-1)^a E_pu\otimes h_qv$ for $u$ of degree $a$. Expanding the tensor boundary cancels the cross terms and gives $\partial H+H\partial=(1-E_p)\otimes1+E_p\otimes(1-E_q)=1-E_p\otimes E_q$. Its degree-zero augmentation is surjective. Both augmented complexes are therefore pointwise exact. Together with Step 1, $P,Q$ are projective resolutions of the constant functor; these contractions need not be natural in $(p,q)$, since they are used only to prove pointwise exactness.

Uses: .

### Old step 4 → lem-sfb-universal-shuffle-homotopy-inverse

The maps $\sigma_{p,q}:Q(p,q)\to P(p,q)$ of [lem-sfb-simplex-lattice-shuffle-boundary] commute with boundary, preserve the augmentation and commute with postcomposition. They therefore assemble to an augmented chain map $\sigma:Q\to P$ in $\mathcal E$. On the distinguished generator of $R_{(a,b)}$, its value is the signed sum of pairs $(\alpha_\mu,\alpha_\nu):(n,n)\to(a,b)$. This also fixes exactly which coordinate receives each list of shuffle positions; no interchange of $a,b$ or additional sign is introduced.

Uses: lem-sfb-simplex-lattice-shuffle-boundary.

### Old step 5 → lem-sfb-universal-shuffle-homotopy-inverse

Use [lem-weil-pbc-injective-resolution-lift-exists] in $\mathcal E^{\mathrm{op}}$ on the identity of the constant object, with the two opposite resolutions in the order $Q^{\mathrm{op}},P^{\mathrm{op}}$. The hypotheses hold: reversing the pointwise kernels/cokernels in Step 1 gives an abelian opposite category; a projective object becomes injective because its lifting through epis is precisely extension across the opposite monos. Enough projectives gives enough injectives in the opposite, and the exact augmented nonnegative chain resolutions become injective nonnegative cochain resolutions. Reversing the resulting map gives $\tau:P\to Q$ with $\epsilon_Q\tau_0=\epsilon_P$. Both $\sigma\tau:P\to P$ and $\tau\sigma:Q\to Q$ have the same augmentation as the respective identities. Apply [new-t4-augmented-resolution-lift-homotopy] to each pair: its source is a projective resolution, its target has all the exactness properties verified in Step 3, and its augmentation vanishes on $d_1$. We obtain $\sigma\tau-1=\partial h_P+h_P\partial$ and $\tau\sigma-1=\partial h_Q+h_Q\partial$ in $\mathcal E$.

Uses: lem-weil-pbc-injective-resolution-lift-exists, new-t4-augmented-resolution-lift-homotopy.

### Old step 6 → lem-sfb-finite-representable-matrix-totalization

Here is the explicit evaluation of these universal identities in an arbitrary abelian $\mathcal C$. A map $R_i\to R_j$ is determined by a finite integral sum of generators $\alpha:j\to i$, by the generator formula in Step 1. For a covariant diagram $Y:I\to\mathcal C$, send that map contravariantly to $\sum c_\alpha Y(\alpha):Y(j)\to Y(i)$. For finite sums of representables take the transposed matrix on the corresponding finite biproducts. Identities, sums and compositions are preserved contravariantly because composition expands as $\sum_{\alpha,\beta}c_\alpha d_\beta Y(\alpha\beta)$, equal to the product of the two matrices by functoriality and bilinearity. Thus every chain-map or homotopy equation between $P,Q$ evaluates to the corresponding cochain equation. Evaluating $P$ gives the diagonal alternating-coface complex of $Y$, and evaluating $Q$ gives the double alternating-coface total. The evaluation of $\sigma$ is precisely $S$, since its generator values were computed in Step 4. The evaluation of $\tau$ is its inverse up to the evaluated cochain homotopies.

Uses: def-sp-abelian.

### Old step 7 → lem-sfb-finite-representable-matrix-totalization

Apply Step 6 with $Y^{a,b}=X^{a,b,r}$ for each internal degree $r$, using the same fixed universal matrices $\sigma,\tau,h_P,h_Q$ for all $r$. Every entry is a sum of structure maps of $X$, so it commutes with $d_r$, and is natural in $X$. The evaluated degree-zero maps preserve total cosimplicial degree $n$: hence $(-1)^n d_r S=S(-1)^n d_r$, and the same for the inverse. They therefore give cochain maps between the complexes $D(X),T(X)$ of the statement. For an evaluated homotopy $H$, which lowers total cosimplicial degree from $n$ to $n-1$, the extra terms in the total homotopy equation are $(-1)^{n-1}d_rH+(-1)^nHd_r=0$. The remaining terms are exactly the cochain homotopy equations of Step 6. Thus $S$ is a chain homotopy equivalence of the full total complexes, including their internal differentials. All matrices and all total-degree sums are finite by nonnegativity, as required by [def-sp-double-complex-total]; no countable sum in $\mathcal C$ is used.

Uses: def-sp-double-complex-total.

### Old step 8 → parent assembly

Passing to the homotopy category, the two homotopy equations say that the classes of $S$ and its evaluated inverse compose to the identity. Their images under the localization defining $D(\mathcal C)$ in [def-weil-abstract-derived-category] still satisfy these two equations, hence give an isomorphism of derived objects. The original maps commute with every map of bicosimplicial complexes by the finite matrix formulas, so this derived isomorphism is natural.

Uses: def-weil-abstract-derived-category.

### Old step 9 → parent assembly

For the augmentation clause, write $f_0,f_1$ and $g_0,g_1$ for the two degree-zero cofaces. The hypotheses are $(f_0-f_1)i=0$ and $(g_0-g_1)i=0$. The diagonal alternating coface applied to $i$ is $f_0g_0i-f_1g_1i=(f_0-f_1)g_0i+f_1(g_0-g_1)i=0$, using commutation of the two directions to move $g_0$ past $f_0-f_1$. The two separate coface sums in $T$ also kill $i$. Since $i$ commutes with internal differentials, the inclusions in cosimplicial degree zero are chain maps $j_D,j_T$. In degree $n=0$ there is just the empty shuffle, its sign is $1$, and both surjections are the identity of $[0]$. Therefore $S_{0,0}=1$ and $Sj_D=j_T$ as chain maps, strictly. Vanishing objects give zero matrices. The contractions in Step 3 and the shuffle identity retain repeated vertices, including $p=0$ or $q=0$; the proof never assumes either cosimplicial direction is nonconstant. Thus constant objects and either constant direction are included.

Uses: .

## Historical NY report retained verbatim

This appendix describes the earlier delivery, not the present three-node repair.

# Stage-1 report: lem-sfb-bicosimplicial-shuffle-totalization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bicosimplicial-shuffle-totalization.json`: statement; split with nine proof steps; no exact project Lean attachment and no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-simplex-lattice-shuffle-boundary.json`: new statement-only unsplit node; Mathlib searches returned no signed lattice-path boundary theorem. It has no proof or proof dependencies.
- `citations.json`: one verbatim statement excerpt for every step/node citation.

There is one new node and zero new Mathlib leaves. `check_small_cases.py` and `write_split.py` are sandbox-only working scripts, not project files.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, bicosimplicial objects, shuffles, Eilenberg–Zilber and Alexander–Whitney found no declaration stating this item. The finite-projective internal-Hom shuffle and Koszul sign references concern different operations. The module cup-product Alexander–Whitney files concern pairings, rather than this diagonal homotopy equivalence.

## Wanted literature

WANTED: C. Weibel, *An Introduction to Homological Algebra*, section 8.5, the Eilenberg–Zilber shuffle boundary calculation, for `lem-sfb-simplex-lattice-shuffle-boundary` and the parent. `literature/LIST.md` records the book as unavailable. I did not download or edit literature. The parent's proof is explicitly marked agent-written: the current blueprint states its geometric application but does not contain this universal free-simplex proof.

## Issues found

The assigned statement is correct as written, including the unnormalized complexes and the specified surjections. No statement was changed. In particular, the shuffle sign is the sign of the concatenated lists of increment positions, with the first list having length a; changing the coordinate assignment would change the formula.

The inherited `blueprint.from.node` is null. `python3 tools/blueprint_refs.py ancestor lem-sfb-bicosimplicial-shuffle-totalization` actually returns None. I preserved that inherited result, filled the child's precise application place and via chain, and recorded the current main-20261015 proof paragraph (3) rather than inventing an ancestor. Whole-blueprint searches for shuffle, simplex and projective-resolution lifts found no equivalent blueprint node. The historical unit JSON points to the older six-functors chapter, whereas this assigned item and its source live in six-functors-basics; I read both and followed the current source's formal open-direct-image comparison without altering the unit or chapter.

## Not duplicates

lem-sfb-simplex-lattice-shuffle-boundary vs lem-sfb-bicosimplicial-shuffle-totalization: the child is only a boundary identity for finite integral sums of weakly increasing pairs of vertex strings. It asserts neither homotopy equivalence nor arbitrary abelian coefficients, internal complexes, totalization or augmentation maps from a complex. The parent's resolution, evaluation, total-differential and strict augmentation arguments are proved in its own steps.

lem-sfb-simplex-lattice-shuffle-boundary vs lem-cbc-normalized-simplex-chain-diagonal: the existing node gives the Alexander–Whitney coalgebra diagonal on normalized free chains, discarding repetitions. The new node concerns the opposite-direction shuffle on unnormalized chains of two independent simplices and retains repetitions. Neither statement specializes to the other.

lem-sfb-simplex-lattice-shuffle-boundary vs lem-coef-bisimplicial-diagonal-equivalence: that node is a weak-equivalence statement about homotopically constant bisimplicial spaces. It supplies no signed integral shuffle boundary identity.

DAG searches also inspected the lattice-path hits for pattern-generator product cells, Cartesian twisted resolutions and nonfree-chain completions: their statements concern marked anodyne attachments, final functors or strict-chain completion counts, not an alternating-deletion identity. No existing node with the child's statement was found. No Stacks tag is assigned to the child: the local Stacks Eilenberg–Zilber statement in sites-cohomology.tex is a derived tensor comparison of simplicial modules, not this explicit shuffle formula or a homotopy inverse for arbitrary abelian coefficients, so I did not misattribute it.

## Mathlib search assessment

Every search in the new node was actually run with the prescribed msearch.py and recorded in searches.jsonl. Both semantic services were available; Loogle and source grep ran too. I tried two semantic formulations of the lattice-path identity. I read the product-simplex coordinate and face statements in AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean, the normalization homotopy equivalence in DoldKan/HomotopyEquivalence.lean, and ExtraDegeneracy.lean's stated hypothesis and conclusion. Product-simplex coordinate equivalences only identify coordinates and deletion; they do not assert the signed sum. Dold–Kan compares one simplicial object's normalized and unnormalized complexes, and extra degeneracy needs a specified contraction of a single augmented simplicial object. The alternating multilinear-map shuffle hits are not chain maps on pairs of simplices. None is an exact or one-line generalized match.

For the item I repeated semantic searches, Loogle and Homology grep with the full bicosimplicial/internal-complex question, retained the inherited search records, and read the returned normalization, extra-degeneracy and totalization candidates. ProjectiveResolution.homotopyEquiv and liftHomotopy really do give general comparison tools: I read Resolution.lean, but no new node was needed for them because the existing injective-resolution lift (dually) and augmented-resolution uniqueness nodes already supply the needed interfaces. The exploratory projective-resolution searches remain in searches.jsonl; they are not recorded as negative searches for the shuffle identity.

## Review by NY

I read the assigned node, its chapter and unit records, the current main-20261015 direct-images proof paragraph (3), the whole B–E checklist of delivery-errors.md (both copies), and the existing nodes cited below. I checked the simplex contraction against Stacks Tag 08Q3 (simplicial.tex, example-simplex-contractible), including its distinction between a first-vertex and last-vertex homotopy. The proof uses an explicitly written first-vertex chain contraction, so it does not assume a reversal of the source's simplicial homotopy. For resolution comparison I read derived.tex Tags 013P/0649 (morphisms-lift and morphisms-lift-projective) and 064A (morphisms-equal-up-to-homotopy-projective), the exact statements of the two cited existing nodes, and the Mathlib injective desc/desc_commutes definitions. The shuffle boundary child is sourced as agent-formulated with the missing Weibel reference honestly requested; the local blueprint and Stacks are not claimed to prove its formula.

Step 1 uses exactly the abelian-category definition. The pointwise kernel/quotient construction verifies it directly; the displayed generator formula proves the special additive Yoneda fact instead of citing the scheme-only Yoneda node. Lifting each generator proves projectivity, and the explicitly indexed coproduct surjects onto every diagram. I checked that I is small, so these auxiliary groups and coproducts exist in a fixed universe. This does not assume any infinite coproducts in the arbitrary target category C.

Step 2 uses the child's explicitly defined unnormalized string complexes and boundaries. The representations R_(n,n) and sum R_(a,b) evaluate to exactly its V and U tensor complexes, not to normalized chains. I checked both cross-term signs and the fact that boundary out of degree zero is zero. Step 3 proves the exactness rather than citing a generic acyclic-model assertion. Prepending the minimum vertex gives d h+h d=1-e epsilon in degree zero and 1 in positive degrees; on a tensor, H=h tensor 1+E tensor h gives 1-E tensor E. I checked that E kills positive degrees, the tensor signs cancel, and the degree-zero augmentations are surjective. Naturality of the contractions is neither true nor needed: only exactness is detected pointwise. Thus the hypotheses of projective resolution comparison hold in the functor category.

Step 4 cites the new child's boundary, augmentation and postcomposition claims, all present in its statement. It uses no homotopy-equivalence conclusion from the child. Evaluating the universal generator gives precisely (alpha_mu,alpha_nu), with the intended lengths, so the item will receive its own specified shuffle, not an unspecified comparison map.

Step 5 cites `lem-weil-pbc-injective-resolution-lift-exists` for the existence of a map of resolutions and `new-t4-augmented-resolution-lift-homotopy` for uniqueness up to homotopy. I opened both nodes. The former is stated for every abelian category and actual injective resolutions. Opposite projective resolutions meet this hypothesis because the abelian axioms dualize, epis become monos and enough projectives in Step 1 gives enough injectives in the opposite. Applying it in the order Q-op, P-op gives tau:P -> Q, not the reversed map. The latter node allows any exact nonnegative target, and here both targets are exact projective resolutions. Its required augmentation equalities follow from epsilon_P sigma=epsilon_Q and epsilon_Q tau=epsilon_P; d_1 followed by augmentation is zero. I declared its off-unit citation as a generic homotopy-uniqueness tool. This does not replace the unit's direct-image route.

Step 6 is a written finite-matrix argument: Nat(R_i,R_j) is the free group on arrows j -> i, so evaluating through the covariant X reverses the universal chain map. I checked this variance, matrix composition, and the reversal of degree +1 chain homotopies to degree -1 cochain homotopies. All matrices are finite sums of representables, and the argument uses only the finite biproduct and bilinear composition clauses of def-sp-abelian.

Step 7 uses def-sp-double-complex-total for finite first-quadrant total sums. The universal matrices commute with d_r since all their entries are X's structure maps. Degree-zero maps preserve the total cosimplicial index n=a+b, whereas a homotopy lowers it by one. I checked the actual internal cross terms (-1)^(n-1)d_r H+(-1)^n H d_r=0. Consequently the homotopies survive totalization, rather than merely proving that each row is a quasi-isomorphism. Step 8 uses precisely the localization from the homotopy category stated in def-weil-abstract-derived-category: an already invertible homotopy-category class stays invertible. It proves an isomorphism of derived objects and its naturality, rather than just cohomology isomorphisms.

Step 9 has no hidden lemma: the two degree-zero coface differences annihilate i, their commutation kills the diagonal coface difference, and the only degree-zero shuffle is the empty partition with sign 1. Thus the asserted square commutes strictly as chain maps. Zero objects, constant diagrams and one constant direction require no reduced/normalized or nondegeneracy assumption. I tested the child's formula exhaustively on 1,969 basis pairs with p,q <= 2 and a+b <= 4, including repeated vertices, p=q=0, and each zero-dimensional factor, using the sandbox-only check_small_cases.py; every signed boundary identity passed. I also checked the zero-degree vertex/augmentation equation and the zero complex directly.

For B1–B9 I checked self-contained objects, definitions or explicit inline meanings, honest sources, unsplit-child emptiness, actual search logs and blueprint origins. For C1/C4 I compared each step's uses with the exact cited statements and generated all verbatim quotes in citations.json. For C6 there is no upward edge: the child has only the module-chain-complex statement dependency, and the existing generic lift/homotopy nodes do not depend on the item. For D1/D2 the substantive resolution construction and totalization proof remain in the item. For D4 the resolutions are verified before comparison is applied. For E1–E5 I checked the hypotheses and the coordinate, variance and total-sign calculations above. Every step is under 2,000 characters, so no long step hides an additional comparison lemma. No statement dispute or source error was found.

## Unfinished work

No part of this one-level split is omitted. The child is intentionally statement-only and joins the stage-1 queue; it is not claimed proved or in Mathlib. Formal Lean writing and all compilation remain outside this task.

## Dry-run repair

The first dry run found one schema issue: the completely explicit combinatorial child had no definition-node citation. I opened def-weil-pbc-module-chain-complex-homology, verified that it defines precisely the integer-indexed module chain complexes and chain maps used here (including extension by zero), and added it as the child's statement dependency with R=Z. I refreshed the parent's verbatim child quotations. The child still has no proof or proof dependencies; the mathematical statement and its searches are unchanged.

## Validation of this repair

The first required deliver.py --no-push completed successfully: preflight passed at 4407bb8aa20. I then added the already-run targeted projective-comparison grep to the universal-shuffle node record and corrected the citation count in this report. The final dry run checks these final files before the authorized push. No mathematical statement or proof changed after that successful check.


## Current-DAG landing repair by Q23 — 2026-10-22

This continuation repairs the landing refusal for returned head `dec77863b03`, not a mathematical rejection of the split. I checked that the interrupted initial dry run had finished: no delivery process remained, and `.stage1-ready.json` recorded successful completion at `4df4fba16ff`. I did not repeat an active command or infer that a provider failure invalidated the work.

I compared `original-node.json`, the retained original parent from which the returned delivery was made, with the current read-only DAG parent, field by field: they are identical, including all nine old proof steps (8,202 characters), statement, statement dependencies, source, blueprint and maintainer records. The three child ids are absent from the current DAG. The sandbox differs from that current parent only in `proof`, `proof_deps` and `split_report`. The delivery wrapper rebases those owned fields on the fetched current `origin/sheaf-dag`, retaining its maintainer-owned fields. The released stage-1 repair note explicitly reopens this reviewed parent and requires at least two new tasks and an assembly of at most 3,000 characters; the retained three tasks and 2,213-character assembly meet that instruction. I preserved every old argument and all recorded search results and citations.

I reread every current supporting statement, rather than relying on its prior review: `def-sp-abelian` supplies finite biproducts and additive composition; `def-sp-double-complex-total` supplies exactly the first-quadrant finite total and sign; `def-weil-abstract-derived-category` explicitly allows localization from the homotopy category. The current `lem-sfb-simplex-lattice-shuffle-boundary` states the unnormalized strings, signed chain-map identity, augmentation and monotone-postcomposition naturality. The current injective-resolution lift states augmented map existence for arbitrary abelian categories, and `new-t4-augmented-resolution-lift-homotopy` states the exactness and augmentation hypotheses of the preserved comparison argument. Thus no current dependency invalidates the argument allocation and no dependency substitution is required. I reread the three new statements in full. Step 1 uses the free-resolution conclusion and the specified universal shuffle with inverse and both homotopies; step 2 uses contravariant matrix evaluation, composition and total homotopies; step 3 uses homotopy-category localization; step 4 writes the commuting-coface and empty-shuffle calculation directly. I expanded the three child quotations in `citations.json` to their complete statements so the inverse, homotopy, variance and total-sign clauses used by the steps are all explicitly quoted, and rechecked literal substring coverage for all four citations.

I reread current blueprint direct-images paragraph (3), which supplies only the application, and the actual local Stacks texts at 08Q3/example-simplex-contractible and 0649/lemma-morphisms-lift-projective and 064A/lemma-morphisms-equal-up-to-homotopy-projective. The pointwise minimum-vertex contractions are not claimed natural; the universal comparison maps are natural. Internal nonnegative degrees make the total sums finite, and the matrix homotopy lowers horizontal degree so its internal signs cancel. The strict degree-zero augmentation is retained. I repeated the whole `WeilConjectures/` tag and concept search; no exact project declaration was found. The Sheaf theorem `AlgebraicTopology.BicosimplicialShuffle.exists_shuffle` at line 194 still ends in `sorry` at line 232, so it is not a finished attachment. I read the retained searches and their results; the questions and statements have not changed, so no service query was repeated or invented.

The correction for this return is the current-baseline delivery, the explicit comparison and dependency audit above, expanded citation evidence, and an updated split-report note. The approved mathematical split and the three new statement-only tasks are preserved. The old report sections describe earlier repairs and are retained as history; this section addresses the current landing return. No repository or launcher file was written, no Git command was run, no Lean was written or compiled, and no agent was started. The final required dry run and push follow this audit.
