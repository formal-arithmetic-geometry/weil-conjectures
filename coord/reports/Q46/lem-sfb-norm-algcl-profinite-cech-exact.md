# Q46 stage-1 repair: lem-sfb-norm-algcl-profinite-cech-exact

## Landing-refusal repair, 2026-10-22

The current return is the landing refusal recorded in `coord/returns/Q46.md` for returned head `5df49922d6f`: the reader approved the split, but the side-project completion had not been promoted to the live DAG. This is distinct from the earlier mathematical re-split order discussed in the historical sections below. The released stage-1 repair note remains present and requires at least two new nodes and an assembly of at most 3000 characters.

I compared the retained item against the current shared read clone without running git. Its statement and statement dependencies still agree exactly. The current DAG has the previous eight-step NI proof rather than this three-node Q46 extraction; none of the three proposed new ids is present there. I retained the extraction and refreshed the item from the current node metadata, retaining this delivery's stage-1 fields. The delivery command reconstructs the commit on freshly fetched `origin/sheaf-dag`, preserving the maintainer's metadata. The initial dry run completed successfully at `471d8892790`; after the changes below I run a new final dry run before pushing.

I re-read all four existing proof/statement interfaces used by the assembly: `lem-sfb-countable-split-profinite-cover`, `lem-sfb-algcl-countable-closed-finite-cover`, `lem-sfb-finite-quotient-fiber-product`, and `def-sfb-profinite-cech-tuples`, as well as the coefficient, continuous-function and universe definitions. Every quote in `citations.json` remains a verbatim substring of the current corresponding statement. In particular the cover still provides clopen oriented pairs and tail density; the exhaustion still provides increasing closed finite intermediate fields; and the pullback still has the claimed subspace topology and profinite conclusion. The general homotopy and the arithmetic and analytic new statements were reread in full. No citation needs substitution and no dependency has been silently taken from a proof.

I adjusted assembly step 2 to spell out the application hypotheses: the norm on the additive group of Omega is ultrametric, and the additive groups of the closed fields contain zero and are closed under differences. I also wrote the coordinate homeomorphism between one-tuples and T, so the analytic node's obstruction to a function on T is explicitly the obstruction to a degree-zero cochain. The revised assembly has 2100 characters, and every individual step is below 2000. The statement, all three new statements, searches, citation quotes and original proof guidance remain intact. This is a refreshed delivery with an explicit proof-interface repair, not an unchanged re-push. No source, target, unit route, Lean file or tool was changed.

The saved semantic-search hits and all queries in `searches.jsonl` were reread; the questions and statements have not changed, so no search was repeated or invented. The new statements remain independent arithmetic, topological-analytic and explicit homotopy obligations, with no proofs in their JSON. The signatures and the preserved review below remain applicable; the original global-exactness dispute and parent warning are still explicitly retained.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-profinite-cech-exact.json`: the statement is byte-for-byte unchanged as a decoded string. Replace the returned eight-step argument by four assembly steps, now 2100 characters total after the landing-refusal repair.
- `dag/nodes/sec-six-functors-basics/lem-sfb-algcl-small-escaping-sequence.json`: statement-only, status unsplit; no Mathlib match. Isolates the square-root-of-uniformizer and rescaling argument for an arbitrary sequence of finite intermediate fields.
- `dag/nodes/sec-six-functors-basics/lem-sfb-double-fibre-null-cocycle-obstruction.json`: statement-only, status unsplit; no Mathlib match. Isolates finite clopen truncation, continuity into the original coefficient group, the fibrewise cocycle identity, and the Baire contradiction for any closed additive-subgroup exhaustion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-topological-cech-homotopy.json`: statement-only, status unsplit; no Mathlib match. Isolates continuity and the full homotopy identity on all continuous cochains of a split continuous map, for general topological abelian coefficients.
- `citations.json`: one exact statement quote for each node used in each assembly step.
- `searches.jsonl`, `*-hits.txt`: actual msearch records and full printed results, retained for review. Helper scripts and preserved old work are sandbox-only research material.

Three new nodes, zero Mathlib leaves. No Lean, compiler, Lake, repository writes or direct git commands were used. The sandbox initially contained only dispatcher marker files, no delivered node/report/search log. I recovered the current item and the prior NI report read-only from the repository, preserved the report as `previous-report.md` and below, and preserved the eight old proof steps as `previous-proof.json` and below. The first dry run on that recovered version exited for the missing Q46 review signature; it was polled to exit before any later delivery invocation.

## Attachments

None. Searches in `lean/WeilConjectures/` by the blueprint tag and the Cech/profinite/section notions do not produce a declaration stating all clauses. The current theorem in `lean/Sheaf/Topology/NormAlgclProfiniteCechExact.lean:145` is still `by sorry`, so it is not an attachment. Its statement and docstring were read and agree with the current corrected item; its tuple helpers do not prove the theorem.

## WANTED

WANTED: an external reference for the original noncomplete-coefficient counterexample and its countably split cover. The motivating main-20261015 direct-images paragraph (3) does not state either result. The existing cover node and historical report retain the complete graph-closure construction.

WANTED: Serre, *Local Fields*, Ch. II, section 2, Proposition 3 and Ch. I, section 1, Proposition 1, for the existing finite-extension DVR input used by the escaping-sequence argument. The new node cites the motivating local-field coefficient setting, not a claim to have read this unavailable book.

WANTED: an exact external reference for the explicitly coordinatized continuous-cochain homotopy. Stacks Tag 016E, `example-fibre-products-simplicial-object`, supplies the nerve and coordinate maps, not the displayed homotopy. Mathlib's abstract extra-degeneracy route is recorded as a candidate, with its needed comparison left to the future worker.

## What the return required and how it is repaired

The return required at least two independent new statement-only work items, rather than an unchanged push or a shortened paraphrase. This repair adds three. None contains proof steps or proof dependencies. The parent is 1911 characters, below the 3000-character ceiling, and each new node states a separate argument with explicit inputs. The analytic obstruction needs a specified double-fibre cover, a specified closed-subgroup exhaustion, and a specified null sequence: it does not construct those inputs and is not the existential counterexample clause restated. The arithmetic node knows nothing about Cech cochains. The homotopy node is an operator identity on all cochains with arbitrary topological abelian coefficients, rather than a primitive-existence clause for Omega.

The exact allocation of the returned work is:

| Old step | Argument owner after repair |
|---|---|
| 1 | Existing `lem-sfb-countable-split-profinite-cover`, retained in assembly step 1; its output is the analytic node's explicit input. |
| 2 | Existing `lem-sfb-algcl-countable-closed-finite-cover`, retained in assembly step 1; its closed exhaustion is the analytic node's explicit input. |
| 3 | New `lem-sfb-algcl-small-escaping-sequence`: root of a uniformizer, integer valuation contradiction, nonzero p-adic rescaling, convergence. |
| 4 | New `lem-sfb-double-fibre-null-cocycle-obstruction`: actual function, finite clopen truncations, direct epsilon argument without completion. |
| 5 | Same analytic node: fibrewise potential and cancellation on every fibre triple. |
| 6 | Same analytic node: preimages of closed subgroups, Baire, tail density and monotonicity contradiction. |
| 7 | New `lem-sfb-split-topological-cech-homotopy`: insertion continuity and all alternating signs, including the first-deletion face and degree one. |
| 8 | Assembly step 4 retains the profinite fibre-product input, coordinate identification, pullback commuting with deletion, diagonal section and empty case. The new homotopy supplies the only homological argument. |

The original eight steps are transcribed verbatim below, not replaced by a compressed proof sketch. Their future proof obligations are the new nodes just named; this report does not mark any of those nodes as split.

## Proof guidance retained for each new worker

For `lem-sfb-algcl-small-escaping-sequence`, apply the existing `lem-weil-l-adic-extension-integers-dvr` to each F_k with its restricted norm. Choose a uniformizer pi_k. Its clauses 1, 4 and 5 give norm-one units, 0 < |pi_k| < 1 and x = u pi_k^m. Algebraic closedness gives b_k^2 = pi_k. If b_k were in F_k, then 2m = 1 for an integer m, a contradiction. Choose M_k >= 0 with |ell|^M_k |b_k| <= ell^(-k). The nonzero scalar ell^M_k and its inverse belong to F_k, so a_k = ell^M_k b_k is still outside F_k. The norm bound proves convergence. No increasing or exhaustion hypothesis was used, which explains the new statement's generality. The cited DVR node is an existing reusable tool, not a new proof dependency of the unsplit JSON.

For `lem-sfb-double-fibre-null-cocycle-obstruction`, the proof is precisely old steps 4, 5 and 6 below, with Omega replaced by the ultrametric additive group A and F_k replaced by H_k. Given epsilon, convergence supplies a tail bound epsilon/2; truncate f at N. On a neighbourhood where f_N is constant, the ultrametric inequality bounds ||f(y)-f(z)|| by the maximum of the two tail errors, so continuity holds in A itself. The finite nonzero loci are clopen; the complement is clopen too. Fibrewise potentials prove the three-term equation. If g exists, the closed subsets g^(-1)(H_j) cover nonempty compact Hausdorff T. Existing `lem-sfb-baire-closed-cover-interior` (Stacks Tag 0CQN, `lemma-baire-category-locally-compact`) gives a nonempty open U contained in one. Tail density gives k >= j with both points in U. Their difference is a_k in H_j, hence in H_k, contrary to the hypothesis. There is no implicit selection of a globally continuous fibrewise potential.

For `lem-sfb-split-topological-cech-homotopy`, the insertion map's coordinates are continuous; q sigma = id puts it in the equal-image subspace. Composition therefore preserves continuity and addition. Expand d f on (sigma(v),t_0,...,t_n):

    (h_(n+1) d f)(t_0,...,t_n)
      = f(t_0,...,t_n)
        - sum_(j=0)^n (-1)^j f(sigma(v),t_0,...,omit t_j,...,t_n)
      = f - d(h_n f).

The anchor in every face is sigma(v), including the face omitting t_0 because n >= 1 and all the q-images agree. This proves the full homotopy equation without assuming df = 0. This is the old step 7 argument, now a separately owned explicit cochain identity; the parent only specializes it and applies it after base change. Old step 8's coordinate calculation is retained verbatim below and in the short assembly. No topology on the space of all functions, beyond continuity of individual functions, is asserted.

## Searches and reuse

All three new nodes were searched before writing them with two different semantic LeanFinder queries, Loogle, LeanSearch and an actual Mathlib grep through msearch. Every query text in their JSON is exactly a logged query; results are the original digest records, not invented search summaries. All services answered. The full printed hits were read from `escaping-hits.txt`, `cocycle-hits.txt`, `contraction-hits.txt`.

The arithmetic hits include `PadicAlgCl.isAlgebraic`, `Padic.rat_dense`, `Valued.integer.exists_norm_lt_one` and the algebraic closure instances. I read `Mathlib/NumberTheory/Padics/Complex.lean:54` onward: those instances and norm-extension theorems do not choose an element outside an arbitrary finite subfield. Density inside Q_p does not imply that exclusion. The uniformizer/nonsquare argument remains real work.

The analytic hits concern finite clopen approximation, group cohomology, and continuity of functions under uniform convergence. None states an explicit cocycle on this equivalence relation or the obstruction from a closed additive-subgroup exhaustion. `ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal` approximates an already continuous function; it does not provide or prove continuity of our prescribed f, nor the Baire obstruction. Group cohomology has a different domain and differential.

For the homotopy node, I read `Mathlib/AlgebraicTopology/ExtraDegeneracy.lean:331` through 440. `CategoryTheory.Arrow.AugmentedCechNerve.extraDegeneracy` (line 368) and `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` (line 415) are useful candidates. They concern a categorical wide-pullback nerve and its alternating-face chain complex. To use them here, one must compare that nerve with the explicit subspace tuple model, pass contravariantly to continuous A-valued functions and check the specified h and differential. That is not a one-line specialization, so the new node is unsplit, with the candidates recorded. Generic `Homotopy.mkCoinductive` also requires the homotopy data and equations rather than proving this one.

Whole-DAG and whole-blueprint searches were made for Cech, double fibre, closed exhaustion, closed subgroup, contracting homotopy, small escaping, double-fibre, topological Cech, uniformizer and split cover. The large common-keyword lists were narrowed by reading the relevant statements. The existing set-theoretic free Cech resolution gives an algebraic contraction, not continuity into arbitrary A for the concrete subspace tuple spaces. The existing sheaf Cech local exactness nodes have scheme/open-cover coefficient domains, not these topological-space function groups. Existing local-norm-algcl-cocycle-descent and completion-boundary-descent concern profinite group cochains and scalar descent, not the fibre relation or its cocycle.

## Not duplicates

lem-sfb-algcl-small-escaping-sequence vs lem-weil-l-adic-extension-integers-dvr: the existing theorem supplies the valuation structure of each finite extension; the new statement constructs a norm-small sequence outside arbitrary given extensions in the algebraic closure.

lem-sfb-algcl-small-escaping-sequence vs lem-sfb-algcl-countable-closed-finite-cover: the existing theorem exhausts Omega by finite closed fields; the new one assumes any finite-field sequence and constructs escaping elements.

lem-sfb-double-fibre-null-cocycle-obstruction vs lem-sfb-countable-split-profinite-cover: the existing theorem constructs topological cover data only; the new statement assumes all those data and gives the analytic cocycle and its obstruction.

lem-sfb-double-fibre-null-cocycle-obstruction vs lem-sfb-baire-closed-cover-interior: both source records mention Tag 0CQN; the existing theorem is the closed-cover form of Baire, without a coefficient group, relation, prescribed cocycle or primitive equation.

lem-sfb-double-fibre-null-cocycle-obstruction vs lem-sfb-parameter-cochain-completion-boundary-descent: both mention Tag 0CQN, but the existing statement concerns continuous profinite-group cochains that already have a completed primitive and local scalar descent; the new statement constructs a fibre-relation cocycle with no global continuous primitive from explicit closed-subgroup and tail-density hypotheses.

lem-sfb-double-fibre-null-cocycle-obstruction vs lem-sfb-norm-algcl-profinite-cech-exact: both mention Tag 0CQN; the parent is an existential Q_l-algebraic-closure counterexample plus split/local exactness. The new statement is a conditional analytic construction in a general ultrametric additive group. It cannot supply the counterexample without the separate cover, arithmetic escape and exhaustion inputs, and says nothing about the parent's local replacement.

lem-sfb-split-topological-cech-homotopy vs def-sfb-profinite-cech-tuples: both mention Tag 016E; the existing definition introduces equal-image tuples and coordinate deletions and states no homotopy identity or continuity of an insertion operator.

lem-sfb-split-topological-cech-homotopy vs def-sfb-set-cech-nerve: both mention Tag 016E; the existing node defines the simplicial set attached to a set map. The new statement concerns all continuous cochains, explicit insertion operators and the full d h + h d identity for general topological spaces and topological abelian groups.

lem-sfb-split-topological-cech-homotopy vs lem-weil-pbc-set-cech-nerve-free-resolution: the existing theorem is a free-module chain resolution for surjective set maps. It has neither the topological tuple model nor continuous-function coefficients; comparison and continuity still require proof.

lem-sfb-split-topological-cech-homotopy vs lem-pc-cech-local-positive-exact: the existing theorem concerns restrictions of complexes of module sheaves on a scheme open family. It supplies no explicit continuous-cochain contraction for a continuous map of spaces.

## Review by Q46

For this landing-refusal repair I personally reread the current cited statements and checked every saved quote against them. The exact hypotheses and the degree-zero coordinate identification are now written explicitly in step 2, as recorded above. The finite fields remain closed in the actual noncomplete Omega; no primitive in a completion is used. The diagonal section and the signs in the homotopy still give the prescribed local formula, including degree one and the empty case. I read the current motivating blueprint paragraph (3), which supplies the setting but asserts neither the counterexample nor its analytic inputs; the report continues to identify those arguments as agent-written. I retained the previous source checks and full proof guidance below.

I read the current item, its Lean statement and docstring, the current chapter record and the legacy unit record. I read the actual main-20261015 direct-images proof, paragraph (3): it delegates proper/open direct-image stability and does not assert global Cech exactness. I preserved the corrected statement and its inherited STATEMENT-DISPUTED history. The earlier parent bar-augmentation use of the disproved global assertion remains a maintainer issue outside this item. The report and all prior arithmetic, topological and contraction arguments were retained; no source claim is silently upgraded.

For new arithmetic work I read the existing DVR theorem's full statement, and the motivating coefficient definition in the old blueprint. The norm-one-unit and integer-uniformizer-exponent conclusions really are stated by the existing theorem. The new statement's finite-dimensional intermediate-field hypotheses are exactly what that theorem needs; restricting the extended Omega norm gives the required absolute value. Algebraic closedness gives a root of X^2-pi_k. Nonzero p-adic scaling does not move membership into F_k. The prime ell=2 still has characteristic zero coefficients, and the integer equality 2m=1 is impossible independently of residue characteristic. No assertion that Omega is complete was introduced.

For new analytic work I read Stacks `topology.tex`, Tag 0CQN, label `lemma-baire-category-locally-compact`, and the entire existing Baire node. Its nonempty locally compact Hausdorff hypothesis applies to compact Hausdorff T (T itself is a compact neighbourhood). Every subgroup H_j is closed by hypothesis, so g^(-1)(H_j) is closed; the exhaustion covers every value of g. Monotonicity and k >= j are explicitly retained. I verified the clopen truncation argument directly in A and the fibrewise cancellation for all triples, including repetitions. These are now the new analytic node's future proof obligations, not assumptions hidden in the parent's assembly. The statement asks only for an ultrametric additive norm; multiplicative field structure was not used in these old steps. Finite or singleton covers cannot satisfy its tail-density condition with distinct v_k, so they are not false small counterexamples. A complete nonzero coefficient group cannot meet all the analytic hypotheses in a way contradicting Baire; completeness was neither used nor asserted.

For new homotopy work I read Stacks `simplicial.tex`, Tag 016E, label `example-fibre-products-simplicial-object`, for the coordinate nerve, and Mathlib's full extra-degeneracy candidate. I checked the insertion coordinate is in the subspace and continuous, h is additive, and the first-deletion and remaining signs give exactly d h + h d = id for n >= 1. At n=1 the faces leave one coordinate, so the common anchor is still sigma(v). Empty spaces cause no choice of a nonexistent t_0: the positive-length tuple domain is empty, and the unique function formula is vacuous. This is an explicit homotopy identity for arbitrary cochains, so the cocycle consequence used by the parent is immediate.

I opened every node statement cited by the new parent. Assembly step 1 uses the existing cover's actual nonempty/metrizable/fibre/clopen/tail-density clauses and the existing finite-field cover's actual increasing/closed/exhaustion clauses; E=Q_l meets the latter's finite-extension hypothesis. I read Stanford L19, Proposition 1.1.9, first bullet, page 3, for its countability/Baire motivation; the existing node, not a finite-stage factorization of functions, supplies the precise exhaustion. Step 2 uses exactly the new escaping sequence and the new analytic statement, with A=Omega and H_k the additive group of F_k. Every listed hypothesis comes from step 1, the item assumptions or the escape lemma; both output equations are the degree-one differential with the given sign convention. Step 3 sets df=0 in the new full homotopy identity, producing exactly the named formula for g. Step 4 uses the existing fibre-product statement solely for the stated compact Hausdorff totally disconnected pullback with its subspace topology; I read Stacks Tags 08ZY (`lemma-profinite`) and 0A2P (`lemma-describe-limits`) for that ambient setting. The rest of this step writes the coordinate maps and their commuting deletion equations explicitly, then applies the homotopy node to the diagonal section. It does not take any claim from a dependency's proof or assume a section of the original cover. `citations.json` quotes the entire relevant statement verbatim for each use, so each asserted conclusion can be read against its exact source node.

I checked delivery-errors B--E against the actual files. Each new node has its own inputs, decoded single-backslash TeX, statement dependencies for the named definitions, empty proof/proof_deps and null proof_origin. The new source records explicitly distinguish motivating blueprint text, Stacks inputs and agent arguments. No search is invented or recorded as a successful absence when unavailable. No new node is an attachment or a one-line Mathlib specialization. The current parent statement and Lean metadata are untouched. The creation chain still has a null blueprint ancestor (confirmed by the ancestor command); the precise paragraph is retained, and each new via list prepends this item to the inherited chain. No unit/chapter route or target is modified. All parent steps are below 2000 characters; the only relatively long argument is the explicit coordinate calculation in step 4, not a hidden comparison theorem.

## What remains

The three new nodes intentionally remain unsplit, to be claimed by separate workers. Their complete inherited proof guidance is retained above and in the verbatim old argument below. No mathematical gap in the parent assembly remains beyond those named dependencies. No other existing node was edited.

## Preserved returned proof, verbatim

### Old step 1

For clause (1), choose $q:T\to V$ and $(t_k^-,t_k^+)$ from [lem-sfb-countable-split-profinite-cover]. Thus every nonempty open subset of $T$ contains both points of some double fibre with arbitrarily large index, and the two oriented off-diagonal points of each such fibre are clopen in $R=T\times_VT$. These are the exact topological properties used below; no continuous section of $q$ is assumed.

### Old step 2

Apply [lem-sfb-algcl-countable-closed-finite-cover] with the finite intermediate field $E=\mathbf Q_\ell$. It gives increasing closed intermediate fields $F_k\subseteq\Omega$, finite over $\mathbf Q_\ell$, with $\Omega=\bigcup_kF_k$. In particular $F_j\subseteq F_k$ whenever $j\leq k$, and for any continuous $g:T\to\Omega$ the subsets $g^{-1}(F_j)$ are closed and cover $T$.

### Old step 3

For each $k$, apply [lem-weil-l-adic-extension-integers-dvr] to the finite extension $F_k$ with the restricted norm and choose a uniformizer $\pi_k$. Its conclusions give $0<|\pi_k|<1$, units of norm $1$, and $x=u\pi_k^m$ for $x\in F_k^\times$, $m\in\mathbf Z$. By algebraic closedness [def-weil-algebraic-closure] choose $b_k\in\Omega$ with $b_k^2=\pi_k$. It is outside $F_k$: otherwise $|b_k|=|\pi_k|^m$ for an integer $m$, so $|\pi_k|^{2m}=|\pi_k|$, forcing $2m=1$. By [def-weil-l-adic-numbers], $|\ell|=\ell^{-1}<1$. Choose an integer $M_k\geq0$ with $|\ell|^{M_k}|b_k|\leq\ell^{-k}$, and put $a_k=\ell^{M_k}b_k$. Then $|a_k|\leq\ell^{-k}$, hence $a_k\to0$, while $a_k\notin F_k$ because the nonzero scalar $\ell^{M_k}$ and its inverse belong to $F_k$.

### Old step 4

Define $f:R\to\Omega$ by $f(x,x)=0$, $f(t_k^-,t_k^+)=a_k$ and $f(t_k^+,t_k^-)=-a_k$. The fibre classification in [lem-sfb-countable-split-profinite-cover] exhausts $R$, so this defines an actual function. For each $N$, the function $f_N$ with these values for $k<N$ and zero elsewhere is continuous: its finitely many nonzero loci are clopen singletons. Given $\epsilon>0$, choose $N$ with $\ell^{-N}<\epsilon$. Around any $z\in R$ choose an open neighbourhood where $f_N$ is constant. On that neighbourhood the ultrametric inequality gives
$$|f(y)-f(z)|\leq\max(|f(y)-f_N(y)|,|f(z)-f_N(z)|)\leq\ell^{-N}<\epsilon.$$
This proves continuity into $\Omega$ itself; no infinite sum is used to define $f$.

### Old step 5

Every tuple in $T_V^3$ lies in a fibre of cardinality one or two. On a singleton fibre put $u=0$. On the fibre $\{t_k^-,t_k^+\}$ put $u(t_k^-)=0$ and $u(t_k^+)=a_k$. On each individual fibre $f(x,y)=u(y)-u(x)$, so
$$f(y,z)-f(x,z)+f(x,y)=(u(z)-u(y))-(u(z)-u(x))+(u(y)-u(x))=0.$$
Hence $d^1f=0$. These fibrewise functions $u$ are used only for this algebraic identity; no global continuity of them is claimed.

### Old step 6

Suppose a continuous $g:T\to\Omega$ satisfied $g(y)-g(x)=f(x,y)$. The closed sets $A_j=g^{-1}(F_j)$ cover the nonempty compact Hausdorff space $T$ by [lem-sfb-algcl-countable-closed-finite-cover]. Apply [lem-sfb-baire-closed-cover-interior] to $Y=X=T$ and $I=\mathbf N$: a compact Hausdorff space is locally compact, since the whole space is a compact neighbourhood of every point. Thus some $A_j$ contains a nonempty open subset $U$ of $T$. By [lem-sfb-countable-split-profinite-cover], choose $k\geq j$ with $t_k^-,t_k^+\in U$. Then
$$a_k=f(t_k^-,t_k^+)=g(t_k^+)-g(t_k^-)\in F_j\subseteq F_k,$$
contradicting step 3. This proves clause (1), with equality of cochains rather than any statement about closures.

### Old step 7

For clause (2), suppose $q\sigma=\mathrm{id}_V$. The map
$$(t_0,\ldots,t_{n-1})\longmapsto(\sigma(q(t_0)),t_0,\ldots,t_{n-1})$$
is continuous into $T_V^{n+1}$: its coordinates are continuous and the equal-image equations follow from $q\sigma=\mathrm{id}_V$. Thus the displayed $g$ is continuous. Apply $d^nf=0$ to $(\sigma(v),t_0,\ldots,t_n)$, where $v=q(t_i)$ for every $i$. Its first summand is $f(t_0,\ldots,t_n)$; the remaining summands give
$$0=f(t_0,\ldots,t_n)-\sum_{j=0}^n(-1)^jf(\sigma(v),t_0,\ldots,\widehat{t_j},\ldots,t_n)=f-d^{n-1}g.$$
The equality uses $\sigma(q(t_i))=\sigma(v)$ for every face, including deletion of $t_0$. It works for $n=1$.

### Old step 8

For any $q$, [lem-sfb-finite-quotient-fiber-product] applied to $T\to V\leftarrow T$ makes $T\times_VT$ profinite. The projection $q':T\times_VT\to T$ is continuous and has the continuous diagonal section $s\mapsto(s,s)$, so is surjective. Its $(n+1)$-fold fibre product over $T$ consists of $(s;t_0,\ldots,t_n)$ with all $q$-images equal; the tuple maps in both directions are coordinate maps and are continuous for the subspace topologies. Pullback sends $f$ to $(s;t_0,\ldots,t_n)\mapsto f(t_0,\ldots,t_n)$ and commutes with each coordinate deletion, hence preserves the cocycle equation. Step 7 with the diagonal section gives exactly
$$h(s;t_0,\ldots,t_{n-1})=f(s,t_0,\ldots,t_{n-1})$$
and $d^{n-1}h=q^*f$. If $T=V=\varnothing$, all these function groups are zero, and the same formulas are the unique zero functions. This completes clause (2).

## Preserved previous NI report (historical)

The following is the prior author report, retained as history of the corrected statement and searches. Its counts, ownership and step numbers describe the previous split, not the Q46 repair above.

# NI stage-1 report: lem-sfb-norm-algcl-profinite-cech-exact

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-norm-algcl-profinite-cech-exact.json`: corrected statement and eight-step split; the imported universal global exactness assertion is false.
- `dag/nodes/sec-six-functors-basics/lem-sfb-countable-split-profinite-cover.json`: one new statement-only pure-topology auxiliary, unsplit; no Mathlib match.
- `citations.json`: a verbatim statement quote for every node cited by every item step.
- `searches.jsonl`: actual msearch records. Earlier searches in the repository item were retained; the sandbox was initially empty of node/report work.

One new node, zero new Mathlib leaves. No Lean files or compilers were used, and no repository or launcher file was written.

## Attachments

None. Searches in `lean/WeilConjectures/` for the item tag and the profinite/noncomplete Cech notions found no declaration stating the item. In particular the unrelated topological Cech-comparison declarations do not supply this result. The Mathlib hits about Nobeling's locally constant integer functions are not this Cech complex.

## WANTED

WANTED: an exact external reference for the countably split Cantor-cover construction in `lem-sfb-countable-split-profinite-cover`. Its complete original construction is below. The motivating blueprint paragraph contains no assertion about such a cover.

WANTED: an exact external reference for the noncomplete-coefficient Cech counterexample itself. It is an agent argument below the motivating blueprint paragraph, explicitly marked as such. It is not attributed to Bhatt–Scholze.

The existing uniformizer theorem cites Serre, *Local Fields*, Ch. II §2 Proposition 3 and Ch. I §1 Proposition 1, as wanted literature. This delivery uses that existing node's stated clauses 1, 4 and 5 and creates no substitute theorem for it.

## Statement corrected

STATEMENT-DISPUTED: the imported assertion “for every profinite surjection, every positive-degree continuous Omega-valued Cech cocycle has an actual continuous Omega-valued primitive” is false already in degree one. Keeping the noncomplete coefficient field is essential. The correction states the counterexample and the valid explicit split-cover/local replacement; it does not claim to establish the false global input under a different coefficient convention.

Choose increasing closed finite intermediate fields F_k covering Omega. Choose a_k outside F_k with |a_k| <= ell^(-k). On the countably split Cantor cover below, let f be zero on the diagonal, a_k on (t_k^-,t_k^+), and -a_k on its reverse. The off-diagonal points are clopen and a_k tends to zero, so f is continuous into Omega. Every fibre has at most two points, so its degree-one cocycle equation holds identically. A hypothetical continuous primitive g has closed preimages g^(-1)(F_j) covering nonempty compact T. Baire gives a nonempty open U contained in one of them. U contains both points of a double fibre with k >= j, so a_k = g(t_k^+) - g(t_k^-) belongs to F_j, hence F_k, a contradiction.

The correct positive assertion requires no change of coefficients: a continuous section sigma of q gives g(t_0,...,t_(n-1)) = f(sigma(q(t_0)),t_0,...,t_(n-1)). Every q becomes split after the profinite base change T -> V. The item proves the formula and the cocycle identity explicitly, including degree one and the empty cover.

The parent `lem-sfb-norm-algcl-bar-augmentation` cites this item for the false universal positive exactness input. That use must be reopened by the maintainer; the corrected item cannot discharge that parent as currently written. I have not edited the parent. The same concern applies to any use that turns norm-Omega coefficients into a globally acyclic coefficient object on all profinite tests. This is a fault of the agent-created auxiliary, not evidence that the blueprint's open-image theorem itself is false.

The inherited title and source are maintainer-owned metadata and are retained in the submitted item; the statement, proof_origin and split_report explicitly record the correction. The maintainer should rename the title to “Failure of global profinite Cech exactness for norm-topological algebraic scalars; local replacement”.

## Pure-topology construction for the new node

Here is a proof of the new auxiliary for the independent reviewer; its node remains statement-only as required.

Let V = {0,1}^N with the product topology and its usual lexicographic order. Let D be the set of binary sequences that are eventually alternating. It is countable: specify a finite initial word, the index after which alternation starts, and the next bit. It is infinite and dense, since every finite cylinder contains such a sequence. In fact every nonempty cylinder contains infinitely many, by altering a bit arbitrarily far beyond the specified initial word and then alternating. Enumerate D without repetition as (v_k). Every v_k has infinitely many zeroes and ones, so is approached from both lexicographic sides by eventually constant sequences, which belong to V minus D. Eventually constant sequences also show that V minus D is dense.

For v outside D, let c_k(v) = 0 if v < v_k and 1 if v > v_k. Define c(v) = (c_k(v))_k. Set T to be the closure of the graph {(v,c(v)): v outside D} in V times {0,1}^N and let q be the first projection. The ambient space is a countable product of two-element discrete compact spaces. Tychonoff gives compactness; clopen cylinders separate points and form a basis, giving Hausdorffness and total disconnectedness. The weighted metric sum_i 2^(-i-1)|x_i-y_i| on each binary product, and the sum of the two factor metrics, induce its topology: fixing the first m coordinates bounds the tail, and a ball of radius less than the smallest specified coordinate weight fixes those coordinates. Restriction gives a compatible metric on closed T. A closed subset of a compact space is compact: add its open complement to an open covering and discard that extra member of a finite subcover. Thus T and V are metrizable profinite spaces.

For v != v_j, the threshold at v_j is locally constant near v. Indeed the first binary digit where v differs from v_j gives a cylinder on which the comparison has the same sign. Therefore at any point of T over v, every coordinate c_j is forced except possibly the one j for which v=v_j. For v outside D the graph itself supplies the unique point. For v=v_k, the points approaching v_k from below and from above outside D show, for every finite cylinder neighbourhood in the ambient product, that both choices of the kth coordinate occur in the graph closure. The other finitely many specified coordinates are locally constant since their thresholds differ from v_k. This proves that the fibre is exactly two points t_k^- and t_k^+, differing only in the kth auxiliary bit. It also proves q is surjective and T is nonempty.

In R = T times_V T, the clopen condition “the first point has kth auxiliary bit 0 and the second has kth auxiliary bit 1” singles out exactly (t_k^-,t_k^+). To see this, any unequal kth bits over a common v force v=v_k by the previous paragraph. The reverse condition singles out the reverse ordered pair. Hence these are clopen singletons. Every other relation point is diagonal, by the fibre classification.

Finally let U be nonempty open in T. The defining graph is dense in T, so choose a graph point (w,c(w)) in U with w outside D. Its q-fibre is a singleton and hence is contained in U. The closed subset T minus U is compact. Its projection is compact and therefore closed in Hausdorff V, so B = V minus q(T minus U) is an open neighbourhood of w, and q^(-1)(B) is contained in U. Every nonempty open B contains infinitely many v_k, as established with cylinders. Choose k >= N with v_k in B. Then both t_k^- and t_k^+ belong to U. This proves the exact tail-density conclusion used by the counterexample.

This is a construction of a topological cover, independent of the scalar field, the Cech differential and cohomological exactness. It is strictly smaller than the item and is not one of its clauses moved into a new node. Its complete construction is not hidden behind the word “standard”.

## Searches and reuse

Before creating the topology node I searched the whole DAG and project Lean for split Cantor covers, double fibres, singleton-fibre density, and irreducible profinite covers; no node with these properties was found. `tools/blueprint_refs.py search` for `Cantor`, `split Cantor`, `double fibre`, and `countable split profinite` found no blueprint duplicate. Searches for `Cech`, `positive profinite`, and `noncomplete` found no blueprint statement of the corrected item. The inherited source paragraph (3) was read in full: it delegates the open-coefficient theorem, and does not state universal Cech exactness for noncomplete coefficients.

For the new node, two semantic phrasings, a LeanSearch query, two Loogle patterns, and source greps ran through msearch and were read. `exists_retractionCantorSet` and `cantorToHilbert_surjective` in Mathlib/Topology/MetricSpace/HausdorffAlexandroff.lean:27–100 were inspected. They construct surjections/retractions and give no double-fibre or tail-density control. The other hits give finite clopen approximations or metrization, not this cover. The node's mathlib_searches records the queries actually logged, with the actual digest records and a no-match verdict. The item retains its earlier searches and adds the searches made here; neither its original false assertion nor the corrected counterexample is a Mathlib leaf.

Reused existing nodes rather than creating duplicates: `lem-sfb-algcl-countable-closed-finite-cover`, `lem-sfb-baire-closed-cover-interior`, `lem-weil-l-adic-extension-integers-dvr`, and `lem-sfb-finite-quotient-fiber-product`. The Baire node already is a Mathlib leaf. The uniformizer theorem is declared in split_report.tool_uses as the generic local-field input of another unit; it does not replace a six-functor proof step.

## Not duplicates

The new topology node has no Stacks tag shared with an existing node. `lem-sfb-countable-split-profinite-cover` vs `lem-sfb-finite-quotient-fiber-product`: the existing node proves profinite fibre-product topology and its finite-partition inverse-limit description, and does not construct a surjection with dense double fibres. `lem-sfb-countable-split-profinite-cover` vs `lem-sfb-profinite-metric-function-quotients`: the existing node factors a continuous map on S times G^r through metrizable quotients, and gives neither double fibres nor clopen off-diagonal points. `lem-sfb-countable-split-profinite-cover` vs `lem-sfb-normed-scalar-profinite-cech-exact`: that node concerns positive exactness for a complete finite-extension coefficient field; the new node is only a pure-topology construction and makes no exactness assertion.

## Review by NI

I read the item and its motivating main-20261015 direct-images proof, paragraph (3), against the chapter and unit records. The seed is explicitly an agent-formulated WANTED noncomplete input. Its complete finite-extension neighbour does not apply: a primitive in a completion or a replacement of all continuous functions by finite-stage functions would change the problem. This led me to test actual degree-one cocycles and find the counterexample above. I corrected the statement openly, rather than treating a theorem for complete coefficients as a proof.

For step 1 I checked every clause of the new topology statement against the construction above. The only inputs the item takes are exactly its fibre classification, the clopen oriented pairs and the double-fibre tail-density property. The source for the new node is only the motivating blueprint paragraph, not a claimed external topology theorem; I marked the reference as wanted and supplied the full original construction here. The Cantor graph closure stays within the permitted profinite universes.

For step 2 I read the existing countable closed-cover node's entire statement and Stanford L19, Proposition 1.1.9, first bullet, p. 3. The cited statement actually gives an increasing closed exhaustion by finite intermediate fields; it is stronger and more precise than just countability of isomorphism classes. E = Q_ell satisfies its finite-extension hypothesis. No claim that f or g has image in a single finite field is made.

For step 3 I read the full statement of the existing DVR theorem and its referenced blueprint definition. Clauses 1, 4 and 5 give the norm-one units, the uniformizer with norm strictly between zero and one, and the integer power decomposition. Applied to F_k with its restricted extended norm, every hypothesis is present. The definition of algebraic closure supplies a root of X^2 - pi_k. Its absence from F_k follows by the integer-exponent norm calculation, and scaling by a nonzero power of ell preserves that absence. This small argument is written out in the step, so it requires no additional lemma node. I did not present the unavailable Serre chapter as read.

In step 4 the topology statement really says that each oriented off-diagonal singleton is clopen. The finite truncations therefore are continuous. I checked the direct epsilon estimate in Omega, with no appeal to completeness or to an undefined infinite sum. At the exceptional oriented pair with index below N, its clopen singleton is the required neighbourhood; elsewhere the complement of the finite exceptional set is open. In step 5 I checked all triples by the fibrewise potential identity. This is an elementary cancellation and does not assert a global potential.

In step 6 I read Stacks Topology Tag 0CQN, lemma-baire-category-locally-compact, and the Baire leaf's entire statement. The cover consists of closed subsets of the actual compact Hausdorff nonempty T, so the Baire hypotheses hold. The tail-density clause supplies k >= j, and monotonicity from the exhaustion gives F_j subset F_k. Thus the contradiction is an equality of values in the original field. Every non-elementary fact here is a cited statement, not something taken from a cited node's proof.

For steps 7 and 8 I checked the two contraction formulas, the signs, and the first-coordinate-deletion case. The common q-image ensures the distinguished point used by every face is the same. The fibre-product node's statement supplies exactly that T times_V T is profinite, with the correct subspace topology. The diagonal is a continuous section and the tuple identifications are coordinate maps, so the split contraction gives the asserted pulled-back primitive without an unproved derived comparison. I read the stated fibre-product lemma and Stacks Topology Tags 08ZY (lemma-profinite) and 0A2P (lemma-describe-limits) for its ambient setting.

Edge checks: degree n=1 uses no negative cochains; empty T=V gives only zero functions in the replacement clause; a finite cover with a set section has the usual contraction, so cannot be this counterexample. The construction works at ell=2, since the coefficient field has characteristic zero and the nonsquare proof uses valuation exponents, not residue characteristic. The complete-field exactness node is consistent with this counterexample: the Baire argument relies on Omega being a countable union of closed finite fields, a property not asserted for its completion. A singleton or finite topology cannot satisfy the new lemma's tail-density property, so the construction necessarily remains nonempty and infinite. No source is SGA.

I checked delivery-errors B–E point by point: the new node is self-contained and statement-only; definitions are supplied inline or cited; TeX has single decoded backslashes; no search is invented; no blueprint duplicate was found; every cited statement was opened and quoted in citations.json; no proof-only content of a cited node was used; the new input is a pure-topology construction rather than a relocated exactness clause; the original false statement has an explicit counterexample and a named correction; the actual cochain maps and their signs are written out. None of the non-elementary item steps exceeds 2000 characters. The ancestor command returns None because the inherited created.item chain ends in a module name rather than a node; I preserved that provenance and named the motivating paragraph in from.place and split_report.blueprint.

## Unfinished work and consequences

The original global exactness assertion cannot be proved because it is false. The corrected diagnostic and local replacement are completely split by one level, with the pure-topology construction isolated as the only new unsplit node. Its proof is supplied above for review, while the new JSON correctly contains only its statement. The parent's dependence on the disproved global claim requires a separate maintainer decision and repair outside this worker's ownership.
