# NU stage-1 report: lem-sfb-elliptic-sobolev-closed-range

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-elliptic-sobolev-closed-range.json: unchanged statement, five-step proof, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-bundle-sobolev-rellich.json: statement, unsplit; no Mathlib match after semantic searches in two phrasings, Loogle and source grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-elliptic-global-garding-estimate.json: statement, unsplit; no Mathlib match after semantic searches in two phrasings, Loogle and source grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-compact-remainder-coercivity.json: statement, unsplit; no Mathlib match after semantic searches in two phrasings, Loogle and source grep.
- citations.json: verbatim statement quotations for every cited node in every item step.
- searches.jsonl: genuine msearch.py results; the searches were read before recording verdicts.

## Attachments

None. Searching the live lean/WeilConjectures by the blueprint tag, elliptic, Sobolev, compact remainder, and the proposed ids found no project declaration proving this item or the new statements. Algebraic elliptic-curve references do not concern this analytic lemma. lean/Sheaf was read as additional reference only. No Lean was written or compiled.

The existing Mathlib leaves lem-sfb-hilbert-orthogonal-projection and lem-sfb-dense-subspace-contractive-extension are reused. Their statements were opened, and their Mathlib sources were checked: Projection/Basic.lean, lines 54, 85–87 and 427–431; Normed/Operator/Extend.lean, lines 190, 194–195, 201–203 and 209–210. No duplicate leaf was created.

## WANTED

WANTED: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, VI §§1–2, printed pp.287–290, for the item and all three new nodes. The PDF is absent from the local literature directory; the existing item's online URL was read directly, without downloading or writing to literature. URL: https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf .

The whole argument is marked agent-origin: the source provides the analytic inputs and a finite-codimension proof of closed range, while this delivery uses a kernel-complement compactness variant and writes out the bounded-extension and distributional-limit arguments. No Stacks tag asserts these analytic results, so none is invented. No SGA source is used.

## Corrections and source comparison

There is no statement dispute. Every clause and hypothesis of the original item is retained. In particular this is closed range of the Sobolev realization, not the assertion that the smooth image itself is closed in L2. No finite codimension, smoothness of the kernel, or self-adjointness is assumed or smuggled into the argument.

Demailly VI §1 treats operators between two bundles and real or complex scalars, and defines the L2 pairing in (1.4). VI §2 states Rellich (2.2), Gårding (2.3), and proves closed Sobolev range inside (2.4)(ii). The local elliptic-system estimate applies between G and H; equality of the bundles is not used. The new Gårding node states only the smooth-section estimate, not the stronger regularity conclusion of Demailly (2.3). The new compact-remainder node is explicitly an abstract lemma isolated by NU, not a quotation of a separately numbered Demailly theorem.

During self-review I made atlas invariance explicit in the Sobolev/Rellich statement. The finite atlas must trivialize both G and H to estimate Q, and equivalence of Sobolev norms is what permits a refinement; merely identifying the weak-derivative images would not supply the necessary bound. The proof now cites exactly that equivalence. The displayed coefficient argument bounds Q directly, avoiding an unproved elliptic extension assertion.

## Not duplicates

The entire DAG was searched for Sobolev, Rellich, Gårding/Garding, compact remainder, orthogonal projection, completion-extension declaration names, and the new ids. Blueprint searches were run for Sobolev, Rellich, Gårding/Garding, elliptic, compact operator, compact remainder, closed range, orthogonal and completion; the analytic keywords had no blueprint match. The existing Sobolev item and its neighbouring elliptic nodes were opened. Their source places and statements differ as follows.

- lem-sfb-bundle-sobolev-rellich vs lem-sfb-elliptic-sobolev-closed-range: arbitrary metric bundles and Sobolev compactness/weak-derivative realization; no differential operator or closed-range conclusion.
- lem-sfb-elliptic-global-garding-estimate vs lem-sfb-elliptic-sobolev-closed-range: an inequality on smooth sections only, with a lower-order remainder; it asserts neither extension nor closed range.
- lem-sfb-compact-remainder-coercivity vs lem-sfb-elliptic-sobolev-closed-range: arbitrary bounded maps of normed/Hilbert spaces with a compact remainder; its conclusion is an estimate on the kernel complement, with no manifold, Sobolev space, extension or closed-range conclusion.
- lem-sfb-elliptic-global-garding-estimate vs lem-sfb-elliptic-adjoint-regularity: quantitative smooth-section norm estimate, whereas the existing node gives qualitative smoothness of a weak solution with smooth right-hand side. Neither is a one-line specialization of the other.
- lem-sfb-bundle-sobolev-rellich vs lem-sfb-elliptic-smooth-fredholm-decomposition: foundational compact inclusion, whereas the existing node asserts a smooth-image/adjoint-kernel decomposition for elliptic operators.
- lem-sfb-compact-remainder-coercivity vs lem-sfb-hilbert-orthogonal-projection: quantitative estimate from compactness; the existing Mathlib leaf supplies only orthogonal decomposition and is reused where needed.

The new nodes do not carry Stacks tags, so there are no same-tag pairs. All three are substantive analytic statements, left statement-only with no proof sketch embedded in their statements. The item carries the construction and the final closed-range argument, rather than delegating the whole item to a renamed elliptic closed-range assertion. The inherited nearest blueprint ancestor is null (confirmed by blueprint_refs.py ancestor); each new node retains that value and the full inherited via chain, prepending this item, with an exact analytic source place. The latest blueprint direct-images proof (3) was read; no chapter or unit route is changed, and this is not the unit's key node, so no unit record is edited.

## Mathlib assessment

The Sobolev search found TemperedDistribution.MemSobolev, operations on Euclidean Bessel-potential spaces, smooth-section types and test-function embeddings. Reading Analysis/Distribution/Sobolev.lean and Analysis/FunctionalSpaces/SobolevInequality.lean showed that these are not compact-manifold bundle Sobolev realization or Rellich compactness. The Gårding searches found Euclidean Gagliardo–Nirenberg estimates and algebraic elliptic-curve names, not an elliptic-system estimate. The compact-remainder searches found IsCoercive.bounded_below and isClosed_range, orthogonal_ker, and bounded-image properties of compact operators. LaxMilgram.lean was opened: its bilinear coercivity hypothesis is precisely not furnished by the remainder inequality, so it is not a match. The abstract anti-Lipschitz closed-range result does not supply the missing compactness argument either. All these searches and actual result summaries are preserved. Services answered successfully; none was misrecorded as unavailable.

## Review by NU

I read the item's entire statement, its parent Fredholm decomposition and neighbouring weak-regularity statement, the chapter/unit records, the latest blueprint direct-images proof (3), the worker/stage rules and delivery-errors B–E. The online Demailly pages were read for the item and the new nodes: VI (1.4) gives the L2 model, the opening of VI §2 gives Sobolev Hilbert spaces, (2.2) supplies compactness, (2.3) supplies the norm estimate, and the proof of (2.4)(ii) shows how compactness removes the L2 remainder. For the abstract coercivity node I verified the normalized-sequence proof independently: if no bound exists, choose unit v_n in the kernel complement with Tv_n tending to zero. Compactness gives a convergent subsequence of Jv_n. The assumed inequality on differences makes v_n Cauchy in E. Its limit has norm one, belongs to ker T by continuity, and remains perpendicular to ker T by continuity of each inner product. Taking the inner product with itself contradicts norm one. This is the genuine lemma hidden in the compactness step, so it is stated as its own node.

Step 1 cites only the Sobolev/Rellich statement, which actually provides all the identifications and the compact injection used. Both bundles satisfy its finite-rank, compact-base and positive-metric hypotheses. Step 2 cites that node for equivalent norms and density, and the existing dense-contraction extension leaf for existence and uniqueness. I checked that normalizing by a strictly positive M gives the required contraction, that the domain is identified with the dense smooth subspace using the injective completion map, and that F is complete by step 1. The coefficient bound is a finite sum on compact supports; it requires no integration-by-parts theorem or adjoint regularity. Step 3 uses the weak-derivative realization in the Sobolev node. Convergence of the derivative coordinates follows from the defining completion norm; its distributional interpretation is the exact image characterization of that node. Testing against a compactly supported smooth section and using Cauchy–Schwarz writes out the compatibility, rather than merely saying it transports.

Step 4 cites the smooth Gårding estimate and the abstract compact-remainder lemma. The estimate extends to all Hk by taking smooth limits through the already bounded maps. E is Hilbert, F and Z=L2(G) are normed, J is compact, T is bounded, and C is positive, so every hypothesis of the abstract lemma is present. Step 5 cites the existing Hilbert orthogonal-decomposition statement. Its closed-subspace hypothesis holds because ker T is the inverse image of zero under a continuous map. The difference of two perpendicular representatives is still perpendicular; the norm estimate makes these representatives Cauchy. Completeness of E, continuity of T and the norm-metric criterion for closedness finish the proof explicitly. No unquoted part of a cited node's proof is used. citations.json contains the actual statement text for each of these citations.

I tested small cases: the empty base and rank-zero bundles give zero Hilbert spaces and the inequalities remain valid; disconnected compact bases cause no issue with a finite atlas. The k>=1 hypothesis is used for Rellich compactness; the item does not claim compactness for H0=L2 in positive dimension. For the abstract lemma, T=0 leaves only the zero vector in the kernel complement, J=0 reduces to the existing global bound, and noninjective J is permitted by the normalized-sequence proof. Completeness is required only for E in that lemma. The Gårding remainder is essential when Q has a kernel, e.g. differentiation on a circle; it was not dropped until restricting to the kernel complement. No step exceeds 2000 characters, and the compactness sublemma is extracted rather than hidden inline.

## Unfinished work

No part of this stage-1 split remains unfinished. The three new statement-only nodes are future queue items, as required; they are not asserted to be already formalized. No Lean edits, compiles, builds, repository writes, launcher edits or additional agents were used.
