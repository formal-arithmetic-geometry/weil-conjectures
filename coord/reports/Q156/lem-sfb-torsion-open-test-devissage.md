# Stage-1 report: lem-sfb-torsion-open-test-devissage

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torsion-open-test-devissage.json: statement, split; no Mathlib match. Six proof steps, no new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for every step/node citation.
- searches.jsonl: results written by the required msearch command; historical item searches are retained in the item.

## Attachments

None. Searching the project WeilConjectures source for the exact blueprint id found no declaration. The WeaklyContractibleCohomology module supplies general projectivity/Leray infrastructure, not this cyclic-to-arbitrary bounded torsion statement. No finished declaration states all the item clauses.

## WANTED

None for this split. The original analytical norm-coefficient issue in the ancestor is outside this item; its proof is not being asserted here.

## Corrections and route

The statement is retained unchanged. The source blueprint paragraph (3) states the open-direct-image preservation input and does not itself state this returned sublemma. The proof is accordingly marked agent-written. Its argument is the required cyclic-coefficient evaluation, finite-primary devissage, then filtered continuity; no SGA source or trace route is used.

The source.unit record sk-thm-sf-ctf-stability remains the older sec-six-functors unit while the inherited item.chapter is sec-six-functors-basics. This mismatch predates this split. Neither fixed field was changed. tools/blueprint_refs.py ancestor returns None for this inherited created-node chain; its null from.node and existing via chain are retained, with the paragraph place already specified. Searches of the whole blueprint for cyclic, torsion restriction, weakly contractible, derived evaluation, Leray, filtered colimit and constant exact found tools but no duplicate of the item. No new nodes were made.

The main points requiring care were that coefficient forgetting need not preserve injectivity, that a final-object Leray node restricted to the purity setting cannot be used for arbitrary schemes, and that the full finite abelian group classification is unnecessary. The split uses the existing general K-injective right-adjoint lemma, the existing bounded-below coefficient-forgetting comparison, and explicit induction on group cardinality instead. There is no appeal to a geometric-point conservativity assertion on the pro-etale site.

## Not duplicates

No new-node/existing-node pairs: zero new nodes. Existing generic tools are cited directly.

## Review by Q156

I read the item's complete statement and its ancestor torsion-acyclic-norm-coefficient-test statement and dependency list, the chapter record, the unit record, and paragraph (3) of the current main-20261015 direct-images proof. I read delivery-errors B–E, including the repeated historical copy, and checked that the proof actually assembles the item rather than renaming its clauses. Every step is below 2000 characters. There are no new statement-only nodes requiring their own source or edge-case review.

For step 1 I read Stacks sites-cohomology.tex, lemma-Leray-unbounded (0D6H), its objectwise assertion, and lemma-derived-pushforward-composition (0D6E); I read derived.tex lemma-adjoint-preserve-K-injectives (08BJ). The cited right-adjoint node states precisely preservation of K-injectives under an exact left adjoint. The cited operations node supplies that exact module adjunction and the formula (j_*I)(V)=I(W times_X V). The weak-contractible evaluation node assumes exactly the epi-surjectivity property the item gives, not a stronger ring-theoretic meaning of w-contractible. The restriction-injectives node states agreement of objectwise derived evaluation with derived sections on the slice scheme. Both V→X and T→W are pro-etale objects, so its weak-etale hypothesis holds. The proof writes the section-level unit followed by the resolution map, fixing the actual restriction arrow. It does not cite the purity-only global-evaluation lemma, whose hypotheses would not fit.

For step 2 I read the entire statements of lem-cbc-sieve-module-sheafification, lem-pe-left-module-derived-evaluation-forget and lem-pe-constant-left-module-inverse-image. The first explicitly identifies underlying abelian sheafification. The second explicitly identifies forgotten module evaluation with abelian derived evaluation, for bounded-below complexes, naturally for restrictions and cohomology pullback. The third explicitly identifies constant coefficients, scalar forgetting and adjunction units under inverse image. Our sheaves are degree zero and the resolutions can be nonnegative, so the bounded-below restriction is satisfied; no general unbounded coefficient-forgetting theorem is needed. I checked Stacks 03FD (module/abelian cohomology agreement) and 0946 (weakly contractible evaluation) as the source route. The proof never claims the forgotten injective is injective.

For step 3 I read Stacks sites-modules.tex lemma-constant-exact (093J), and the cited sheafification-exact node, which gives finite-limit and colimit preservation. Applied to constant presheaves this gives exactly the two short exact sheaf sequences. I opened the statements of the short-exact triangle, triangulated right-derived functor and long-exact homology nodes: together they give the cohomology exact sequence on each scheme, with no etale-only lemma being applied to pro-etale sheaves. The short five lemma states the middle-map conclusion for short exact rows. The positive vanishing of the outer terms makes the section rows short exact; commutativity is underived section naturality, so no missing connecting-map comparison is hidden here.

For step 4 I checked the zero group, a single nonzero cyclic group, and a noncyclic group killed by ell. The induction does not require a structure theorem: the order of b divides ell^n by division with remainder, hence is ell^s; its cosets give a strictly smaller quotient. The extension-closure argument is in the preceding proof step. This is elementary finite-group arithmetic, not a new node or a relabelled clause.

For step 5 I opened the complete det-pe-bounded-continuity-sections statement and read proetale.tex lemma-compute-cohomology (09A2) and the following qcqs direct-sum/homotopy-colimit lemma (09A3), the source of the existing bounded-continuity tool. The statement explicitly assumes small filtered diagrams, qcqs objects and a common termwise lower bound. The finite subgroups of M are a set in the coefficient universe, are directed under sum and exhaust M; their degree-zero complexes have common bound zero. Both V and its principal open T are affine, hence qcqs. I checked the colimit identification using sheafification's colimit preservation, rather than assuming the raw constant presheaf is already a sheaf. The comparison maps on H^0 commute with restriction because their representatives are sections and both paths are the same section restriction followed by inclusion into M. Positive cohomology of a colimit is computed by precisely the cited statement.

For step 6 I checked the derived localization definition: a map inducing isomorphisms on every cohomology group has acyclic cone and is invertible. Nonnegative resolutions justify absence of negative groups. Naturality belongs to the original restriction transformation; no nonfunctorial choice of finite subgroup is used to define a new arrow. The identity open is the identity, the zero group gives zero, and empty schemes require no sections to be chosen. If T is empty while V is not, the cyclic hypothesis already forces the cyclic comparison used in step 1, so the argument does not silently assume T nonempty.

I checked every uses entry against its node's full statement and wrote that literal text into citations.json. All off-unit non-leaf facts are explicitly declared generic tool uses in split_report; they support, rather than replace, the unit's open-direct-image route. No definition is cited as evidence for an additional theorem. No missing non-elementary input was converted into an elementary step. New-node checks B1–B10 are vacuous; source, citation, cycle and mathematical hypothesis checks C–E were applied to every reused node.

## Unfinished work

No mathematical part of the split remains. The cited unsplit tools remain existing DAG items, as permitted by one-level splitting. Delivery validation is recorded by the required delivery command.
