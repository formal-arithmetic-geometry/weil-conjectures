## Worker report

Current repair, 2026-10-21. This section supersedes the retained historical reports below. I continued all five sandbox node files, compared the parent against the current read-only repository, and read the prior searches and outputs. The latest route note explicitly resolves the former schema conflict: NEW helpers must be statement-only, status unsplit, without proof steps. I have made that substantive repair. Their earlier arguments and citations are retained below for later stage-1 workers, rather than discarded or claimed as completed splits.

Files written:

- dag/nodes/sec-six-functors-basics/sk-lem-stratified-lattice.json: split parent, same complete statement and Lean record; seven assembly steps, 2424 proof characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-lattice-pullback.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-etale-trace-image.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-sum-lattice.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-continuous-lattice-sum.json: statement, unsplit; no Mathlib match.
- dag/units/sk-lem-stratified-lattice.json: only realized and realized_by, as required for the key node.
- citations.json: literal statement quotes for each parent citation, including the newly explicit splitting and finite-sum citations.

Attachments: none. The tagged declaration in lean/Sheaf/Paper/StratifiedLattice.lean remains sorry; the project-source tag/notion searches supply no finished exact attachment.

WANTED: none.

Fault repaired: the first repair incorrectly interpreted the coarse-split return as requiring already-proved helpers and repeatedly blocked at the unsplit-only gate. The latest human route note explicitly requires the usual one-level statement-only delivery, now implemented without tool changes or bypasses. I also corrected a C4 gap: the trace helper's statement gives an image formula on any splitting, not existence of a covering of splittings. Parent step 5 now cites lem-weil-pbc-finite-etale-etale-local-split for that existence. Step 6 explicitly uses the finite-sum node as well as the continuous-function image node, so all four new nodes are reached directly by the parent's proof.

The parent split is complete; the four new statement-only helpers intentionally await their own future stage-1 splits. No Lean file, repository file or launcher file was written; no compiler, Lake, build, or direct git command was run.

## Review by Q46

I read the main-20261015 item, its five-paragraph unit and its chapter, and the full blueprint proof and trace detail. The parent statement is unchanged, including coefficient conventions, varying ranks, empty cases, and the nodal example. I read Bhatt–Scholze Proposition 6.8.4(6) and the first paragraph of Lemma 6.8.13: they supply the local-lattice and finite-stratification setting. The chosen construction stays on the blueprint's trace route. I read Stacks 03S0 (etale-cohomology-lemma-etale-stratified-finite), 04HN (etale-lemma-finite-etale-etale-local) and 0AUW(3) (more-algebra-lemma-dedekind-torsion-free-flat). No SGA source is used.

Step 1 uses the opened statements of lem-weil-pbc-finite-type-over-noetherian for scheme Noetherianity, lem-sc-affine-noetherian-underlying-space on the finite affine charts, and lem-sfb-noetherian-space-compact-subsets for quasi-compactness. Spec k is Noetherian since k is a field; finite type is a standing hypothesis. Stabilization on a finite cover proves the underlying topological assertion, and compactness of affine intersections gives quasi-separatedness.

Step 2 uses lem-weil-pbc-continuous-coefficient-realizations exactly for the ring comparison and its compatibility with A→E, and det-prop-sfb-qlbar-colimit-x-invert-ell for coefficient localization. The ultrametric clopen balls verify total disconnectedness. Step 3 uses lem-weil-pbc-continuous-etale-local-lattice, whose statement explicitly supplies a qcqs source and an étale surjection for topologically Noetherian X. In free coordinates its scalar-extension unit is injective, so the supplied integral object is an actual embedded lattice. This elementary coordinate check needs neither a normality assumption nor a flat scheme morphism.

Step 4 applies lem-weil-pbc-etale-stratified-finite with both qcqs hypotheses established, and uses lem-sfb-lattice-pullback on V×_X S→V. Its statement, opened in this session, preserves the monomorphism and the inclusion-induced rationalization, rather than only local freeness. Surjectivity of each base change follows by the fibre description. Step 5 uses lem-sfb-finite-etale-trace-image for the actual pro-étale trace and its integral sheaf image, and the separately cited lem-weil-pbc-finite-etale-etale-local-split for covering splitting neighbourhoods. The latter statement gives an étale neighbourhood of every point and finite clopen sheets isomorphic to the neighbourhood. Nonempty sheet sets follow from surjectivity on nonempty neighbourhoods. No étale-site trace definition is mistaken for a pro-étale theorem.

Step 6 uses lem-weil-pbc-lattice-sheaf-locally-constant: its statement identifies lattice classes with the constant coset sheaf and identifies the embedded representatives g A^r. Finite successive cover refinement fixes all classes together after trivializing L. The nonempty finite index set and full rank hypotheses of both new sum nodes now hold. lem-sfb-finite-sum-lattice supplies the full basis and its homeomorphism; lem-sfb-continuous-lattice-sum supplies the precise equality of submodule sheaves and the inclusion-induced rationalization. These are distinct from mere equality of fibres. Step 7 is the local definition of lisse and gluing of mutually inverse maps; empty X and zero rank are explicitly covered.

I reviewed each new statement independently. Pullback permits arbitrary scheme maps because it concerns cartesian coefficient modules, not structure-sheaf modules. Trace/image allows nonsurjective finite covers, including the empty cover, and arbitrary integral submodules; it makes no lattice or stratification conclusion. Finite sums require a nonempty finite index set: without nonemptiness full rank can fail in positive rank. Their topology is explicitly the subspace topology, and no unramifiedness assumption on E is introduced. The continuous-sum node asserts a continuous section and equality on every test space, rather than assuming algebraic image computations imply a sheaf formula. These are strictly smaller reusable assertions, not renamed clauses saying that strata carry lattices.

Small cases checked: empty X, empty finite cover for the trace, degree-one covers, zero rank, repeated lattices, and the rank-one sum A+π^{-m}A=π^{-m}A for m≥0. Ramification changes neither DVR freeness nor the basis-matrix topology. The zero sum for an empty cover is kept out of full-rank uses by the parent's surjectivity hypothesis. Each new node has complete objects/hypotheses, definition dependencies, source and precise blueprint ancestry. All are unsplit with empty proof/proof_deps, null proof_origin, and no split_report. Their arguments below are research material for the next worker, not embedded proofs in their statements.

I reread the retained msearch outputs: two LeanFinder phrasings, Loogle, grep and LeanSearch per helper. Queries and statements are unchanged, so I reused the exact logged searches. Scheme.Modules.pullback concerns structure-sheaf modules; algebraic trace results do not give the pro-étale trace; Submodule.IsLattice.sup gives algebraic sums but omits the asserted basis topology; ContinuousLinearMap.range_coprod and DirectSum.range_coeLinearMap omit the continuous section and continuous-function sheaf assertion. Thus none is an exact match or a one-line specialization. The node records remain faithful to the executed queries, with no invented search. I searched the current whole DAG by tags and lattice/sum/pullback/trace notions and tools/blueprint_refs.py by lattice, trace and lattice sum; no duplicate of the four assertions was found. Pairwise distinctions from relevant existing statements are retained under Not duplicates below.

Return repair checklist: the 7686-character parent is replaced by a short assembly (2424 characters); all four substantive arguments are NEW statement-only nodes; the parent statement and Lean record are unchanged; all helper arguments/provenance/searches are retained; every parent citation is supported by a verbatim quote; no long step hides a further lemma. The latest route note is followed literally instead of repeating the earlier gate conflict.

## Preserved helper arguments for future workers

### lem-sfb-continuous-lattice-sum

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md — Pushing down by the trace: identification of the sheaf sum with the continuous module of the finite sum lattice

Proposed future proof (retained from the earlier attempt, not a split of this new node):

1. By [lem-sfb-finite-sum-lattice], choose a basis $b_1,\dots,b_r$ of $\Lambda$ and basis homeomorphisms for it and all $\Lambda_j$. For every $b_i$, choose a tuple $v_i\in\bigoplus_j\Lambda_j$ summing to $b_i$. Extend $b_i\mapsto v_i$ linearly to a right inverse $s$ of $q$. In the chosen basis homeomorphisms every component of $s$ is a finite matrix over $A$, and is continuous by its coordinate sum formula. Thus $s$ is continuous.

2. For $f:Z\to\Lambda$ continuous, the components of $s\circ f$ are continuous lifts and sum to $f$. The sum of functions into the $\Lambda_j$ takes values in $\Lambda$ and is continuous there by the subspace topology. These constructions commute with precomposition in $Z$. Hence the image equals $C(Z,\Lambda)$ already on sections, and therefore equals it after sheafification as well. The basis homeomorphism gives $C(|U|,\Lambda)\cong C(|U|,A)^r$ naturally in $U$; the basis matrix is invertible over $E$, giving the scalar-extension isomorphism for the inclusion. The construction also works for $r=0$.

### lem-sfb-finite-etale-trace-image

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md — Pushing down by the trace: definition of the trace and of its image, before asserting that the image is lisse

Proposed future proof (retained from the earlier attempt, not a split of this new node):

1. By [lem-weil-pbc-finite-etale-etale-local-split], étale neighbourhoods splitting $p$ cover $S$. On any pro-étale test scheme over a splitting, sections over the disjoint union are tuples of sections over its sheets, by the sheaf axiom for the finite disjoint open covering. Define the trace there by finite addition.

2. On an overlap of two splittings, the intersection of a sheet from one with a sheet from the other is open and closed. These intersections partition each sheet and identify the two indexing sets locally by a permutation. Addition is invariant under permutations, so the two sum maps agree. The sheaf axiom glues them uniquely to a trace. Each sum is linear over the coefficient ring, hence so is the glued map.

3. A section is in $N$ exactly when it locally has a trace expression. Restrictions preserve these expressions; expressions glue locally. After a common refinement, a sum or an $A_S$-multiple of two expressions is the trace of the sum or multiple of their lifts, so $N$ is an integral submodule. On a splitting, a trace expression is exactly a finite sum of sections of the $M_j$. Taking local expressions on both sides proves the equality of submodule sheaves. The empty sheet set gives the zero map and zero image.

### lem-sfb-finite-sum-lattice

Source: literature/stacks-project/more-algebra.tex — Tag 0AUW (more-algebra-lemma-dedekind-torsion-free-flat), part (3); topology calculation expanded from the blueprint trace paragraph

Proposed future proof (retained from the earlier attempt, not a split of this new node):

1. The union of the finitely many specified bases generates $\Lambda$ over $A$, and $\Lambda$ is torsion-free as a submodule of the field vector space $E^r$. The ring $A$ is a DVR with fraction field $E$ by [lem-weil-l-adic-extension-integers-dvr]. Thus [lem-sc-dvr-fg-torsionfree-free] makes $\Lambda$ finite free.

2. Choose a finite $A$-basis $b_1,\dots,b_t$ of $\Lambda$. Any $E$-linear relation among these vectors can be multiplied by a common nonzero denominator in $A$ to become an $A$-linear relation; all coefficients then vanish. Their $E$-span is $E^r$, since $J$ is nonempty and $\Lambda$ contains any one full lattice $\Lambda_j$. Hence they are an $E$-basis and $t=r$. For its basis matrix $B\in\operatorname{GL}_r(E)$, the maps $x\mapsto Bx$ and $y\mapsto B^{-1}y$ are continuous: every coordinate is a finite sum of products by fixed scalars. Restricting them to $A^r$ and $\Lambda$ gives continuous inverse maps for the subspace topologies. Apply the identical matrix calculation to each given basis of $\Lambda_j$. When $r=0$ these are the unique maps between one-point modules.

### lem-sfb-lattice-pullback

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md — Pushing down by the trace: restriction of the universal lattice to each finite étale stratum

Proposed future proof (retained from the earlier attempt, not a split of this new node):

1. Both pullbacks are locally finite free by [lem-weil-pbc-continuous-locally-free-pullback]. Pull back a covering trivializing $M$, and use its rationalization isomorphism to give $L$ the corresponding rational basis. On these charts $i$ is the coordinate inclusion $A^r\to E^r$.

2. The canonical map comparing scalar extension and geometric pullback is defined on tensors by $b\otimes m\mapsto b\,g^*i(m)$. On the chosen charts it sends each rational basis vector to the corresponding basis vector, hence is an isomorphism. The coordinate inclusion on $Y$ is injective because $C(|U|,A)\to C(|U|,E)$ is injective, including $r=0$. These local maps agree on overlaps: each is induced by the single map $i$ and the coefficient maps, and the tensor relation $(ba)\otimes m=b\otimes(am)$ holds on both sides. Their inverse matrices agree as well. Sheaf gluing therefore gives the asserted monomorphism and rationalization isomorphism globally.

## Current validation

The required baseline dry run was run before edits, polled in one process to exit 1, and reproduced only the four old status=split rejections (plus an explicitly nonfatal existing route warning). The repaired complete dry run and push are recorded below when finished.

## Historical report retained verbatim (superseded by the current repair above)

## Worker report

Repair of the human's 2026-10-21 return: the former 7686-character proof was too coarse for Sheaf.Paper.StratifiedLattice. The sandbox supplied to this session contained only dispatcher marker files, not node files, a report, citations, or searches.jsonl. I copied the current shared-repository item and retained its exact statement, coefficient conventions, motivational example, Lean record, previous searches, and blueprint route. The baseline dry run failed only because report.md was absent. All subsequent files are in the designated sandbox. No Lean was written or compiled, no repository or launcher file was written, and no git command was run in the shared repository.

Files written under dag/nodes/sec-six-functors-basics/:

- sk-lem-stratified-lattice.json: repaired parent; same statement, seven short assembly steps, 2124 characters of proof text.
- lem-sfb-lattice-pullback.json: statement, not a Mathlib leaf; actual lattice inclusion and its scalar-extension adjoint survive arbitrary scheme pullback. Proof: 934 characters.
- lem-sfb-finite-etale-trace-image.json: statement, not a Mathlib leaf; constructs the pro-étale trace and identifies its integral image on a splitting. Proof: 1238 characters.
- lem-sfb-finite-sum-lattice.json: statement, not a Mathlib leaf; finite sum of full valuation-ring lattices, including basis topology. Proof: 1089 characters.
- lem-sfb-continuous-lattice-sum.json: statement, not a Mathlib leaf; continuous section of the sum map and resulting sheaf-image identification. Proof: 1036 characters.

The return specifically requires each extracted argument to have a proof in words, so the four new nodes are split, with full proof steps and exact dependency unions, rather than statement-only unsplit nodes. Every proof is well under 3000 characters and every individual step is below 2000. citations.json quotes the actual statements used by every parent step; helper-citations.json supplies the same evidence for the new proofs.

Attachments: none. The project's existing exists_stratified_lisse_integral_lattice in lean/Sheaf/Paper/StratifiedLattice.lean has a sorry. Searches of WeilConjectures for the blueprint tag and the lattice/trace/pullback notions found no declaration proving this item or the extracted assertions. Its Lean record is retained; this delivery adds no Lean declaration and closes no Lean sorry.

WANTED: none. Sources read: the current main-20261015 item statement, proof, unit and chapter; Bhatt–Scholze §6.8, especially Proposition 6.8.4(6), Lemma 6.8.13 and Remark 6.8.15; Stacks etale-cohomology.tex, lemma-etale-stratified-finite (03S0); etale.tex, lemma-finite-etale-etale-local (04HN); more-algebra.tex, lemma-dedekind-torsion-free-flat (0AUW), part (3). Bhatt–Scholze proves the finite-stratification lattice assertion using representations; we retain the blueprint's specified trace proof and mark its expanded arguments agent-written. No SGA route is used.

What was wrong: the existing proof had correct but bundled pullback, trace gluing, lattice topology and continuous-function image arguments. Moving the whole trace descent into the existing det-lem-stratified-lattice-trace, or citing the existing more general stratified-lattice theorem, would merely transfer that coarse argument. Instead each new node stops strictly before the parent conclusion: none produces a stratification or descends a lattice to S. The parent still assembles the cover, the strata, the trace, the simultaneous local classification, and the local freeness/rationalization conclusion.

Nothing mathematical remains unfinished in the split. Actual Lean proofs remain future stage-3 work. Server checks and delivery results are recorded below when available.

## Review by Q46

I read the baseline item against its current blueprint source, its unit's five route paragraphs and the chapter's coefficient distinction. The exact parent statement and its existing Lean record are unchanged. The new proof keeps the same cover → finite strata → trace construction; neither invariant-lattice representation theory nor an intersection-descent replacement is introduced.

For parent step 1 I opened lem-weil-pbc-finite-type-over-noetherian and lem-sc-affine-noetherian-underlying-space. The first really gives a Noetherian source over a Noetherian base; Spec k has this property since k is a field. The second supplies the topological assertion on each Noetherian affine chart. Stabilization on the finite cover is written out. The additionally cited lem-sfb-noetherian-space-compact-subsets says every subset of a Noetherian scheme is quasi-compact, so in particular X and the intersections of affine opens meet the qcqs hypothesis. This avoids leaving that compactness implication implicit.

For step 2 I read lem-weil-pbc-continuous-coefficient-realizations: it gives ring isomorphisms for totally disconnected coefficient rings and explicitly intertwines a continuous ring map. The ultrametric argument supplies that hypothesis for E and A. I checked det-prop-sfb-qlbar-colimit-x-invert-ell actually identifies the inclusion-induced coefficient map with localization. These comparisons act on the scalar laws and so transport the modules and inclusions, not merely their underlying sheaves. Step 3 uses the exact statement of lem-weil-pbc-continuous-etale-local-lattice: topological Noetherianity was proved in step 1, its source V is explicitly qcqs, ranks may vary, and rationalization is ordinary scalar extension. Injectivity of M into that extension is checked in free coordinates, including rank zero.

For step 4 I reread lem-weil-pbc-etale-stratified-finite and its Stacks 03S0 source. Both qcqs hypotheses are now in force. It gives finite étale base changes and the required constructible locally closed partition. Surjectivity is retained under base change; no unsupported factorization through a stratum is used. The new pullback lemma is applied to the actual map V×_X S→V, and keeps the original inclusion-induced scalar-extension map. Its proof uses lem-weil-pbc-continuous-locally-free-pullback precisely for local freeness of both coefficient pullbacks. In local integral bases, the given rationalization supplies the rational bases; the tensor comparison is written on generators and the balanced relation, and injectivity is checked via the actual A→E inclusion. This is valid without an extra flatness assumption on the scheme map, because these are the cartesian pro-étale coefficient modules, not structure-sheaf modules.

For step 5 and lem-sfb-finite-etale-trace-image I reread the blueprint trace paragraph and the statement of lem-weil-pbc-finite-etale-etale-local-split against Stacks 04HN. It supplies exactly the splitting neighbourhoods used, with no Noetherian or surjectivity assumption needed for trace construction. I wrote the sheet-permutation comparison on clopen intersections, uniqueness by gluing, and closure of the sheaf image under integral scalar multiplication. The existing def-weil-pbc-finite-etale-trace is on the small étale site, so it is not mis-cited as the pro-étale trace theorem. The new node constructs the pro-étale map explicitly and asserts only its image description, not the lisse-lattice conclusion.

For step 6 I opened lem-weil-pbc-lattice-sheaf-locally-constant. Its actual statement gives the constant-coset sheaf classification and sends the class of g to the embedded submodule g A^r; therefore it gives the fixed embedded lattices claimed here, not just representability. On a trivialization of L all sheets have the same rational rank. The sheet set is finite, so successive refinement simultaneously fixes all lattice classes. It is nonempty on nonempty neighbourhoods because p_S is surjective. Thus the precise hypotheses of lem-sfb-continuous-lattice-sum hold.

For lem-sfb-finite-sum-lattice I read Stacks 0AUW(3), lem-sc-dvr-fg-torsionfree-free and lem-weil-l-adic-extension-integers-dvr. The sum is finitely generated by the finite union of bases and torsion-free inside E^r; the coefficient ring is the DVR whose fraction field is E. The free basis becomes an E-basis by clearing a common denominator and using nonemptiness of J to obtain full span. I supplied the basis matrix and inverse continuity calculation instead of citing an algebraic freeness lemma for a topological conclusion. Mathlib's Submodule.IsLattice.sup (Algebra/Module/Lattice.lean:107) was inspected: it covers algebraic binary sums, not the topological assertion of this node. ZLattice theorems use discrete Z-lattices and do not specialize to valuation-ring lattices.

For lem-sfb-continuous-lattice-sum I checked that its one theorem citation supplies basis homeomorphisms for the sum AND the individual lattices. Lifting a finite basis through the sum map gives a linear section; its matrix entries lie in A, so it is continuous in exactly those topologies. Composing a continuous function with this section gives continuous lifts on every test space, naturally under restriction. This proves equality of sheaf images as submodules, not only equality of fibres. The same basis matrix gives the inclusion-induced rationalization isomorphism. The Mathlib range_coprod/direct-sum range candidates supply algebraic image equalities only and omit this continuous section and functor-of-continuous-functions conclusion. Step 7 is then the local definition of lisse and gluing of the actual inverse maps, so needs no additional non-elementary lemma.

I tested empty X (empty stratification), empty V for trace (zero sum), zero rank (unique basis and zero lattice), degree-one covers (trace identity and original image), repeated sheet lattices, rank-one lattices A and π^{-m}A (sum π^{-m}A for m≥0), and ramified E/Q_l. Nonempty J is essential only for the full-span conclusions: I kept it in both finite-sum nodes and derived it before using them. The finite-sum proof uses general DVR freeness, not an unramified or algebraically closed coefficient assumption. No scheme normality is introduced; the nodal counterexample remains in the unchanged parent statement.

I checked delivery-errors B–E with the source and cited statements open: self-contained new statements, exact blueprint ancestry/place, literal executed search records, one backslash in TeX, no hollow definitions, no claim borrowed from a cited proof rather than its statement, no hidden uncited theorem, no circular use of the parent, no clause-restatement nodes, and no route change. All four helper nodes have full proofs because that is the explicit requirement of this return. Searches were run for each via msearch.py (LeanFinder twice with changed phrasing, Loogle, grep, and LeanSearch); full outputs are retained in research-results.jsonl and recorded queries agree with searches.jsonl. None is a leaf. The source/library search results were read, including the partial algebraic matches, before making that decision.

## Not duplicates

lem-sfb-lattice-pullback vs lem-weil-pbc-continuous-locally-free-pullback: the existing statement preserves local freeness only; the new lemma proves the coefficient/tensor comparison for the specified lattice inclusion and preserves its inclusion-induced rationalization and monomorphism.
lem-sfb-finite-etale-trace-image vs def-weil-pbc-finite-etale-trace: the existing trace is an étale-site definition; the new lemma constructs the pro-étale trace and proves its integral image is the local sum, without asserting local freeness.
lem-sfb-finite-etale-trace-image vs det-lem-stratified-lattice-trace: the existing statement assumes a trace and concludes the image is a lattice and then constructs strata. The new lemma constructs the trace and describes the image for arbitrary submodules, without lisse, lattice, Noetherianity or stratification conclusions.
lem-sfb-finite-sum-lattice vs lem-sc-dvr-fg-torsionfree-free: the latter supplies algebraic freeness and is cited. The new lemma identifies the rank, rational spanning, and basis homeomorphism for the finite sum with its specified subspace topology.
lem-sfb-finite-sum-lattice vs lem-weil-pbc-pid-torsion-free-module-flat: flatness does not supply the finite-sum basis/topology assertion; the new proof does not use flatness.
lem-sfb-finite-sum-lattice vs lem-pur-twist-integral-basis: that is a finite Z_l-basis of the coefficient ring itself; here it is an A-basis/homeomorphism of a finite sum of submodules of E^r.
lem-sfb-finite-sum-lattice vs lem-sbc-root-normalization-generic-stalk-flat: the latter concerns flatness of a normalization map at stalks; it does not concern finite sums of coefficient lattices or their topology.
lem-sfb-finite-sum-lattice vs lem-pod-profinite-stable-lattice-topology: the existing statement assumes a group-stable lattice and compares its adic topology; the new assertion has no group action and gives basis homeomorphisms for a specified finite sum. It does not assert adic-topology comparison.
lem-sfb-continuous-lattice-sum vs lem-weil-pbc-continuous-lattice-intersection-split-model: the existing result describes an intersection using an image-pullback and a kernel presentation. The new result describes finite sums using a continuous section, including the continuous-function and sheaf image calculation.

## Validation and blocking gate

Local read-only comparisons confirmed the parent statement and Lean record are unchanged. All five proof dependency lists equal the unions of their step citations. The parent has 2124 proof characters; helpers have 934, 1238, 1089, and 1036; the longest individual step is 777 characters. The initial baseline dry run exited for the absent report. A subsequent srvcheck review_split exited PASS, but reported zero new nodes, so it is not evidence that the helper delivery passed.

The required complete dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q46 sk-lem-stratified-lattice --no-push`, exited 1 with four fatal preflight reasons, one for each new node: `status 'split'; a new node is unsplit or mathlib`. The server also recorded an existing off-unit route warning for det-proper-heart-bound-reduction; this was explicitly not a refusal. Nothing was pushed.

The fatal rule conflicts with this return's express instruction that the finer nodes each carry statement, source and proof in words. Their full proofs and stage-1 split status are retained for inspection; marking them unsplit or dropping those proofs would obscure the requested repair. The brief explicitly says a gate that seems wrong must be reported BLOCKED, never patched or worked around. No launcher edits, private patched copies, or bypasses were attempted. The delivery needs the maintainer/launcher to permit proved helper nodes for an authorized finer-split repair (or give an explicit supported format for those proofs), after which the prepared files can undergo the complete dry run and push.

## Retry validation — 2026-10-21

Continued the retained repair rather than regenerating the nodes or searches. Read the current worker brief, stage-1 rules, GOAL, delivery-errors B–E, the unit/chapter route, and all four retained helper statements and proofs. The required initial dry run was run to completion in a single tool session:

`python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q46 sk-lem-stratified-lattice --no-push`

It again exited 1, with exactly the four fatal reasons below; nothing was pushed:

- `new node lem-sfb-continuous-lattice-sum: status 'split'; a new node is unsplit or mathlib`
- `new node lem-sfb-finite-etale-trace-image: status 'split'; a new node is unsplit or mathlib`
- `new node lem-sfb-finite-sum-lattice: status 'split'; a new node is unsplit or mathlib`
- `new node lem-sfb-lattice-pullback: status 'split'; a new node is unsplit or mathlib`

The off-unit warning for det-proper-heart-bound-reduction remains explicitly recorded rather than refused. No later validation or delivery invocation was launched. The requested finer proofs remain intact. The blocker is still the server preflight's refusal of proved new helper nodes; the explicit repair requirement asks for those proofs, while the ordinary new-node schema accepts only unsplit or Mathlib nodes. Relabelling these proved nodes as unsplit, removing their proofs, or patching a delivery tool would bypass or undo the requested repair. No such change was made. This retry therefore reports BLOCKED with the concrete server diagnostic; it does not claim that the repair has passed preflight.

## Retained-repair retry — 2026-10-21 (current session)

Compared all five retained node files with the current read-only repository. The four helper ids are still absent there. The parent's only changed fields are proof, proof_deps and split_report; its statement, source, Lean record, previous searches and other metadata remain unchanged. Read the retained report and helper proofs and the current blueprint proof/detail texts. The existing Lean theorem in lean/Sheaf/Paper/StratifiedLattice.lean still ends in sorry, so it is not an attachment.

As required for an existing split/report, ran the dry run before changing any node:

`python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q46 sk-lem-stratified-lattice --no-push`

Polled its single process (session 54145) until it exited 1. Server preflight was admitted in slot 1. It again refused precisely these four nodes:

- lem-sfb-continuous-lattice-sum: status 'split'; a new node is unsplit or mathlib
- lem-sfb-finite-etale-trace-image: status 'split'; a new node is unsplit or mathlib
- lem-sfb-finite-sum-lattice: status 'split'; a new node is unsplit or mathlib
- lem-sfb-lattice-pullback: status 'split'; a new node is unsplit or mathlib

The existing det-proper-heart-bound-reduction route warning was recorded but expressly not refused. No push was attempted, no second delivery process was started, and no searches were repeated. The requested proved helper nodes are retained unchanged. The blocking rule has not changed since the previous retry: it cannot accept the human-required finer split in its current schema. Following the brief's instruction to report a faulty gate rather than patch or work around it, this session reports BLOCKED. The only write in this session is this sandbox report entry.


## Validation repair after the first edited dry run

The complete dry run exited 1 because populating the required unit realizations exposed its declared coefficient-heart edge: “units: sk-lem-stratified-lattice cites sk-lem-coefficient-heart, which its nodes do not reach”. I repaired the mathematical use, rather than removing the realization record: step 4 now explicitly uses part (2) of det-lem-coefficient-heart-common-stratification to restrict the rational lisse module to the locally closed stratum. I opened that statement, verified the ambient X is Noetherian and coefficients are E, and checked it has no dependency path back to the parent. It says precisely that a lisse module restricts to a lisse module on a locally closed subset; apply it with its initial S=X and T the chosen stratum. This is the coefficient-heart tool named by the unit's original trace detail. The literal part-(2) quote is added to citations.json and the realization and tool-use records describe the same use. The proof stays below 3000 characters; no new helper or search was required.

## Successful repaired dry run — 2026-10-21

The final required no-push invocation was polled as a single process to exit 0. Server preflight printed: `OK (not pushed) deliver/Q46/sk-lem-stratified-lattice at 027d57a5b86: preflight passed`, and saved the durable stage-1 receipt. This validates the four statement-only helper nodes, parent assembly, unit realization and literal citations. Delivery is now being invoked through the required unmodified tool.

## Resumed delivery verification — 2026-10-21

Continued the prepared statement-only repair after reading its historical report and executed search records; no searches were invented or repeated. Compared the five node files against current main: the four helper ids remain new, and the parent differs only in proof, proof_deps and split_report. Read all fourteen cited statements and checked that citations.json covers every (step, node) pair with a literal substring. Rechecked the current seven-step source proof against the extraction: base-change compatibility is in lem-sfb-lattice-pullback; trace construction and the integral image calculation are in lem-sfb-finite-etale-trace-image; finite-sum freeness, rank and basis topology are in lem-sfb-finite-sum-lattice; the continuous section and continuous-function sheaf image are in lem-sfb-continuous-lattice-sum. The remaining assembly has 2424 characters. The earlier detailed arguments remain in this report for future workers.

The prescribed initial dry run completed with exit 0: `OK (not pushed) deliver/Q46/sk-lem-stratified-lattice at 6885a38f2dc: preflight passed`. The tagged project theorem still contains sorry; the WeilConjectures search supplies no exact finished attachment. No node changes were needed beyond the substantive repair already retained in the sandbox. Proceeding with the required delivery command after that dry run exited.
