# Stage-1 report: lem-coef-symmetric-family-block-assembly

## Files written

- `dag/nodes/sec-six-functors/lem-coef-symmetric-family-block-assembly.json`: statement split into seven steps; Mathlib verdict no match; no statement change.
- `citations.json`: verbatim statement excerpts for every step/node citation.
- `searches.jsonl`: retained the eight interrupted-attempt searches and appended one source-location search through msearch.

No new nodes or Mathlib leaves.

## Attachments

None. The project-source searches for the item id, symmetric families and block assembly found no declaration stating the assertion. The only broad block-assembly text hit was an unrelated abelian-variety overview. No upstream sorry declaration was counted as a proof.

## WANTED

WANTED: Lurie, *Higher Algebra*, Definition 2.3.2.10 and proof of Theorem 3.1.2.3(1), printed pp.253–254 and 336–337, for this item; Corollary 2.2.4.5 and Remark 2.2.4.6 for its existing concatenation dependency. I inspected the [online September 2017 edition](https://people.math.harvard.edu/~lurie/papers/HA.pdf); it is not archived in literature/.

WANTED: archived copies of the existing dependencies' sources: [Kerodon 018F](https://kerodon.net/tag/018F), [01DK](https://kerodon.net/tag/01DK), [00ZP](https://kerodon.net/tag/00ZP), and HTT Theorem 2.2.1.2 with its coherent mapping-bifunctor compatibilities, for right slices, pointwise equivalences, contractible homotopy fibers and space-valued transport. These sources belong to existing dependency nodes, not new children. Their precise statements were read in the DAG. Online Kerodon 018F, 01DK, 00ZP and the transport discussion 05R5/02HU were also inspected; the full coherent transport theorem is cited as the existing node's assertion, not inferred from Kerodon's homotopy-category statement alone.

## What was wrong or incomplete

The imported item had no proof, proof dependencies, origin or split report. Its mathematical statement remains unchanged. The interrupted sandbox already contained five steps, citations and eight logged Mathlib searches. I first ran its required dry run; it exited successfully at f353ba08eb. I retained its relative Segal argument and searches, then repaired two mathematical gaps before final delivery: the fourth step's expression `a p_j` was ill-typed, and objectwise contractibility alone had been asserted to give all coherent functor data. The new steps use a transformation of contravariant space diagrams, the existing pointwise-equivalence theorem, and existing right-fibration transport to supply that coherence. Contractibility now cites the existing homotopy-fiber criterion explicitly.

The current repository still has the item unsplit. Its statement, source, ancestry, chapter and unit match the sandbox. I read both the current main-20261015 ancestor file (which has no proof paragraph) and the older master ancestor with its second mapping-complex paragraph. The inherited ancestry refers to that historical paragraph and is preserved, rather than attributing an absent proof to the current main file. The fixed chapter and the inherited sk-prop-sf-biduality-general unit were read; no route or binding was changed.

Whole-DAG searches for block assembly and the related Segal descriptions found the item, its sibling block-restriction lemma, inert-active orthogonality, and its parent active-slice-calculus lemma. The parent depends on this item and was not cited. Blueprint searches for block assembly and Segal found no duplicate blueprint statement. All newly used tools already exist, and dependency traversal confirmed none reaches this item. No new node was needed.

The eight retained Mathlib searches comprise LeanFinder, Loogle, grep and LeanSearch in two phrasings. I read their logged hits; they concern ordinary categories, strict Segal sets, and triangulated triangles. The added logged grep located the StrictSegal source documentation and its explicit ordinary-category nerve examples; these do not state the relative operadic assertion. No unavailable search was called a negative result.

## What I could not finish

Nothing remains in this stage-1 split. No Lean was written, no compiler or Lake command was run, and no live source, launcher or shared repository file was edited.

## Review by Q104

I checked B–E of delivery-errors.md against the statement, all seven proof steps and each cited node's statement. There are no new statement-only nodes to check for B1, no moved clause or whole-item helper (D1/D2), and no additional hypotheses. The proof is marked agent-written because its expansion is mine, even though the relevant HA passage was inspected online. The source's output-product comparison is the intended route; no SGA source is used.

Step 1 fixes the given concatenation and stationary projections, defines each block's fold map, and checks the actual pointed-map equation rho_j alpha = kappa_j q_j. Its elementary content is this calculation and the identity parameter coordinates. Its cited family definition says what inert means, and concatenation's statement explicitly includes finite tuples and the empty unit.

Step 2 uses exactly the mapping-space homotopy-pullback square in def-coef-symmetric-operadic-family. The chosen target projections are inert at parameter t; the source is in parameter zero. Taking a fiber over a specified arrow in the discrete base yields the displayed product. The proof no longer confuses the whole base mapping space with the selected arrow. Step 3 takes the homotopy fiber over the composed component operations: lem-cbc-kan-fibration-fiber-criterion explicitly says equivalences of Kan complexes have contractible homotopy fibers, and the family definition defines the active subcategory by the pointed map. This general homotopy-fiber fact is declared as an off-unit tool in split_report.tool_uses.

Step 4 defines P, Q and R on tuples of sources. I checked that active tuple maps preserve the block-assignment map alpha and that the comparison p'_j (sum h_j) = h_j p_j is the blockwise comparison for canonical tuple concatenation. The existing space-transport statement explicitly provides the coherent mapping bifunctor, its pre/postcomposition action and compatibility with higher simplices, so this step is not relying on a definition to assert a transport theorem.

Step 5 invokes lem-coef-infinity-pointwise-equivalences only after checking every component of E by Step 2. Its statement applies to any small diagram shape, hence to C opposite, with target the infinity category of spaces. Inverting E there gives a coherent transformation R to P. The transport node states the dual right-fibration classification and its coherent mapping-space formula; the join-slice node explicitly describes simplices as maps from a join. These statements identify the total categories and the resulting functor, including triangles. All categories are small as required by the item and the fixed universe convention.

Step 6 writes out the component path with both sides mapping x to b_j, correcting the interrupted draft's ill-typed formula. It also verifies that a triangle between active arrows to a color forces its source-change map to be active, so such edges really lie over C. Higher compatibility comes from the coherent transformation just constructed and the transport statement, not from independent objectwise choices.

Step 7 checks s=0, s=1 and nullary blocks directly. The empty product is terminal, P is contractible by the zero-output family axiom, and the empty tuple is the specified unit. A block with no inputs still has an inert projection and active nullary fold, so no nonemptiness assumption was introduced. I inspected the lengths of every non-elementary step: all are below 2000 characters. Each citation quote is copied verbatim from the precise existing statement used at that step; proof_deps is exactly the union of uses.
