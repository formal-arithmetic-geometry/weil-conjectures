## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-ultrametric-best-approximation.json`: unchanged mathematical statement, six-step compact-ball proof, status split; added the existing finite-dimensional-subspace definition to statement dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-dimensional-normed-proper.json`: statement, Mathlib leaf `FiniteDimensional.proper`, `Mathlib/Analysis/Normed/Module/FiniteDimension.lean:553` (hypotheses at 546–547, proof through 556).
- `dag/nodes/sec-six-functors-basics/lem-sfb-compact-real-function-minimum.json`: statement, Mathlib leaf `IsCompact.exists_isMinOn`, `Mathlib/Topology/Order/Compact.lean:230` (through 235), specialized to real-valued functions.

The sandbox also contains `citations.json`, the original search-command log `searches.jsonl`, and the local authoring script. The delivery comprises only the node files and this report, as packaged by the prescribed tool.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id, nearest/best approximation, finite ultrametric spaces, `exists_isMinOn`, and finite-dimensional properness. The scalar properness applications in `NumberTheory/Padics/Extension.lean` and `SixFunctors/ProEtale/Adic/LisseCover/Congruence.lean` do not state the item. Also checked the relevant `lean/Sheaf/` directories. No project declaration supplies the nearest-point theorem and its positivity clause.

## Literature and wanted sources

No WANTED source is required for this split. Read the entire current blueprint proof `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, its paragraph (3), and the chapter/unit records. The paragraph discusses proper/open direct images, not ultrametric approximation. The analytic argument is explicitly marked agent-written, not attributed to that paragraph. Its only non-elementary inputs are the existing scalar-properness leaf and the two Mathlib statements whose full hypotheses and source proofs were read. No Stacks tag or external functional-analysis theorem is asserted as a source; no SGA source is used.

## Corrections and findings

The imported statement is true as written; it was not weakened or strengthened. The title's reference to discrete valuation is more restrictive than necessary for the proof: local compactness of the coefficient field suffices, and the values of the vector norm need not lie in the value group of the field. This distinction matters: trying to round the distance infimum merely by discreteness of scalar values would leave a gap.

The inherited `blueprint.from.node` was null, and `tools/blueprint_refs.py ancestor lem-sfb-finite-ultrametric-best-approximation` likewise printed None. Traced every `created.item` and `blueprint.from.via` link. The chain reaches `lem-sfb-admissible-direct-image`, whose explicit `blueprint.from.node` is `det-thm-sf-ctf-stability-direct-images`; that node exists and is imported (`blueprint.is` equals its id). The first dry run rejected using that explicit ancestor: its ancestry resolver computes None from the inherited chain. In accordance with the required blueprint_refs.py output and its preflight diagnostic, retained blueprint.from.node=null for this item and both new leaves. The actual older blueprint association is reported here and described by from.place; no unrelated node or tool was changed. Kept the inherited intermediate via list and prepended the item for its children. The blueprint source place now says that this is an agent analytic expansion supporting paragraph (3), rather than pretending that the paragraph contains an orthogonal-basis proof.

No unit or chapter file was changed. This item is not a unit key statement. The existing scalar-properness node is a Mathlib leaf, so it is a permitted generic tool independently of its unit.

## Not duplicates

lem-sfb-finite-dimensional-normed-proper vs lem-weil-l-adic-extension-proper: despite the latter's broad title, its statement only proves properness of the coefficient field E itself, as a finite extension of Q_l. It does not quantify over a normed E-vector space W with an arbitrary vector norm. The new generic Mathlib leaf supplies exactly that additional quantified vector-space case over any locally compact nontrivially normed field; its use with K=E and Y=W is not a specialization of the old node's statement.

lem-sfb-finite-dimensional-normed-proper vs lem-cbc-euclidean-sphere-compact: that node states compactness of spheres in finite-dimensional real normed spaces. The new leaf concerns all closed balls over arbitrary locally compact nontrivially normed fields, including E, which has no compatible real scalar structure.

Searched every DAG statement for proper metric spaces, finite-dimensional normed spaces, nearest points, minima of compact sets, and the two exact Mathlib names. Read the scalar-properness node and its coefficient-definition dependencies. Whole-blueprint searches included best approximation, locally compact, finite-dimensional normed, compact minimum, extreme value, continuous real, compact continuous, and normed. The new minimum theorem had no existing node or blueprint match. The two new nodes are independent supporting tools, not reformulations of the item's existence or positivity clauses. Both are Mathlib leaves with empty proof and proof_deps, not new unsplit obligations.

## Review by NH

I checked the current source paragraph and both Mathlib files open beside the item and new node statements. `FiniteDimensional.proper` has a locally compact, nontrivially normed scalar field, a normed additive group and normed scalar action, and finite-dimensionality. It does not assume completeness of the vector space; our new leaf preserves all these hypotheses. Its notion ProperSpace is compactness of every metric closed ball. `IsCompact.exists_isMinOn` assumes a nonempty compact domain subset and continuity on that subset; specializing its ordered codomain to the reals gives exactly the second leaf, with no metric or completeness requirement on its domain. The new nodes introduce their own objects and have no proof sketch inside the statements. Their nontrivial norm and finite-dimensional notions are given inline or by their existing definition nodes. No Stacks source is involved, so there are no omitted Stacks-tag duplicate pairs.

Step 1 takes only properness of the coefficient field from `lem-weil-l-adic-extension-proper`. I read its complete statement, not merely the general-sounding title. The item has exactly its finite field extension and extending norm, so the application is valid. A closed unit ball is a compact neighbourhood since it contains an open unit ball; the inherited absolute value restricts to the l-adic one, so |l|=1/l<1 supplies nontriviality. The ultrametric inequality implies the ordinary norm triangle inequality. These are elementary deductions from the stated hypotheses and the cited properness conclusion.

Step 2 cites only `lem-sfb-finite-dimensional-normed-proper`, with K=E and Y=W. The restricted norm is homogeneous and definite by the item's assumptions, finite-dimensionality is a hypothesis, and local compactness and nontriviality were checked in step 1. The conclusion gives compactness of C, a closed ball in W itself. It never asserts that the possibly infinite-dimensional ambient V is proper or complete. Zero belongs to C because r=||x|| is nonnegative, so the nonemptiness hypothesis needed later is explicit.

Step 3 has no hidden continuity theorem: the two written triangle inequalities prove the 1-Lipschitz inequality for w ↦ ||x-w|| on the metric subspace W, which gives continuity directly. Step 4 cites `lem-sfb-compact-real-function-minimum` and uses exactly its minimum inequality, with the nonempty compact set from step 2 and continuity from step 3. The citation quotes the entire real-valued minimum statement verbatim. Inserting w=0 gives the comparison f(w0)≤r.

Step 5 proves, rather than cites, the ultrametric exclusion: ||w||>r and the two displayed max inequalities force f(w)=||w||>r outside C. This proves global minimality from the minimum on C. Step 6 is the defining infimum property of a minimum, with the set explicitly nonempty and bounded below; definiteness and w0∈W give strict positivity if x∉W. Thus no separate finite-dimensional closedness or spherical-completeness lemma is smuggled into the positivity clause. All cited uses have full verbatim statement quotes in citations.json. No proof step exceeds 2000 characters.

Tested W=0 (unique candidate zero), x=0 (C={0}), x∈W (x belongs to C and the minimum is zero), a one-dimensional subspace with nonunique closest points, and an incomplete ambient ultrametric space (only its finite-dimensional W needs compact balls). None needs uniqueness or a value-group constraint on ||V||. For both new leaves checked dimension zero and negative-radius/zero-radius balls; the empty-ball case is compact and the minimum theorem retains its essential nonempty-domain hypothesis. Checked C1–C8 for missing or mismatched citations and circularity, D1–D5 for restatements and omitted arguments, and E1–E7 for hypotheses, objects and false inferences. No new node depends on the item; proof_deps is exactly the union of step uses. The corrections made during this review were documenting the inherited null ancestry and the explicit out-of-ball max-inequality argument, in place of an unsupported appeal to discrete norm values. The first preflight also required a definition citation in the minimum leaf. I read def-kun-subspace-topology and added its precise induced-topology citation; compactness is now explicitly defined by finite subcovers, and continuity on C is the continuity of the restriction. This is the same extreme-value statement and the same searches remain applicable.

## Unfinished work

None in the stage-1 split. Both new nodes terminate in verified Mathlib matches; no new unsplit analytic lemma is left.

## Dry-run repairs

The first preflight returned exactly three metadata points: the minimum leaf needed a definition-node citation, and each new leaf's from.node had to equal the resolver's None. Added the existing subspace-topology definition to the minimum statement and stmt_deps, defined compactness inline, regenerated the verbatim step-4 quote, and conformed both new leaves and the item to the required inherited null ancestor. The mathematics, proof route, search queries and Mathlib matches are unchanged. No script was edited or bypassed.
