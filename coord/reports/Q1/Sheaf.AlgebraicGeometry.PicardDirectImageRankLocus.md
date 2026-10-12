## What changed

Reduced `AlgebraicGeometry.Scheme.exists_picardDirectImageRankLocus` to rank-only
representability and canonical base-change compatibility. Its signature, the original
rank-condition definition, and all public imports are unchanged.

Added `PicardUniversalRankMatch`, the second conjunct of the existing condition, as a real
predicate in its own module. Added two theorem modules, each with one public named hole.
The first asserts representability only for the rank clause; the second proves compatibility
from that clause and asserts no representing object. Neither is a renaming of the original
full statement. The main module proves finite local freeness from the identity test in the
rank clause, using the source library open-cover locality theorem and uniqueness of left
adjoints to compare tensor pullback with ordinary pullback. It then combines the clauses,
proves the reverse implication, and gets quasi-separatedness from immersion.

Proof imports now use `PicardUniversalRankMatchLocus`, `PicardRankMatchBaseChange`, and
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`. The two geometric helper modules
retain the original perfect-direct-image and lowest-cohomology proof dependencies.
The rank-only locus also imports `ProperNormalizedFibres` for its recorded connected-fibre
step (added in the second reading).

Validation: `lcompile.py --all` compiled all four modules without warnings. The launcher
axiom probe and `deliver3.py --no-push` passed; the dry run reports OK with only the second
reading deferred to its designated reader. Nothing was pushed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.exists_picardDirectImageRankLocus`
(node `lem-sc-picard-direct-image-rank-locus`). No sorry remains in the assigned module.
This is a decomposition, not a completed geometric proof: one upper hole is closed and
two lower holes are added (net holes closed minus added: -1).

Every hole added is exactly the entire proof of a named public theorem:

- `AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus`, node
  `lem-sc-picard-universal-rank-match-locus`.
- `AlgebraicGeometry.Scheme.picardRankMatch_baseChange`, node
  `lem-sc-picard-rank-match-base-change`.

Both have source citations and complete proof descriptions in their docstrings and nodes.
`PicardUniversalRankMatch` is an explicit definition without any hole. No data is chosen
from an undetermined existence theorem: the representing scheme is only eliminated in a
proof of a proposition.

Edge cases checked against the statements: the empty test scheme has a vacuous rank clause,
its direct image and canonical maps are uniquely determined; rank zero uses a zero first
free term and the zero-to-zero map. Nonreduced tests remain quantified over, so pointwise
rank alone is never substituted for universal freeness. In the compatibility theorem no
structure-sheaf unit assumption is used: the rank of E is supplied by the rank hypothesis,
and proper flat finite presentation supplies perfectness after base change.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`
and `Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus` from the assigned module, replacing
them by the two intermediate theorem imports. These two modules and their nodes remain
needed transitively for the new statements; no whole-library pruning is claimed.
The original nodes `lem-weil-pbc-flat-lfp-open`, `lem-weil-pbc-proper-closed-image`,
`lem-pc-rf-perfect-base-change`, and `lem-sc-perfect-h0-locally-closed` are no longer direct
proof dependencies of the assigned node, but remain dependencies of the rank-only locus
and compatibility nodes. No unused dependency of the source proof has been identified.

## Where the brief, the DAG or earlier work was wrong

The original plan leaves the comparison between derived cohomology base change and the
specific ordinary adjoint-defined map implicit. The lowest-cohomology declaration gives
an object isomorphism, not by itself invertibility of that specific map. This comparison
is explicitly part of the new canonical-compatibility item. The existing perfect-direct-
image declarations also carry derived-category localization and additivity instances;
constructing these and the local degree-zero comparisons is part of the new geometric
items, not something silently inferred by this delivery.

The rank clause already implies the first finite-local-freeness conjunct, so that conjunct
needs no new hole. Its Lean proof required transporting the identity-composite test by
`congrArg`, since simplification cannot unfold the unexposed categorical limit choices.

The unit record `sk-prop-av-cube` was read. This delivery stays on the existing Tag 0BDP
rank-locus route below that unit. Whole-blueprint searches for `rank direct image`, `0BDP`,
`universal rank`, and `lowest cohomology` found no duplicate blueprint node. The ancestor
helper returned None for this stage-3-created node; the new nodes use the explicit ancestor
`thm-sc-theorem-of-cube` already recorded on the parent node.

Searches were actually run through msearch: LeanSearch returned HTTP Internal Server Error
and is recorded unavailable; LeanFinder returned general representability or unrelated
cohomology lemmas; grep returned ring/module rank lemmas, with no exact sheaf result.
Stacks Tags 0BDP, 0BDL, and 0B91 were read directly online because local literature is absent.
No definition or statement repair and no forced adaptation is made.

## New nodes

`def-sc-picard-universal-rank-match`: the explicit universal rank clause, in
`Sheaf.AlgebraicGeometry.PicardUniversalRankMatch`.

`lem-sc-picard-universal-rank-match-locus`: construct the rank-only representing immersion
from the clopen rank decomposition and the two perfect lowest-cohomology loci, in
`Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus`.

`lem-sc-picard-rank-match-base-change`: identify the canonical ordinary maps with the
scalar-extension maps on local degree-zero matrix models, in
`Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange`. This implication needs no hO.

All new node files and the updated parent proof are under
`dag/nodes/sec-abelian-varieties/`. There are no change records.

## Second reading by Q1

1. **Unchanged interface: pass.** Compared every delivered module against the read-only
   repository. Only the assigned module exists there. Its two declaration signatures,
   the entire body of `PicardDirectImageRankCondition`, and all public imports are byte
   for byte unchanged. The only old-node fields changed are `proof`, `proof_deps`, and
   `proof_origin`. There are no adaptations or statement/definition change records.
2. **Kernel proof and holes: pass as a decomposition.** Independently compiled all four
   modules with `lcompile.py --all`, without errors or warnings. Inspected all declaration
   bodies: the assigned theorem has no hole; precisely the two named geometric theorems
   listed above have whole-body `by sorry`. There is no forbidden declaration, hidden
   hole, or arbitrary data witness. A scratch `#print axioms` probe checked both predicates
   and all three theorems; only the permitted standard axioms and `sorryAx` occur.
   The upper proof uses the identity test to obtain local freeness, covers by these opens,
   transports tensor pullback to ordinary pullback by uniqueness of left adjoints, and
   combines the two genuinely separate geometric assertions.
3. **Split statements: pass.** Read the actual quantifiers and source proofs in
   [Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP),
   [Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL), and
   [Tag 0B91](https://stacks.math.columbia.edu/tag/0B91).
   Rank-only representability and canonical map invertibility are separate parts of the
   original assertion; neither has its full conclusion. Empty bases, rank zero, identity
   maps, residue-field tests, and nonreduced tests preserve the asserted implications.
   In particular the canonical-map assertion needs no structure-sheaf unit hypothesis.
   Repeated searches with different wording through LeanFinder, Loogle and grep found
   no exact result. Read the upstream `PerfectLocusOfRank` declarations: they additionally
   require vanishing of all other cohomology, and their base-change isomorphism is only
   an object isomorphism, so they cannot replace either new theorem. Neither geometric
   hole can be closed by a short existing lemma.
4. **Route and pruning: pass.** Read `sk-prop-av-cube` and its `realized` fields (currently
   empty); this delivery does not change or bypass its route. The two old geometric
   imports are removed only from the assigned module and retained in its new dependencies.
   The report's no-longer-needed list accounts for every old direct proof dependency;
   no module is pruned from the target closure. Statement imports remain public and
   proof imports private. Retained imports in holed theorem modules are their DAG plans,
   as required by the standing brief. The connected-fibre plan was missing its private
   `ProperNormalizedFibres` import; added it.
5. **DAG and proof descriptions: pass after repair.** Checked all new nodes' source,
   Lean statement, chapter/unit, creation, blueprint, and search records. Each
   `proof_deps` is precisely the union of the recorded steps' `uses`. The parent proof
   accurately describes its Lean reduction and its two new dependencies. Tightened the
   base-change theorem's docstring and node proof to specify the residue model with a
   rank-r first term, after cancelling contractible summands: the outgoing matrix
   vanishes in that chosen model, not in an arbitrary finite-free model.

Second-reading changes: one private proof-dependency import, the new base-change theorem's
proof description and matching node step, and this report. Existing statements, definitions,
and the correct Lean proof were not rewritten. The result remains one original hole closed,
two simpler holes added, net -1; it is not a completed geometric proof.
