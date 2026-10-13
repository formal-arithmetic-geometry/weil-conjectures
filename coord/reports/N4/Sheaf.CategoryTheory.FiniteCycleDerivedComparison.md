## What changed

Completed the earlier sandbox attempt in
`lean/Sheaf/CategoryTheory/FiniteCycleDerivedComparison.lean`. The original theorem
signature, visibility, and sole public import are unchanged. Added documentation to
the private helpers and checked their completed proofs against the node's three-step
argument.

The explicit recursive `comparisonLift` uses identity transports and image
factorization maps, without choosing an arbitrary witness. `comparisonInclusion_alpha`
proves compatibility of the recursive inclusions with alpha; `comparisonAlpha_succ`
reconciles the appended and prepended iterate recurrences. These yield
`comparisonLift_inclusion`. Independently, `comparisonLift_g` proves the g equation
by induction, cancelling the monic kernel inclusion in the successor step and using
`cycleLift_comm` and `projection_succ`. Finally the public theorem cancels the supplied
monic I to identify e with the constructed lift.

The existing DAG proof and dependencies already describe this exact argument, so no
node copy or route change is needed. The unit record has no realized statement or
proof step that this argument bypasses.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.BigradedExactCouple.finiteCycle_derived_comparison`
(node `lem-sp-finite-cycle-derived-comparison`). All four private helper theorems
are proved. No sorry remains in this module; no holes or new modules were added.
This is a proof, not a decomposition into new unproved statements.

Single-file compilation through lcompile.py passed without warnings. A scratch copy
with `#print axioms` for comparisonLift, comparisonInclusion_alpha,
comparisonAlpha_succ, comparisonLift_inclusion, comparisonLift_g, and
finiteCycle_derived_comparison reports only propext, Classical.choice, and Quot.sound
for every declaration; no sorryAx occurs, including in their dependency closure.

## No longer needed

None. No imports were added or removed. The proof uses the exact-couple definitions,
DerivedMaps.alpha_comm and DerivedMaps.g_comm from `def-sp-exact-couple`, and the
cycle tower and alpha iterate from `def-sp-convergence`. These are precisely the
node's existing proof dependencies, exposed by the sole public import
`Sheaf.CategoryTheory.ExactCoupleConvergence`.

## Where the brief, the DAG or earlier work was wrong

The earlier worker left a complete compiling proof in the sandbox but did not finish
the report or delivery dry run. Its proof follows the existing node, including the
zero-page case and all endpoint transports. No statement or interface correction
was required.

Fresh LeanFinder search for the iterated derived-couple g comparison returned eight
homology/snake-lemma results, with no matching comparison theorem. Loogle confirmed
`CategoryTheory.Limits.image.fac`, which the proof uses. The launcher's grep search
for `finiteCycle_derived|alphaIter.*succ` found no Mathlib result; direct library
searches found related private iterate inductions and consumers of this theorem,
but no shorter existing theorem proving this statement.


## Second reading by N4

1. **Public interface: pass.** Read the entire repository and sandbox modules and
   compared them with diff. The sole existing declaration,
   `CategoryTheory.BigradedExactCouple.finiteCycle_derived_comparison`, has a
   byte-for-byte identical signature, checked separately with a text assertion.
   Its docstring, visibility, universes, section instances, and sole public import
   are unchanged. The other additions are private helpers and the author credit;
   no existing definition or target statement changes and no change record is needed.

2. **Proof and constructions: pass.** Compiled the delivered module through
   lcompile.py with no errors or warnings. Searched all delivered Lean source for
   sorry and the forbidden declarations/options; none occurs. Compiled a scratch
   copy with `#print axioms` for all six declarations: each uses precisely the
   permitted propext, Classical.choice, and Quot.sound, with no sorryAx.
   comparisonLift is an explicit identity/image-factorization recursion. The
   chosen DerivedMaps used by the proof agree with the existing pageCouple
   construction: alpha_comm determines alpha by monic image inclusion, f_comm
   determines f by epic cokernel projection and monic image inclusion, and g_comm
   determines g by epic factorThruImage. No arbitrary existence witness is added.

3. **Split statements and edge cases: pass.** No unproved statement is split off,
   no public helper is introduced, and no node is added. Read all four proved
   private helper statements. comparisonAlpha_succ asserts only the appended
   recurrence; comparisonInclusion_alpha and comparisonLift_inclusion prove the
   required inclusion compatibility; comparisonLift_g proves only the constructed
   lift's g equation. All are used. Their zero cases reduce to identity transports
   and projection_zero; the successor uses hgprev from Z_decreasing, not an
   extra factorization hypothesis. Checked r=0, r=1, arbitrary negative p and q,
   and the zero-category case against the displayed equations; no positivity or
   vanishing assumption is introduced.

4. **Shortest route, imports, and unit: pass.** Fresh LeanFinder query about the
   iterated connecting-map image returned eight homology-sequence results, none
   stating this comparison. Loogle with fully qualified factorThruImage and
   image.ι returned twelve image-factorization results, including image.fac
   already used here. The launcher grep search for derived comparisons, iterated
   alpha, and exact couples found only unrelated derived-functor comparisons.
   Direct searches of lean/ found consumers and related private iterate lemmas in
   FinitePageImageLift, but no public theorem giving a shorter route. Reusing that
   private iteration lemma would require an extra module for essentially the same
   induction and would not shorten the g comparison. The sole public import is
   necessary for types in the public statement. Both old proof dependencies remain
   used, so `## No longer needed` is complete. Read
   dag/units/sk-prop-av-pqf-finite.json: its realized statement and sole realized
   step are empty; this proof bypasses no realized unit node. The referenced
   literature files are absent on this machine; the reviewed source descriptions
   are those preserved in the module and node, and no new source claim is added.

5. **DAG agreement: pass.** Opened lem-sp-finite-cycle-derived-comparison and its
   two dependency nodes. Its first proof step is exactly comparisonLift,
   comparisonInclusion_alpha, comparisonAlpha_succ, comparisonLift_inclusion,
   and the final mono cancellation. Its second step is comparisonLift_g's zero
   case and hb obtained by cancelling the Z_n arrow. Its third step is hcycles,
   cancelling kernel.ι after cycleLift_comm, followed by M.g_comm and
   projection_succ with the endpoint naturality transports. The proof_deps remain
   def-sp-exact-couple and def-sp-convergence, and the agent-expansion proof_origin
   still describes this argument. No node metadata edit is required.

**Second-reading changes:** corrected the report's tentative dependency-axiom
wording to the measured standard-axiom result and appended this independent review.
No Lean proof, signature, import, definition, or DAG field required repair.
