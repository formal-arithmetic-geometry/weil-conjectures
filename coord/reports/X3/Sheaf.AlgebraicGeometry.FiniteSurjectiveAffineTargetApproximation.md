## What changed

Proved `AlgebraicGeometry.exists_noetherian_affine_factor` in
`Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetApproximation`, keeping its signature,
`NoetherianAffineFactor`, and all public imports unchanged. Two proved private helpers organize
terminal-object pullback compatibility and the finite-presentation case. The proof implements
all eight approximation steps: qcqs target, integral approximation, affine finite-presentation
stage, absolute Noetherian approximation, spreading out, finite and surjective descent, affine
source descent, and a common upper bound. It never assumes the target is affine.

Added the proof import `Mathlib.CategoryTheory.Presentable.Directed` for reindexing the
Noetherian approximation. Updated the existing node's proof, proof dependencies, and proof
origin to describe the actual Over-category tail and Mathlib affine-projection argument.
The blueprint unit's statement and steps are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_noetherian_affine_factor`
(node `lem-weil-pbc-finite-surjective-affine-target-approximation`).

No `sorry` remains in the delivered module. No holes or new public statements were added.
The private helpers `property_over_pullback_terminal` and `factor_of_finitePresentation` are
proved, not split-off obligations. This is a proof from existing library declarations, not a
new decomposition. Single-file compilation through `lcompile.py` passes without warnings.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.LimitAffineTransition` and proof dependency
`lem-weil-pbc-limit-affine-transition`. General existence of affine-transition limits, their
relative-spectrum construction, and the affine-spectrum comparison are not needed by this
proof: the integral and Noetherian approximations already provide their limit cones, and
`isLimitBaseChangeCone` provides the source-model cone. The affine projection follows directly
from Mathlib `isAffineHom_π_app`, recorded by existing leaf
`lem-weil-pbc-limit-cone-affine-projections-opens`.

This prunes that module from this item's direct proof imports; no claim is made that it is
unreachable from other target branches. All other existing proof imports are used. No other
planned nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The recorded finite approximation is cofiltered rather than
literally indexed by a directed order; Mathlib affine-stage descent handles it directly.
The Noetherian approximation is reindexed by a directed order for the two descent lemmas.
Their Over-morphism convention requires an elementary target-isomorphism comparison with
the ordinary pullback projection. The original last step unnecessarily imported the general
limit-existence theorem when only affineness of a supplied limit projection is needed.

All data assembled in the final existential proof come from the existing approximation and
pullback constructions. No definition chooses arbitrary data from an unproved existence theorem.

## Second reading by X3

1. **Visible interface: PASS.** Compared the complete delivered module with the repository
   using `diff -u`. The existing theorem signature and the complete
   `NoetherianAffineFactor` structure are byte-for-byte unchanged; all public imports and
   visibility are unchanged. Only a proof import is added, a proof import removed, two
   proved private helpers added, and the original proof filled. No change record is needed.
2. **Proof and axioms: PASS.** Independently compiled the delivered file with `lcompile.py`
   (3.2 seconds, no errors or warnings). Compiled a scratch copy printing axioms of both
   private helpers and `AlgebraicGeometry.exists_noetherian_affine_factor`: each uses only
   `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. Scanned the delivery for
   holes and forbidden declarations: none. Approximation witnesses are eliminated inside
   theorem proofs; no definition chooses data from an unproved existence statement.
3. **Split-off statements: PASS (none).** There are no added holes or public statements.
   Checked the private pullback comparison by the isomorphism of the terminal-object
   pullback with its base, and checked the finite-presentation helper against the actual
   spreading-out and descent signatures. Empty schemes cause no exception: approximation
   indices are nonempty, and common bounds use only directedness. Identity morphisms and
   one-stage diagrams satisfy the same pullback comparisons.
4. **Route and pruning: PASS.** Read the existing integral finite-presentation approximation,
   Noetherian approximation, spreading-out, finite descent, surjective descent, and base-change
   limit declarations. The proof uses them from the target downward, preserves all eight
   mathematical steps, and does not assume the target affine. An independent Lean Finder
   search for “affineness descends along a finite surjective scheme morphism” and repository
   searches found no shorter applicable result; the downstream affine-target theorem would
   be circular. The unit `sk-thm-p1` and its `realized` routes remain unchanged. Every proof
   import retained has a use; the sole removed old dependency is completely listed in
   `## No longer needed`. The original theorem docstring still names the old general
   limit node in its final explanatory step; the updated DAG and report record the precise
   Mathlib affine-projection replacement.
5. **DAG agreement: PASS.** The only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`. Checked that `proof_deps` is exactly the union of the steps' `uses`.
   The sole removed node is `lem-weil-pbc-limit-affine-transition`, replaced by the existing
   Mathlib leaf `lem-weil-pbc-limit-cone-affine-projections-opens`, whose recorded declaration
   is exactly `isAffineHom_π_app` used in the proof. The remaining steps agree with the
   reindexing, Over-category base changes, and final common upper bound in Lean.

Second reading changed only this report, adding independent verification and the docstring
citation observation. No repair to the Lean proof or node was necessary. One original hole
closed, zero holes added, zero split off.
