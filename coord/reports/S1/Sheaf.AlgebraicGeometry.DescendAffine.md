## What changed

Proved `AlgebraicGeometry.exists_isAffineHom_baseChange_of_isLimit` in
`Sheaf.AlgebraicGeometry.DescendAffine`, with its signature unchanged. A proved private
upper-tail equivalence lets the source library's `isLimitBaseChangeCone` supply the
limit of Xᵢ. The composite X → Y₀ is affine because both X → Y and Y → Y₀ are affine.
Apply `AlgebraicGeometry.eventually_affine` to the Xᵢ over the fixed base Y₀; cancel the
affine projection Yᵢ → Y₀ using `IsAffineHom.comp_iff` to get the required fᵢ.
Added one proof-only import, `Sheaf.AlgebraicGeometry.EventuallyAffine`. Replaced the
unused public `LimitAffineTransition` import with its Mathlib statement import.
Updated the existing DAG node's proof, proof_deps and proof_origin to this route.
The import change is recorded in `coord/changes/descend-affine-import-pruning.md`.
The unit's realized nodes do not include the pruned helper, so the unit route is kept.

Local compilation is clean. Searches: LeanFinder for affine-composition cancellation,
Loogle for `AlgebraicGeometry.IsAffineHom.comp_iff`, and grep all found Mathlib's
`IsAffineHom.comp_iff` in Morphisms/Separated.lean. The library search also found the
existing `EventuallyAffine` module and source base-change-limit construction. Import
cycle checking permits the new import. The upper tail is inhabited by i₀; empty
schemes require no special assumption.

Repair of the returned landing: the previous review passed, but the landing command
failed before merging because a connection-reset message was parsed as command
arguments. Rechecked the existing proof against the current library and retained its
statement and proof route. The repair uses `deliver3.py --no-push` to rebuild the
delivery commit on the latest `origin/sheaf-dag`, compile locally and on the server,
and rerun the stage-3 preflight. The old delivery commit is not reused. No push is
performed by this worker; the second reader handles delivery.

## Proved and sorry left

Closed the single original sorry:
`AlgebraicGeometry.exists_isAffineHom_baseChange_of_isLimit`
(node `lem-weil-pbc-descend-affine`). No sorry remains in the delivered Lean file,
and no new theorem with sorry was added. The existing imported theorem
`AlgebraicGeometry.eventually_affine` (node `lem-weil-pbc-eventually-affine`)
still contains sorry and becomes the remaining proof obligation on this route.
Thus this is a complete Lean reduction to an existing stated node, not an
axiom-free completion of its transitive closure.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.LimitAffineTransition` (replaced by its
Mathlib statement import). Its existence theorem and affine comparison are not used.
The node `lem-weil-pbc-limit-affine-transition` remains a statement dependency of the
original node but its Sheaf module is no longer a direct import of this module.

Removed direct proof dependencies: `lem-weil-pbc-limit-affine-transition`,
`def-pc-scheme`, `def-weil-pbc-scheme-conventions`,
`lem-weil-pbc-cartesian-square-pasting`,
`lem-weil-pbc-open-preimage-fibre-product`, `lem-weil-pbc-qcqs-over-affine`, and
`lem-weil-pbc-limit-affine-stage`. The latter three are still part of the stated
proof of `eventually_affine`; this delivery does not claim they leave the global
closure. The scheme/convention definition nodes formerly listed as proof dependencies
remain implicit mathematical vocabulary and original statement dependencies where
applicable; there is no separate appeal to them in the Lean proof.

Kept direct tools: scheme-over-limit, affine permanence, qcqs permanence, affine limit
projections, and the affine-local-target criterion (encapsulated in Mathlib's affine
cancellation theorem). No unit-level node or route was bypassed. No other import was
removed; the source-library import supplies the base-change diagram and cone.

## Where the brief, the DAG or earlier work was wrong

The return identified a transport/landing-command failure, not a Lean or review
failure. The requested repair is a fresh delivery based on current `sheaf-dag` with
server compilation, rather than an unchanged re-push of the old commit.

No statement error found. The original six-step proof plan is valid but unnecessarily
repeats the finite-cover argument already packaged by the existing fixed-target
`eventually_affine` theorem. The replacement route uses that existing node, rather
than introducing a second statement of the missing geometry. The original theorem
docstring retains its source proof plan; the updated DAG and proof comments explain
the implemented route.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module against the repository version. The theorem signature and all existing declarations are byte for byte unchanged; only the proof and imports changed, as recorded in `coord/changes/descend-affine-import-pruning.md`.
2. Compiled `DescendAffine.lean` locally successfully. The file has no `sorry`, axioms, unsafe declarations, or hollow definitions; the remaining imported `eventually_affine` theorem is the named open dependency.
3. Checked the implemented route against Mathlib and library searches. No split-off theorem was added, and the proof uses the existing fixed-target theorem plus Mathlib affine cancellation, so no duplicate statement was introduced.
4. The proof follows the unit route through the base-change limit cone and fixed-target eventual affineness; the shorter packaged theorem is used only below the unit level. The removed `LimitAffineTransition` export is unused by downstream declarations, and the report lists the pruned direct dependencies.
5. The DAG node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof and its source. The theorem remains exactly the original target statement.

Changed only the report by adding this second-reading record; no further code repair was needed.


## Second reading by S1

1. **Visible declarations — PASS.** Independently diffed the delivered module against
   the repository. The existing theorem signature is byte for byte identical; its
   docstring, namespace, universe and attributes are unchanged. The only new declaration
   is the private, fully constructed upper-tail equivalence. The public import change
   is declared in `coord/changes/descend-affine-import-pruning.md`; no statement or
   public definition changed.
2. **Proof and axioms — PASS as a reduction.** Local compilation of the delivered file
   passed without warnings. A scratch copy with `#print axioms` reports only `propext`,
   `Classical.choice`, `Quot.sound` for the private equivalence, and these plus `sorryAx`
   for the theorem. The latter is expected from the existing open `eventually_affine`
   dependency, explicitly listed above. The delivered file has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, or kernel-check bypass. Its private
   definition has explicit data and proved laws, and never enters a public signature
   or a public definition.
3. **Split statements and shorter tools — PASS.** No split-off statement or new open
   node was added. Independently searched the library for eventual affineness and
   descent, and Mathlib through LeanFinder, Loogle and grep. The valid Loogle name
   search confirms `IsAffineHom.comp_iff`; LeanFinder returns the absolute affine-stage
   theorem and limit-projection tools, rather than a shorter fixed-target morphism
   theorem. Read the source definitions of `baseChangeDiagram`, `baseChangeCone`,
   `isLimitBaseChangeCone`, and their affine and qcqs instances. The upper tail contains
   the chosen index and is directed even for a preorder without antisymmetry; empty
   schemes and a singleton indexing preorder need no extra assumptions. Affine
   cancellation uses precisely the affine projection already established in the proof.
4. **Pruning and unit route — PASS.** Read `dag/units/sk-thm-p1.json`'s `realized`
   statement and all four steps: none of the removed dependency nodes realizes these
   steps. The fixed-target theorem packages the local finite-cover argument below the
   unit level. All three imports are needed for the unchanged signature or the proof;
   both imports used only in the proof are plain imports. Compared the old and new
   `proof_deps` sets and made the seven removed IDs explicit under `No longer needed`.
   This prunes direct dependencies, without claiming their entire global closure is
   pruned. The removed public module's declarations are not used by downstream modules
   listed in the change record.
5. **DAG agreement — PASS.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Its four proof steps match the implemented upper-tail base-change
   limit, affineness of the limit composite, eventual affineness, and cancellation.
   The dependency list is the union of their `uses`, and the origin identifies the
   existing fixed-target theorem and the agent-written reduction. No new-node fields
   are required because there are no new nodes.

Changed only this report: completed the explicit list of removed direct proof
dependencies and recorded this independent second reading. No Lean repair was needed.
