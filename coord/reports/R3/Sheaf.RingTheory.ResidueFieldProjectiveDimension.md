## What changed

The existing target signature is byte-for-byte unchanged. Replaced the first
worker's two-component conjunction with an actual reduction: projective dimension
is bounded by depth, depth by support dimension, and Mathlib identifies the
support dimension of R with its Krull dimension. The finite-length conclusion is
proved directly using Nat.find_spec and padding the same resolution by zeros.
The first worker's Core and Finite modules and nodes were removed before delivery.
One new module, ResidueFieldProjectiveDimensionDepth, states precisely the depth
bound (steps 1-4 of the original plan). No existing definition or signature changed;
no change record is required.

## Proved and sorry left

Hole closed: `Ring.residueField_projectiveDimension_le_ringKrullDim`
(node `lem-weil-pbc-residue-field-pd-le-krull-dimension`). Its finite-dimension
conclusion is now proved without a new hole.

Hole added and remaining: `Ring.residueField_projectiveDimension_le_depth`
(node `lem-weil-pbc-residue-field-pd-le-depth`), in the new Depth module.
There are no sorries in the item's module, no other holes added, and no data
chosen from an unproved existence theorem. This is a decomposition: one old hole
closed, one new hole added, net zero in the import closure, not a complete
axiom-free proof of the target. The earlier Core/Finite holes were draft additions,
not repository holes, and are not counted as holes closed against the baseline.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.Algebra.ProjectiveDimensionWellDefined`,
`Sheaf.AlgebraicGeometry.ExactFreeComplexLastMinors`,
`Sheaf.RingTheory.Depth`, and
`Sheaf.RingTheory.MinimalFiniteFreeResolutionLocal`.
The new Depth module imports the last-minors and minimal-resolution dependencies;
the existing depth/support module supplies depth to the target proof.
ProjectiveDimensionWellDefined is replaced in the target proof by Nat.find_spec
and the elementary padding argument. Public statement imports are unchanged.
Removed both draft Core/Finite module imports; neither draft module is delivered.

Old parent proof dependencies no longer used directly by the target:
- `lem-weil-pbc-projective-dimension-well-defined`
- `def-weil-finitely-generated-module`
- `lem-weil-pbc-minimal-finite-free-resolution-local`
- `def-weil-pbc-exact-sequence`
- `def-weil-pbc-free-module`
- `def-weil-pbc-projective-module`
- `def-weil-pbc-krull-dimension-ring`
- `lem-weil-pbc-exact-free-complex-last-minors-regular-sequence`
- `def-weil-pbc-matrix-determinant`
- `def-weil-pbc-regular-sequence`
- `def-weil-pbc-depth`
- `def-weil-pbc-module-localization`

These old steps remain recorded in the new depth-bound node where needed, or are
replaced by the elementary minimum-length argument in the parent. No claim that
an existing library module becomes unreachable is made: whole-library pruning
must be measured from the targets' closure. Pruned library modules: none.

## Where the brief, the DAG or earlier work was wrong

The first draft transferred almost the entire inequality to a new Core hole and
left the easy finite-length consequence as another hole. Its new-node proofs were
only placeholders, and the parent node still described the original five-step
implementation. Replaced that draft with a narrower depth-bound component having
a complete source-based proof in words and updated both nodes to match the code.
Mathlib already has Module.supportDim_self_eq_ringKrullDim; no new support lemma
is needed. Search of leanfinder, loogle, msearch grep and lean/ found no existing
residue-field projective-dimension versus depth theorem for this definition.

## New nodes

`lem-weil-pbc-residue-field-pd-le-depth`, module
`Sheaf.RingTheory.ResidueFieldProjectiveDimensionDepth`, declaration
`Ring.residueField_projectiveDimension_le_depth`. It isolates steps 1-4 of Stacks
00OB: minimum-length minimal finite free resolution, last nonzero degree,
Buchsbaum--Eisenbud, and proper last-minor ideal producing a regular sequence.
Its natural-language proof, source, dependency union, fresh search records for all three required kinds (LeanSearch unavailable),
creation record and verbatim Lean signature are included. No change records.

## Second reading by R3

1. Compared the delivered target against the repository with diff and asserted
   literal equality of its existing signature through `:= by`. Verdict: unchanged
   hypotheses, conclusion, declaration visibility and public imports; no existing
   definitions changed. Only sandbox files were repaired.
2. Compiled both delivered files locally in import order using lcompile.py.
   Verdict: no errors or warnings. Only the named depth theorem has `sorry`, as
   its entire proof. Scanned the sources for forbidden declarations/attributes;
   none. Scratch #print axioms for both declarations gives only propext,
   Classical.choice, Quot.sound and sorryAx, the last solely reflecting the open
   depth component. The minimum resolution uses Nat.find_spec on the supplied
   hypothesis h; no arbitrary data is chosen from an unproved theorem.
3. Read the component's complete proof in words against the original Stacks
   00OB plan and the imported minimal-resolution and last-minor statements.
   Verdict: true and a proper subargument, with the dimension/support step and
   finite-length construction genuinely implemented above it. Checked n=0
   (nonnegative depth), fields (pd=depth=0), infinite depth (automatic bound),
   positive last rank (all minors in the maximal ideal), and the impossibility
   of zero residue field for a local ring. Fresh leanfinder, loogle and grep
   searches found no duplicate depth bound in Mathlib or lean/; Mathlib's support
   identity is used directly. Removed the draft finite clause's unnecessary hole.
4. Read from the parent downwards and minimized imports. Verdict: target uses
   the existing proved depth/support theorem and Mathlib support identity, then
   elementary minimum-length padding. The remaining depth subargument follows
   the existing stated minimal-resolution and last-minor dependencies. Reviewed
   dag/units/sk-thm-p1.json realized: this subsidiary node is not itself a unit
   realization, and no unit-level statement or step is bypassed. All old parent
   proof dependencies removed from its direct route are listed above; dependencies
   still required by the depth subargument remain in that node.
5. Checked parent and new-node proof/proof_deps/proof_origin, source, creation,
   statement dependencies and verbatim Lean statement. Verdict: records match
   the implemented reduction and the remaining source-based proof plan; each
   proof_deps list is the union of the step uses. No unit records changed.

LeanSearch was also attempted for the required third search category; it returned
Internal Server Error and is recorded as unavailable, without a no-match verdict.
The other search services and local source searches succeeded.

Changes made in second reading: removed the draft Core/Finite components;
introduced the narrower depth component; proved the support/dimension comparison
and finite-resolution padding in the target; pruned direct proof imports; wrote
complete new-node metadata and updated the parent route; corrected progress
accounting to a decomposition with net zero holes.
