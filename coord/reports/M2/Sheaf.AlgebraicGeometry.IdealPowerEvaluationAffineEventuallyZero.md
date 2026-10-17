## What changed

Repaired the duplicate-helper return in
`Sheaf.AlgebraicGeometry.IdealPowerEvaluationAffineEventuallyZero`.
Removed `Modules.local_product_qc`, `Modules.local_multiplication_range`, and
`Modules.local_powers_qc` entirely. The proof now directly imports
`WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
with `import all` and uses its existing private `Modules.multiplication_range`
and `Modules.powers_qc`. No imported module or existing signature was changed.
The retained `powers_range` induction and the restored public
`ideal_power_evaluation_affine_eventually_zero` proof compile without warnings.
Updated the item's proof metadata to match these dependencies.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.powers_range`, the one active hole in the
current repository module. Restored with its original signature and a complete proof:
`AlgebraicGeometry.Scheme.ideal_power_evaluation_affine_eventually_zero`, which the
current repository comments out after the upstream sync.

All seven declarations were checked with `#print axioms` in the delivered module;
only `propext`, `Classical.choice`, and `Quot.sound` occur.

Actual holes remaining in the delivered module: zero. Holes added: zero.
Split-offs: zero. This repair removes duplicate proofs and retains the previous
proof; it does not claim the three removed helpers as newly closed holes.

## No longer needed

Removed the retired wrapper import
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`, replacing
it with the direct source-module import above.
Removed these direct proof imports from the returned sandbox:

- `WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`

Their corresponding direct DAG dependencies are no longer needed by this item's proof:
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`,
`lem-weil-pbc-quasi-coherent-module-cokernel-closure`, and
`lem-weil-pbc-quasi-coherent-module-kernel`.
These remain indirect ingredients of the existing imported theorem; no claim is
made that they leave the targets' overall closure. The original six proof
dependencies and the unit route remain in use. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned delivery incorrectly concluded that private helpers could not be reused.
`import all` of the retired Sheaf wrapper exposes only that wrapper's declarations;
it does not expose the source module's private helpers. A direct `import all` of
`WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
exposes both existing helpers. This was checked explicitly with `#check` and by
compiling the final proof. Reproving those helpers was unnecessary and caused
the duplicate-statement rejection. The returned DAG step describing those local
proofs has been replaced with the direct reuse route. No new nodes, statement
changes, definition changes, or forced consumer adaptations are needed.

## Second reading by M2

1. **Signatures and accidental changes — pass.** I compared the delivered module
with the repository version. The existing `powers_range` signature is unchanged,
and the restored `ideal_power_evaluation_affine_eventually_zero` signature is
byte-for-byte the signature recorded in its node. The only interface import change
is the proof-only import from the retired Sheaf wrapper to the source module; no
existing declaration in another module was edited.

2. **Compilation and axioms — pass.** The module compiles with
`python3 /home/ubuntu/weil-launcher/lcompile.py`. A scratch compilation with
`#print axioms` for all seven declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`,
`opaque`, `extern`, or `implemented_by` declarations.

3. **Statements and split-offs — pass.** No new statement or split-off was added.
The affine theorem is the original target statement, including all hypotheses and
the unrestricted affine-open conclusion. The proof reuses the existing source
declarations `Modules.multiplication_range` and `Modules.powers_qc`; it does not
duplicate them or weaken the target.

4. **Pruning and route — pass.** The proof follows the node's five-step route:
recursive power-range induction, finite affine sections, stalk/basic-open
vanishing, radical-annihilator containment, and affine sheaf hom extensionality.
The unit `sk-thm-p1` route is retained. The retired wrapper and the duplicate local
helper route are removed; the direct source import is the shortest available proof
dependency.

5. **DAG agreement — pass.** The node's proof text and `proof_origin` describe the
direct source-module reuse and the `powers_range` induction used by the Lean proof.
Its six proof dependencies remain the declarations actually used (directly or via
their imported helper modules), and no new node or change record is required.

Changed during second reading: no Lean proof or statement changes; only this review
record was added after compilation, signature comparison, and the axioms check.
