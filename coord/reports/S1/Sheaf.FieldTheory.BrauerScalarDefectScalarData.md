## What changed

Proved `Field.exists_brauerScalarDefect_scalar_data` in
`Sheaf.FieldTheory.BrauerScalarDefectScalarData`, preserving its existing signature
byte for byte. Two proved private helpers give scalar injectivity and the elementary
conjugation cancellation. The proof uses Mathlib's `center_eq_range_scalar`, tensor
induction, open stabilizers, and scalar cancellation. The formerly duplicated private
`Field.locallyConstant_galois_eval` was removed before this second reading; its proof
is inline at the sole use site because the other module's helper is private.

Added proof-only imports `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic`
and `Mathlib.Topology.Algebra.MulAction`. Updated the existing node's proof route.
No public statement or definition changed; no change record is needed.

## Proved and sorry left

Closed the one original hole: `Field.exists_brauerScalarDefect_scalar_data`
(node `lem-sc-brauer-scalar-defect-scalar-data`). Added zero holes, split off zero
statements, and left zero `sorry`s in the delivered module. This is a proof, not a
decomposition. The axiom check reports only `propext`, `Classical.choice`, `Quot.sound`.

## No longer needed

Removed the redundant direct proof import `Sheaf.FieldTheory.GaloisUnitsCohomology`:
`Sheaf.FieldTheory.BrauerScalarDefect` already publicly imports it. Its definitions
and Krull-topology API remain available and needed, so neither its node nor its module
is pruned. Both original `proof_deps` remain used. No other modules or nodes are pruned.
The duplicated private evaluation helper is unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original report described only the duplicate-helper repair, omitting the proof
of the original hole and the removed direct import. The original node described the
mathematical argument but did not record the actual Mathlib center theorem and
local-constancy API used by the Lean proof. Both records are now corrected.

## Second reading by S1

1. Compared the entire delivered module against the repository version with `diff`.
   The sole existing public declaration's signature and docstring are byte for byte
   unchanged; no definitions or targets changed. The only new declarations are two
   private proved helpers. Verdict: pass.
2. Compiled the module with `lcompile.py` without errors or warnings. A scratch copy
   with `#print axioms Field.exists_brauerScalarDefect_scalar_data` reports only the
   three permitted axioms. No `sorry`, forbidden declaration, or data definition is
   present. The scalar choice comes from a proved existence argument and is unique
   by scalar injectivity. Verdict: pass.
3. There are no split-off statements or new nodes. Checked both private helpers:
   n ≠ 0 supplies the diagonal entry (including n = 1), and conjugation cancellation
   works in any monoid for units. The argument does not require normalized b(1).
   Searched the library and Mathlib for evaluation/local-constancy and scalar
   injectivity facts. Mathlib's central-scalar theorem is already used; the existing
   evaluation helper in BrauerScalarDefectLifts is private. Verdict: pass.
4. Read the proof from its theorem downward. The central defect, local constancy,
   and cocycle calculation are direct and complete, with no postponed obligations.
   Both added imports are proof-only and supply the center and continuous-action
   results. The removed direct import was redundant. Read dag/units/sk-thm-br.json:
   this node is not a realized unit statement or step, and no unit route or realized
   record changes. Verdict: pass.
5. Compared the node, its two dependency modules, and the Lean proof. Updated proof
   steps to name the actual Mathlib route, retaining both needed definition nodes
   in proof_deps. The existing proof_origin attribution and source are retained
   with a note describing the S1 implementation. No new-node fields are needed.
   Verdict: pass.

Second reading changed the report and node proof metadata only; the compiling Lean
proof needed no repair.
