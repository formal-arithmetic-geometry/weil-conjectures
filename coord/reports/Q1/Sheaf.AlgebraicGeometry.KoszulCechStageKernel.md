## What changed

Completed the earlier sandbox proof of
`AlgebraicGeometry.koszulCechCocone_stage_kernel` in
`Sheaf.AlgebraicGeometry.KoszulCechStageKernel`, without changing its statement
or docstring. Added the proof-only import
`Mathlib.LinearAlgebra.ExteriorPower.Basis`.

The three proved private helpers establish affine localization torsion,
transport of zero evaluations through the extension degree identifications,
and vanishing of a Koszul transition from its exterior-basis coordinates.
The main proof transports the zero cocone image, cancels its invertible sign,
chooses a common bound for the finitely many coordinate torsion exponents,
and transports the resulting zero cochain back to the diagram.

The earlier attempt failed at a dependent rewrite relating the subset cardinality
to the extended Koszul degree. Destructuring the basis index and applying the
proved degree-transport helper resolves that failure. The sandbox module compiles
with lcompile.py without errors or warnings. All lines meet the 100-character limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.koszulCechCocone_stage_kernel`
(node `lem-sc-koszul-cech-stage-kernel`).

Holes closed: 1. Holes added: 0. No sorry remains in the delivered module.
The private helpers `affine_section_torsion`, `extended_evaluation_zero_iff`,
and `koszul_transition_zero` are all fully proved.

The proof uses the existing construction declarations
`koszulCechHomDiagram_exists` and `koszulCechCocone_exists`; their existing
holes in `Sheaf.AlgebraicGeometry.KoszulCechComparisonConstruction` remain
outside this delivery. No claim is made that the entire dependency closure
is axiom-free yet.

The argument includes the empty index set r=0, arbitrary integer degree,
the zero ring, zero modules, and nilpotent or zero generators. No cancellation
of a generator in A, and no cycle hypothesis, is used.

## No longer needed

No repository import, DAG node, or module is pruned: the original comparison
construction import and all three stated proof dependencies remain needed.
Removed `Mathlib.Data.Fintype.Order` from the previous sandbox attempt after
verifying compilation without it. Also removed its unnecessary file-level
`backward.isDefEq.respectTransparency` option; the proof compiles with the
repository's original options. These were not present in the repository baseline.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found in the brief or DAG. The DAG's
existing proof, proof_deps, and proof_origin already describe the actual route,
so no node copy needs changing. The earlier attempt's dependent rewrite was
not accepted by Lean; the proved transport helper supplies the missing glue.
No new nodes, definitions, statement changes, or forced adaptations are needed.


## Second reading by Q1

1. PASS: compared the entire delivered module with the repository baseline.
   The existing theorem signature is byte for byte identical, including all
   hypotheses and the conclusion; its docstring and visibility are unchanged.
   The only additions are three proved private helpers, the proof body, and
   one plain proof-only import. No definitions or public interfaces changed.
2. PASS: independently compiled the module with lcompile.py (9.2 seconds,
   no errors or warnings). A scratch copy with explicit #print axioms checks
   shows only propext, Classical.choice and Quot.sound for all three helpers.
   The main theorem additionally uses sorryAx through the existing comparison
   construction; it has no direct sorry. No forbidden declarations or hollow
   definitions were added. The imported diagram's object and map equations
   determine it up to the identifications used here; the cocone formula
   uniquely determines its values since its denominator is invertible on
   the principal open. No arbitrary existence witness was introduced.
3. PASS: no statements were split off and no holes were added. Read all three
   private helper proofs: localization uses the Mathlib zero criterion,
   degree transport is substitution and reflexivity, and transition vanishing
   uses the standard exterior basis and its diagonal scalar formula. Checked
   empty Fin r, exterior degrees above r, positive extended degrees, zero
   rings/modules and zero or nilpotent generators. These require no extra
   hypothesis. The empty coordinate set still admits a common bound by
   Finite.exists_le, and the empty exterior bases force zero components.
4. PASS: searched the local Koszul/Cech modules and upstream module files for
   kernel, vanishing and localization results, and inspected the worker's
   semantic and type searches. The proof already uses Mathlib localization
   and exterior-power tools directly; no shorter existing kernel result was
   found. The public construction import is needed by the original signature;
   the new Basis import is plain and needed only by the proof. No baseline
   import or old proof dependency is unused. The unit record
   dag/units/sk-thm-picard-duality.json was inspected: its existing empty
   realized lists are unchanged, and this local kernel argument replaces no
   unit statement or unit step.
5. PASS: read lem-sc-koszul-cech-stage-kernel and the comparison construction,
   Koszul open system and principal Cech declarations it names. The actual
   proof follows the node's localization, common exponent and exterior-basis
   route. All three proof_deps remain used, and proof_origin remains accurate.
   There are no new nodes to validate and no changed node fields required.

Second reading changed only this report by adding the independent review and
explicit axiom results. The Lean proof required no repair. Holes closed: 1;
holes added: 0; no modules pruned. Existing dependency holes remain open.
