## What changed

Replaced the first worker's `Algebra.popescuEighthPowerLifting_tail_core` restatement
with the narrower `Algebra.popescuEighthPowerLifting_quotientData` in the new module
`Sheaf.RingTheory.PopescuLiftQuotientData`. Its conclusion constructs the fixed first
quotient and transports the tail inputs; it has no induction hypothesis and does not
assert that the first quotient can be resolved. The existing successor theorem now
explicitly applies `ih` to those quotient rings and tail inputs, then packages the
result. Restored the existing theorem's original docstring. All existing signatures
and definitions are unchanged; there is no change record or forced adaptation.

The successor's only new import is the proof-only (plain) import of the quotient-data
module. The new module publicly imports `PopescuLiftInduction` for its signature and
plainly imports `StrictlyStandardBaseChange` and Mathlib's tensor-quotient module for
the open transport proof's dependency plan. Existing node proof fields now describe
the actual reduction.

## Proved and sorry left

Hole closed: `Algebra.popescuEighthPowerLifting_tail` (existing node
`lem-weil-pbc-popescu-lift-successor`), conditionally on the named quotient-data lemma.
Hole added: `Algebra.popescuEighthPowerLifting_quotientData`, node
`lem-weil-pbc-popescu-lift-quotient-data`; this is the only delivery-local `sorry`.
The rejected `Algebra.popescuEighthPowerLifting_tail_core` and its node are removed.
This is a decomposition: one existing hole closed, one strictly-partial hole added,
net zero holes, not a completed proof of the target closure. No hole is in a definition.

Both delivered files compile locally without warnings. A scratch-copy axiom check
shows `popescuEighthPowerLifting_tail` uses only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`; the quotient-data theorem has the same axiom set. The
two induction definitions use only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No import or module is pruned. Every former proof dependency remains used transitively:
`def-weil-pbc-popescu-resolution`, `def-weil-pbc-strictly-standard-element`,
`lem-weil-pbc-strictly-standard-base-change`, and
`lem-weil-pbc-tensor-quotient-base-change` are no longer direct dependencies of the
successor's completed proof; they belong to the new quotient-data lemma's plan.
`def-weil-pbc-popescu-lift-induction` remains a direct dependency. The successor's
new direct dependency is `lem-weil-pbc-popescu-lift-quotient-data`.

## Where the brief, the DAG or earlier work was wrong

The first worker's core was `∃ h : P, True` under exactly the original hypotheses,
and the purported proof simply chose its witness. This is equivalent to the entire
item, not a strictly simpler statement, and is rejected regardless of whether the
tool recognizes that wrapper. Its node also lacked three searches and a verbatim
Lean signature, and the original successor node was not updated. Those faults have
been removed. The original proof docstring was replaced without reason and an
overlong proof line produced a compiler warning; both are repaired.

The source proof is indeed quotient construction/transport followed by induction;
its length does not justify a restatement. The new lemma isolates the construction
and transport before that induction. The Stacks source was read at the locally
available copy `/home/ubuntu/work-bp/sheaf/literature/stacks-project/smoothing.tex`,
Lemma `lemma-lift-solution` final paragraph and `lemma-strictly-standard-base-change`.

## New nodes

`lem-weil-pbc-popescu-lift-quotient-data` is in
`dag/nodes/sec-proper-base-change/` and matches the new module and full signature.
It records construction of the first quotient and transfer of the tail hypotheses,
strictly before applying P(n). The natural-language proof gives the quotient maps,
prime correspondence, finite-presentation base change, preceding-power kernel
identifications, strict-standard base change, and transport of the final resolution.
Real Lean Finder, Loogle, LeanSearch (unavailable), and grep searches are recorded;
the found quotient/tensor equivalences are component tools, not this lemma. Repository
and upstream searches found no duplicate; importing `PopescuLiftSolution` would be
circular because its induction already uses the successor theorem.

## Second reading by R3

1. Compared every delivered module with the repository baseline. The existing
   successor declaration's signature is byte-for-byte unchanged; its original
   docstring is restored. The new module contains only a new theorem and introduces
   no definition or public change to the existing module. Verdict: pass after repair.
2. Compiled both files in import order with `lcompile.py`; no errors or warnings.
   Inspected all delivered text: no forbidden declaration or escape hatch, and the
   only `sorry` is the new named theorem with its source, proof docstring and node.
   Scratch-copy `#print axioms` checks contain only standard axioms and `sorryAx`.
   The remaining hole is fully disclosed. Verdict: valid conditional reduction.
3. Rejected and removed the equivalent existential restatement. Checked the new
   quotient-data statement against the source: it excludes `ih` and cannot conclude
   the first resolution; it supplies the inputs to `ih` instead. The quotient
   carriers and tail are explicit, while compatibility with surjective maps uniquely
   determines the induced map and prime. No data definition chooses an arbitrary
   witness from an open existence theorem. Checked n=1 (two original parameters),
   zero or nilpotent parameters, coincident parameters, and a zero base: the kernel
   identifications and scalar actions hold; a zero target cannot have q. There is
   no extra nonzeroness or distinctness assumption. Search found no duplicate.
   Verdict: true and strictly a part of the argument, with a complete word proof.
4. Read from the successor downward. The proof makes the source's induction call;
   the remaining hole is the generic quotient transport preceding that call. The
   public import is needed for the unchanged statement; the added successor import
   is plain because only its proof needs it. All former dependencies are retained
   transitively and listed above, with no module pruned. Read
   `dag/units/sk-thm-p1.json`, including `realized`: this item is a tool below its
   realized steps, and no unit statement or route changes. Verdict: route preserved.
5. Checked the existing node's new `proof`, `proof_deps`, and `proof_origin` against
   the explicit quotient-data/induction/packaging proof. Checked the new node's full
   signature, source, searches, creation, blueprint, chapter and unit fields.
   Verdict: nodes agree; no unrecorded statement change.

Second reading changed the fake core into a genuine quotient-data decomposition,
restored the original docstring, wrote the actual induction proof, repaired the node
records and searches, and corrected the report to state zero net progress.
