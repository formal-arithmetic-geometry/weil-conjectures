## What changed

Closed the proof of `isNoetherian_genericFormalFiber_of_regular_powerSeries` without
changing its signature or docstring. Added private proof imports
`Sheaf.RingTheory.AdicCompletionNoetherian` and
`Sheaf.RingTheory.FibreRingNoetherian`. Regular-local Noetherianity passes to the
prime localization, then to its maximal-ideal completion, then to the generic
fibre. The model hypothesis stays in the statement and is unnecessary in this proof.
Updated the existing node's proof route, proof dependencies and proof origin.

## Proved and sorry left

Hole closed: `isNoetherian_genericFormalFiber_of_regular_powerSeries`
(node `new-lem-weil-pbc-generic-formal-fibre-noetherian`). One of one original
holes closed; zero holes added; zero split off; no sorry remains in the module.
The scratch axiom check of this theorem and both invoked library theorems reports
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

None. No import or module was removed. The old node's `proof_deps` was empty,
so there are no old proof dependencies to mark as pruned. Public imports supply
the unchanged statement's regular-local, Cohen-ring, power-series, completion,
localization and fibre vocabulary; both new private imports are used by the proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG provided only an extracted obligation, not a proof plan.
The stronger general completion and fibre theorems already prove this obligation;
the power-series model is not needed for its Noetherianity clause. No mathematical
statement is changed. The earlier report incorrectly suggested the model hypothesis
was removed and carried an unnecessary change record for a proof-only edit.

## New nodes

None. No statement or definition change and no change record are needed.

## Second reading by E2

1. Compared the sole delivered module with the repository using `diff -u`.
   The existing theorem signature and docstring are byte for byte unchanged;
   only its proof and two private imports differ. No definitions, targets or
   other modules changed. Verdict: pass.
2. Compiled the module locally through `lcompile.py`, without errors or warnings.
   Inspected the proof: no sorry, axiom, unsafe, opaque, implemented_by, extern,
   or data selected from an unproved existence theorem. A scratch copy prints
   the axioms of the theorem and both library dependencies: only the three
   permitted axioms, no `sorryAx`. Verdict: pass.
3. No statements are split off and no new declarations or nodes are added.
   Checked the general argument also for a field (zero maximal ideal), zero
   variables in the model, and the zero prime; localization, arbitrary-ideal
   completion and fibre Noetherianity cover these cases. Verdict: pass.
4. Read both imported proved lemmas and searched Mathlib with a new `msearch.py`
   grep query about Noetherian completions and fibres; searched `lean/Sheaf`
   and `lean/WeilConjectures` for the same notions. No shorter direct theorem
   was found. The two proved library lemmas give the natural short reduction.
   Both private imports are used; all public imports support the preserved
   statement. Checked `dag/units/sk-thm-p1.json`: this node is below the unit's
   realized steps, and this proof replaces no unit statement or step.
   No old proof dependency is unused. Verdict: pass.
5. Compared the node with the Lean proof and the two dependency nodes.
   `proof_deps` names exactly `lem-weil-pbc-adic-completion-noetherian` and
   `lem-weil-pbc-fibre-ring-noetherian`; these declarations are the ones used.
   The proof describes localization, completion and fibre Noetherianity.
   Corrected `proof_origin` to identify the general reduction as agent-written
   rather than attributing its exact route to Proposition 07PS. Verdict: pass.

Second reading changed the report and proof-origin attribution, and removed the
unnecessary change record. The Lean proof was correct and was left unchanged.
