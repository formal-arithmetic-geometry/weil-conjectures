## What changed
Added `FiniteUnramifiedEtaleLocalReduction.lean` with two intermediate theorems isolating (1) finite-fibre enumeration and application of the unramified decomposition lemma and (2) the shrinking/base-change/clopen-to-coproduct construction. The target module now combines these intermediate results; all files compile.

## Proved and sorry left
The target theorem `exists_etale_closed_immersion_decomposition_of_finite_unramified` is reduced by a complete Lean application to the two intermediate statements. The intermediate theorems `finite_decomposition_input` and `finite_coproduct_of_unramified_decomposition` remain `sorry`, each representing a strict part of the Stacks 04HJ proof.

## No longer needed
No imports were removed. The direct lower-level dependencies are encapsulated by the intermediate reduction theorem.

## Where the brief, the DAG or earlier work was wrong
The original DAG proof combines several substantial geometric and categorical steps. These cannot be discharged from the currently stated declarations in the available time, so they were split into two strict intermediate statements rather than leaving a partial proof.

## New nodes

`lem-weil-pbc-finite-unramified-etale-local-input` records `finite_decomposition_input` in the new reduction module.

`lem-weil-pbc-finite-unramified-etale-local-reduction` records `finite_coproduct_of_unramified_decomposition` in the new reduction module.

## Second reading by J2

1. Compared the delivered target module with the repository version. The target statement and all existing declarations are byte-for-byte unchanged; only the proof now applies the two named reductions. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds with no errors. The only remaining `sorry`s are the two named intermediate theorems, each documented and represented by a DAG node. Verdict: pass.
3. Checked both split-off statements against the Stacks 04HJ proof route. They are strict intermediate reductions and preserve the target conclusion; no duplicate library theorem was found. Verdict: pass.
4. The route still uses the existing unramified local decomposition unit step, with no imports removed because the reduction module needs it. Verdict: pass.
5. Updated both new DAG nodes with statement dependencies, Mathlib search records, and the exact Lean declaration signatures required by the delivery checker. Verdict: pass.

Changed the report and new node metadata only; no Lean proof changes were needed during second reading.

## New nodes

lem-weil-pbc-finite-unramified-etale-local-input: records `finite_decomposition_input` in `FiniteUnramifiedEtaleLocalReduction.lean`.

lem-weil-pbc-finite-unramified-etale-local-reduction: records `finite_coproduct_of_unramified_decomposition` in the same module.
