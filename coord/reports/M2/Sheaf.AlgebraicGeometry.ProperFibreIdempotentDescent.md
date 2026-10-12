## What changed

Proved `AlgebraicGeometry.proper_fibre_idempotent_descent` in
`Sheaf.AlgebraicGeometry.ProperFibreIdempotentDescent`, with its signature and docstring unchanged.
Added two proved private helpers: `descend_idempotent` descends a section and its idempotent equation
using Mathlib section descent and eventual vanishing; `affine_fibre_idempotent_descent` combines
proper Noetherian approximation with the existing fibre-limit theorem and transports the limiting
cone and stage fibres along their recorded equalities. The public proof restricts to an affine open,
constructs the canonical restriction-fibre isomorphism as `pullback.map`, and transports the affine
result back to the original fibre. This follows Stacks Tag 0G7X, general case (checked against
https://stacks.math.columbia.edu/tag/0G7X). No new public declarations, definitions, or axioms.

The locally Noetherian property uses the approximation's locally finite type maps to
`Spec (ULift ℤ)` and Mathlib's `LocallyOfFiniteType.isLocallyNoetherian`. Thus neither the
approximation's extra affine-stage clause nor its base global-section colimit is needed.
Updated the existing node's proof, proof dependencies and proof origin to this implementation.
The unit route is unchanged; this auxiliary node is not itself one of the unit's realized steps.

Validation: the complete module compiles locally without errors or warnings, including after
removing unused proof imports. No signature, public import, attribute or file-level option changed;
transparency options are scoped to individual proofs. Existing imported theorems may still depend
on upstream sorries, as permitted by stage 3.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.proper_fibre_idempotent_descent`
(node `lem-weil-pbc-stein-fibre-idempotent-descent`).
The two private helpers are fully proved. Zero sorries left in the delivered module;
zero holes added or split off. This is a proof from existing declarations, not a decomposition.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.ProperBasic`: the needed compactness and quasi-separatedness follow
  directly from Mathlib properness and base-change instances.
- `Mathlib.RingTheory.FiniteType`: no direct use remains; Noetherian permanence is obtained from
  Mathlib's scheme-level locally finite type theorem.

Removed direct proof dependencies:
- `pqf-def-locnoeth`: retained as a statement dependency; the proof uses the scheme-level
  permanence theorem rather than unfolding this definition as a separate proof step.
- `pqf-lem-proper-basic` / `Sheaf.AlgebraicGeometry.ProperBasic`.
- `lem-weil-pbc-finite-type-algebra-noetherian` / `Mathlib.RingTheory.FiniteType` as a separate step;
  the scheme-level Mathlib leaf `pqf-lem-locnoeth-lft` now performs the permanence step.
- `lem-weil-pbc-limit-residue-field` / `Sheaf.AlgebraicGeometry.LimitResidueField` as a direct step:
  it is already encapsulated in `lem-weil-pbc-limit-fibre-products`, whose module remains imported.

Retained `Sheaf.AlgebraicGeometry.ProperLimitNoetherian`,
`Sheaf.AlgebraicGeometry.LimitFibreProducts` and
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`. No claim is made that the removed direct
prerequisites are globally unreachable: other modules and retained dependencies may still use them.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface found. The original DAG's ring-level Noetherian argument
and separate residue-field step were unnecessary in this module: the available scheme-level
Noetherian permanence and fibre-limit theorem already package them. The local checkout omits the
untracked Stacks TeX source, so the source was read from its official Tag 0G7X page.

## Second reading by M2

1. **Statements and interfaces:** Compared the delivered module with the repository version.
The public theorem signature, docstring, imports visible to downstream modules, and all existing
declarations are unchanged; only proof code and proof-only imports were added or removed. Verdict:
pass.

2. **Proof and trust basis:** Compiled the complete module with `lcompile.py`; it has no `sorry`,
forbidden declarations, or warnings. An axiom print for
`AlgebraicGeometry.proper_fibre_idempotent_descent` reports only `propext`, `Classical.choice`,
and `Quot.sound`. Verdict: pass.

3. **Split statements and search:** No new public or split-off statements were introduced. The
private helpers are proved in full, and the existing node remains the sole target. The recorded
Mathlib searches found no duplicate theorem. Verdict: pass.

4. **Route and pruning:** The proof uses the existing proper-limit and fibre-product declarations,
then Mathlib section descent and scheme-level locally-Noetherian permanence. The removed
`ProperBasic` and `FiniteType` imports are unused, and the node's proof dependencies match the
implemented route. Verdict: pass.

5. **DAG and unit agreement:** The existing Lean signature is byte-identical to its original;
the unchanged node statement agrees with it, and its
proof, dependencies, and origin describe the delivered route. The unit `sk-thm-p1` route and
realized fields are unchanged. Verdict: pass.

Changed only this review record and completed the pruned-dependency list with `pqf-def-locnoeth`;
no Lean declarations or DAG statements required repair.
