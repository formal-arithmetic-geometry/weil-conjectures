## What changed

Proved `MvPolynomial.ringKrullDim_localizationAtMaximal` with its signature and visibility
unchanged. A fully proved private helper `MvPolynomial.height_maximal_eq_numVariables`
inducts on the number of variables. The successor step transports the ideal by
`finSuccEquiv`, contracts it by `Polynomial.C`, uses Mathlib's Jacobson contraction
lemma, and applies `Polynomial.height_eq_height_add_one`. The original theorem then
uses `IsLocalization.AtPrime.ringKrullDim_eq_height`.

Added proof-only imports `Mathlib.RingTheory.Jacobson.Ring` and
`Mathlib.RingTheory.KrullDimension.Zero`. Kept the existing public import. Updated
only the node's `proof`, `proof_deps`, and `proof_origin`, and the theorem's proof
explanation, to agree with the Lean proof.

LeanFinder, Loogle, and source grep were run through msearch. They located the
polynomial height step and the Jacobson maximal-contraction lemma. The tempting
alternative through `finiteTypeDomain_ringKrullDim_localizationAtMaximal` would
introduce an import cycle: that module already imports this item.

The proof handles `n = 0` explicitly and all fields and maximal ideals, including
non-rational closed points and positive characteristic. No statement or definition
was changed. The item's node is not a realized statement or step of `sk-thm-p1`,
so replacing its internal proof preserves the unit route.

## Proved and sorry left

Closed the sole original hole: `MvPolynomial.ringKrullDim_localizationAtMaximal`
(node `lem-weil-pbc-polynomial-ring-maximal-localization-dimension`).
The private induction helper is fully proved. Holes closed: 1; holes added: 0;
split off: 0. No `sorry` remains in any delivered Lean file.

The module compiles without warnings using lcompile. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. The deliver3 dry run printed OK:
compilation and preflight passed except for the second reading, which the designated
second reader writes. Nothing was pushed.

## No longer needed

No existing imports were removed: the module originally imported only
`Mathlib.RingTheory.KrullDimension.Polynomial`, which the proof uses.
No Sheaf or WeilConjectures proof-dependency modules are needed.

Removed these explicit DAG proof dependencies:

- `lem-weil-pbc-zariski-lemma` (explicit residue-field finiteness).
- `lem-weil-pbc-minimal-polynomial-quotient-field-iso` (constructing generators).
- `lem-weil-pbc-polynomial-coefficient-map-kernel` (identifying successive quotients).
- `lem-weil-pbc-polynomial-ring-domain` (proving those successive quotients are domains).
- `lem-weil-pbc-finite-type-algebra-noetherian` (the needed polynomial Noetherian instance
  is supplied by Mathlib directly).
- `lem-weil-pbc-localization-noetherian` (no Noetherian localization argument is used).
- `lem-weil-pbc-noetherian-local-dimension-le-generators` (no generator upper bound).

These nodes have Mathlib matches, so there are no corresponding Sheaf modules to
remove. This is pruning of this item's proof route; other users may still need them.
The polynomial-ring, Noetherian-ring, localization, Krull-dimension definition nodes
and the localization-dimension/height node remain in `proof_deps`.

## Where the brief, the DAG or earlier work was wrong

The original six-step plan is mathematically valid but unnecessary. Its existing
`mathlib_candidate` already suggested the successful induction route; Mathlib also
supplies precisely the maximal-contraction theorem needed for that induction.
The finite-type-domain alternative noted there would be circular in the current
library, as explained above. No disputed statement, tool workaround, new node,
forced adaptation, or change record is needed.

## Second reading by R2

1. **Interface and accidental changes.** Compared the delivered module with the
repository version. The theorem signature, visibility, statement, imports needed
for its public interface, and surrounding declarations are unchanged; only
proof-only imports, the private helper, and proof documentation were added.
Verdict: pass.

2. **Proof validity and axioms.** Compiled the module with `lcompile.py`; it
finishes without errors or warnings and contains no `sorry`, `axiom`, `unsafe`,
`opaque`, `extern`, or `implemented_by`. The proof is a direct induction using
Mathlib's height and Jacobson contraction results. A scratch axiom check reports
only the permitted axioms (`propext`, `Classical.choice`, `Quot.sound`). Verdict:
pass.

3. **Statements and split-offs.** No statements were split off and no new holes
were introduced. The private induction helper is fully proved, and the target
theorem has exactly the original hypotheses and conclusion. The zero-variable
case and arbitrary maximal ideals are covered. Searches found no existing
declaration duplicating the helper or target. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the shorter Mathlib induction
route suggested by the node's candidate, while retaining the unit's target
statement and route. The removed proof dependencies are genuinely unused, and
the two added imports are proof-only. Verdict: pass.

5. **DAG agreement.** The node's proof steps, proof dependencies, and origin
describe the induction, height transport, Jacobson contraction, and localization
translation implemented in the module. No unit realization fields or statement
fields changed. Verdict: pass.

Changed during second reading: added this review section only; no Lean or DAG
changes were necessary.
