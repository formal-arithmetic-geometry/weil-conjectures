## What changed

Proved `MvPowerSeries.field_cohen_power_series_formally_smooth` in
`Sheaf.RingTheory.FieldCohenPowerSeriesFormallySmooth`, without changing its signature.
Two proved private helpers implement the field-case rational lifting and the case split.
Added proof-only imports `Sheaf.RingTheory.FormallySmoothAdicUniverseLift` and
`Mathlib.RingTheory.Smooth.Basic`. All original imports remain necessary for the
statements or the proof. Updated the existing node's proof, proof dependencies and
proof origin to record universe transfer. No other module or interface changed.

In the field case, turn `IsField` into a compatible `Field` instance, lift the rational
structure map using Mathlib's localization formal smoothness, and apply
`MvPowerSeries.formallySmoothAdic_rat`. In the Cohen case, apply
`MvPowerSeries.formallySmoothAdic_int_of_isCohenRing`. Both cases use the proved
`Algebra.formallySmoothAdic_lift_universe` for independent source and test universes.
Convert ring maps to integer-algebra maps to obtain the adic formal smoothness conjunct.
For the explicit bound, prove `m ^ r ≤ J.comap h`, square this containment and use
`Ideal.le_comap_pow` and `J ^ 2 = ⊥` to show that the lift kills `m ^ (2 * r)`.

Validation: the single-file local compile passes without warnings or errors. The proof
uses no positivity of `n`, so `n = 0` is included; the ideal calculation also works
for the zero ideal and imposes no nontriviality on the test ring. The integer-algebra
conjunct allows an arbitrary integer-algebra structure on the test ring.

## Proved and sorry left

Closed the module's one hole:
`MvPowerSeries.field_cohen_power_series_formally_smooth`
(node `lem-weil-pbc-field-cohen-power-series-formally-smooth`).
No `sorry` remains in this module. No holes added, no statements split off.

The proof depends on the two existing holed declarations
`MvPowerSeries.formallySmoothAdic_rat` and
`MvPowerSeries.formallySmoothAdic_int_of_isCohenRing`, both recorded by
`lem-weil-pbc-power-series-cohen-formally-smooth-adic`; those are unchanged and
remain the next proof obligations. The universe-transfer theorem and its small-model
construction are already proved. This closes one upper hole from the existing
statements, rather than establishing the entire import closure as sorry-free.

## No longer needed

None of the original imports is pruned. The proof no longer uses the node
`lem-weil-pbc-localization-square-zero-lifting`, which was an old proof dependency;
the corresponding experimental import of
`Mathlib.RingTheory.Localization.FractionRing` was removed as redundant with the
remaining imports. No new theory of power series, Cohen rings, completions, or
coefficient-field lifts was added.

## Where the brief, the DAG or earlier work was wrong

The original plan did not record the universe transfer needed for the explicit
`D : Type v` lifting clause: `FormallySmoothAdic` only quantifies over the universe
of its base and source. The existing, proved node
`lem-weil-pbc-fs-adic-universe-lift` supplies precisely that transfer; added it to
the node's proof dependencies. No mathematical statement correction is needed,
and the unit's realized statements and steps are unchanged.


## Second reading by K3

1. Compared the delivered module with the repository version. The public theorem
   statement and all existing declarations are byte-for-byte unchanged; only proof
   helpers and proof-only imports were added.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings.
   There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`
   declarations in the delivered file. The only remaining proof obligations are the
   two pre-existing imported power-series lemmas named above.
3. Checked the helper route against Mathlib and the existing universe-lift theorem.
   The field branch uses `FormallySmooth.of_isLocalization`; the Cohen branch uses
   the existing Cohen power-series theorem. The bound follows from ideal comap and
   square-zero arithmetic. No duplicate or split-off statement was added.
4. Checked pruning and dependencies. The obsolete localization square-zero node was
   removed from `proof_deps`; the universe-lift node is recorded and used. The unit's
   realized statement and steps remain unchanged.
5. Checked edge cases including `n = 0`, the zero ideal, and arbitrary commutative
   test rings; the proof imposes no extra hypotheses and retains the exact target
   strength.

Changed the report and DAG dependency metadata only; no mathematical statement or
Lean interface was changed.
