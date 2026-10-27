## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.exists_monoidal_resolution_tower` with a complete Lean proof
combining the existing fan-desingularization and strict étale descent theorems
with two new intermediate statements. The original theorem signature and its
public import are unchanged. All added imports in the item are private proof
imports. No existing module besides the item is changed.

The proof obtains a charted procedure from a fixed fan resolution, extends it by
`functorial_log_blowup_etale_descent`, and applies the extension to the given
admissible input. It identifies each terminal geometric characteristic with a
charted terminal characteristic and then with a smooth terminal fan stalk. It
composes these monoid isomorphisms and explicitly converts the function model
`Multiplicative (Fin r → ℕ)` to the exact required model
`ULift (Multiplicative (Fin r →₀ ℕ))` using `Finsupp.addEquivFunOnFinite`,
`AddEquiv.toMultiplicative`, and `MulEquiv.ulift`.

The two new modules separate the global-chart construction/comparison argument
from terminal-stalk locality. Their public theorem statements contain the
remaining work; both have source citations and full proof instructions in their
docstrings and matching DAG nodes. These are different parts of the source proof:
the first constructs a procedure only on globally charted inputs; the second
assumes supplied procedures and comparisons and proves a stalk-locality fact,
without asserting the existence of a resolution or any freeness.

## Proved and sorry left

Original item: one hole. Closed its body:
`AlgebraicGeometry.exists_monoidal_resolution_tower`
(`lem-trf-monoidal-resolution-tower`). Its reduction to the cited declarations is
complete. There are zero `sorry`s remaining in the item module.

Remote `lcompile.py --all` compiled all three modules without errors or warnings:
3.6 s for each intermediate module and 5.4 s for the item. Subsequent delivery
checks validate the final import cleanup as well.

Added two holes, both public theorems whose bodies are exactly `:= by sorry`:

- `AlgebraicGeometry.exists_charted_fan_resolution_procedure`
  (`lem-trf-charted-fan-resolution-procedure`), in
  `Sheaf.AlgebraicGeometry.ChartedFanResolutionProcedure`.
- `AlgebraicGeometry.log_blowup_extension_terminal_stalk`
  (`lem-trf-log-blowup-extension-terminal-stalk`), in
  `Sheaf.AlgebraicGeometry.LogBlowupExtensionTerminalStalk`.

This is a decomposition, not a completed proof of monoidal resolution independent
of the remaining holes: one original hole closed, two holes added, net minus one
hole closed in the delivery. Existing dependency holes remain in their owning
modules and were not copied or altered. No definitions or instances have holes.

The edge-case reading checked the empty input, length-zero towers, rank zero,
consecutive whole-center deletions, and proper principal centers (which are
retained). In the terminal-stalk statement the same algebraically closed field
suffices because the covering maps are étale. The locality statement does not
assume smoothness, log regularity, or free characteristic monoids.

## No longer needed

No original import was removed, and no module is withdrawn or globally pruned.

Removed redundant private imports from the new intermediate modules after the
first clean compile: `LogFanChartBlowup` from each, `StrictFanChartLocalComparison`
from `ChartedFanResolutionProcedure`, and `CoherentLogIdealChartConstruction`
from `LogBlowupExtensionTerminalStalk`. Their current statements need only the
public `StrictEtaleLogBlowupProcedure` import; their future proof dependencies
are retained in the nodes and proof instructions.

The original item's direct proof-dependency list no longer directly cites
`lem-trf-log-fan-chart-blowup` or
`lem-trf-strict-fan-chart-local-comparison`; these are still needed by the new
charted-procedure lemma. The log-chart theorem is also needed by the new
terminal-stalk lemma. Their modules remain needed, so this is a relocation of
work, not a claim that they can be deleted or omitted from the library.

All five original dependencies remain needed somewhere in the reduction:
fan desingularization and procedure descent are used directly; the two chart
lemmas are used in the split-off work; the fs log blowup definitions remain the
public statement provider. The fine-fan definitions also provide the terminal
smoothness assertion used in the Lean proof. No unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical route is unchanged. The stated dependency signatures do not
already assemble a chart-independent log procedure from a fan resolution, or
expose the terminal-stalk localization for an arbitrary extension. Those two
pieces of glue are now stated separately rather than hidden in the original
hole. The supplied source explains them in the proof of ILO VIII 3.3.15.

The terminal-stalk argument uses the coherent-ideal chart construction for strict
étale base change on general étale log structures. It does not apply
`strictLogBlowupCartesian` to an arbitrary input: that theorem requires a Zariski
log structure. No statement or definition repair was necessary.

## New nodes

`lem-trf-charted-fan-resolution-procedure` states the construction on globally
charted admissible inputs, retaining the terminal chart into the specified fan
resolution and its geometric-stalk comparison. It covers original proof steps
1--4, leaving the already stated étale extension theorem to do the global descent.
Its source is ILO VIII 3.3.13 and the proof of 3.3.15, pp. 108--110.

`lem-trf-log-blowup-extension-terminal-stalk` states the geometric-stalk locality
part of original step 6 for any procedures with the supplied charted-test
comparisons. Its source is ILO VIII 3.3.8--3.3.13 and the descent reduction in the
proof of 3.3.15, pp. 107--110.

Each node records successful LeanSearch and LeanFinder queries and a source grep
of Mathlib, WeilConjectures, and Sheaf. Returned types concern ordinary scheme
morphisms or ordinary sheaf stalks and do not give these logarithmic procedure
statements. The existing Sheaf procedure, chart, descent, contraction, and
rigidified-quotient declarations were read before introducing the new statements;
none states either missing step. A whole-blueprint search for log blowups found
no duplicate. Both nodes inherit the item's chapter, unit, and blueprint ancestry.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
