# EtaleCEClosedPageBounds

## Reason

The static interface checker treats a local tactic macro as a changed command. The macro
is local to this module and proves the closed numeral bounds omitted in the existing
statement by decide, avoiding the default lia scan of the large CE context. The theorem's
textual signature and both public imports are identical. No exported definition, statement,
instance, notation or macro is changed; no downstream adaptation is necessary.

## Old

No local lia override; omitted spectral-sequence page bounds use their imported default tactic.

## New

```lean
local macro_rules | `(tactic| lia) => `(tactic| decide)
```

The scope ends at the namespace end. This changes only the method of elaborating proofs
of the closed page inequalities; the kernel checks the resulting decide proofs.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleCEPrescribedQuotientPageDescent | unchanged holder | none; signature and visibility unchanged |

No consumer uses the local macro. No adapted module is delivered.

## Status

landed 20261013T123213-L-3679556 2026-10-13 (merge of deliver/X2/Sheaf.Paper.EtaleCEPrescribedNormalizedFirstPages)
