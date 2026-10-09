# Worker report: lem-weil-pbc-finite-etale-lifting-essential-surjectivity

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-etale-lifting-essential-surjectivity.json`: statement split into four proof steps; status `split`.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-etale-lifting-complete.json`: new unsplit statement; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-etale-lifting-approximation.json`: new unsplit statement; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-etale-lifting-limit-descent.json`: new unsplit statement; no Mathlib match.

## Attachments

None.

## WANTED

WANTED: `literature/stacks-project/pione.tex`, Fundamental Groups Lemma 0GS2, for the complete Noetherian algebraization, G-ring approximation, and general henselian limit-descent steps. The source is cited by the imported node but is not present in this clone.

## Review by C

I checked the target statement against the existing theorem `thm-weil-pbc-finite-etale-lifting` and its reviewed proof. The essential-surjectivity argument is independent of the idempotent-lifting proof of full faithfulness and follows the three cases in Stacks Tag 0GS2: complete Noetherian algebraization, Noetherian G-ring approximation after completion, and finite-presentation descent through a filtered henselian limit. The new nodes are statement dependencies only and remain `unsplit`. Each new node records LeanSearch, Loogle/LeanFinder, and Mathlib-source grep searches; no Mathlib theorem covers scheme-level finite-etale lifting over henselian pairs. No Lean was written or compiled.

## What was wrong or incomplete

The imported proof was empty and the parent theorem correctly identified essential surjectivity as a separate gap. The earlier claim that H^0/idempotent comparison alone proves essential surjectivity is invalid; those comparisons only establish the full-faithfulness side. The Stacks source file is absent locally, so the proof is recorded from the cited theorem's three cases and marked WANTED above.

## Unfinished

The three new statements still need their own stage-1 splits. Formal verification is outside stage 1.
