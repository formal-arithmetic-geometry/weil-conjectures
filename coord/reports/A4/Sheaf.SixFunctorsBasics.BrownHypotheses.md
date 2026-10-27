## What changed

Copied the current module into the A4 sandbox and made the final theorem's geometric
setup explicit: quasi-compactness supplies `CompactSpace X`, and locally finite type
supplies `IsLocallyNoetherian X`. These are the hypotheses required by the existing
Noetherian Brown criterion. No public statement, definition, import, or existing node
was changed.

## Proved and sorry left

The module's existing formal lemmas remain proved. The theorem
`CategoryTheory.brownHypotheses` remains the single `sorry`. Its unrestricted
arbitrary-field compactness premise is explicitly marked `STATEMENT-DISPUTED` in the
source and in node `sk-lem-brown-hypotheses`; the available compactness results require
a finite-field datum or an explicit Ext bound, so they cannot prove this theorem for an
arbitrary positive-characteristic field. No new `sorry` was added.

## No longer needed

None. The existing proof imports remain in use by the proved criterion and
specialization lemmas in this module.

## Where the brief, the DAG or earlier work was wrong

The final arbitrary-field Brown theorem has no valid proof from its stated hypotheses:
the DAG itself records that the unrestricted compactness input is disputed. The finite
field and integral compactness theorems in the import closure have strictly stronger
hypotheses. The only remaining hole is therefore retained rather than replaced by the
retired false compactness witness.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
