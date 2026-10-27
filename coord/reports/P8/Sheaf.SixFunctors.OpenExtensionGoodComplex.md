## What changed

Added two strictly simpler component statements for the target's conjunction: preservation
of the good-complex predicate by completed open extension, and preservation after the
completed ordinary pullback. The target theorem now combines those components with a
real conjunction proof. The two component statements remain `sorry` for follow-up proof
workers; all three modules compile.

## Proved and sorry left

Closed `WeilConjectures.IntegralSystemRealization.openExtension_goodComplex` by combining
its two component lemmas. Added `sorry` in
`openExtension_goodComplex_extension` and `openExtension_goodComplex_pullback`.

## No longer needed

None. The target's canonical bridge import is used by the target and both component
statements. The proof follows the two component obligations corresponding to the two
steps in the node; no declared dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The original target bundled two independent preservation results into one conjunctive
statement, while its proof plan has two separate mathematical arguments. The conjunction
is now reduced to those two strictly simpler obligations so each can be proved and
reviewed independently.

## New nodes

- `lem-sf-open-extension-good-complex-extension`: extension preserves the good-complex
  predicate.
- `lem-sf-open-extension-good-complex-pullback`: completed ordinary pullback preserves
  the good-complex predicate after extension.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
