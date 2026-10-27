## What changed

Proved `Algebra.exists_separable_residueField_section` in
`Sheaf.TraceFormula.SeparableResidueCoefficientSection`, preserving its signature,
universes and public imports. The separable residue field is formally étale by
Mathlib, hence formally smooth. Mathlib's complete-target lifting theorem applied
to its identity algebra map gives the section; taking underlying ring maps gives
the required equation. Replaced the two private WeilConjectures proof imports by
`Mathlib.RingTheory.Smooth.AdicCompletion` and updated the node's proof route.
The declaration docstring now explains this shorter argument.

The source read was Stacks More on Algebra, Tag 0C34,
`lemma-lift-residue-field`, together with Mathlib's `Etale/Field.lean` and
`Smooth/AdicCompletion.lean`. The argument needs no Noetherian or finite-degree
hypothesis and works for arbitrary separable algebraic residue extensions and
independent base and target universes. The latest blueprint's curve-zero unit
and its recorded realizations are unchanged.

## Proved and sorry left

Closed the sole hole: `Algebra.exists_separable_residueField_section`
(node `lem-trf-separable-residue-coefficient-section`). Original holes: 1;
closed: 1; added: 0; remaining: 0. No split-off declarations.

## No longer needed

Removed private imports:
- `WeilConjectures.RingTheory.FormallySmoothAdic`;
- `WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete`.

This proof no longer needs nodes `def-weil-pbc-formally-smooth-adic` or
`lem-weil-pbc-fs-adic-lift-into-complete`, or their further proof dependencies:
Mathlib already supplies exactly the complete-target lift needed here. Removed
the latter node's obsolete top-level `tool_uses` entry. These modules and
statements are preserved for other consumers; no module is withdrawn.
Retained `Mathlib.RingTheory.Etale.Field`, which supplies the separable-extension
formal étaleness theorem and realizes the remaining declared proof dependency.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but unnecessarily general: the source ideal is zero
and the target ideal is exactly the completeness ideal, so Mathlib's discrete
formal smoothness theorem handles the lifting directly. No statement correction
or definition repair was required. The whole proof is a five-line Mathlib-only
proof, so no additional lifting node is needed under stages/1-dag.md §2.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
