## What changed

Proved `nagata_invert_prime` in `Sheaf.TraceFormula.NagataInvertPrime`, preserving its signature and both existing public imports. Added the private proof import `Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization`. Updated the node's proof and proof_origin to describe the compiled route.

The forward implication uses Mathlib's localization `map_prime` and injectivity. For the converse, assuming x is not prime, closure induction proves x divides s*y only if x divides y. Mathlib's `map_dvd_map` then descends divisibility; a localized prime makes x prime, and a localized unit makes x a unit, giving the two contradictions.

## Proved and sorry left

Closed: `nagata_invert_prime` (node `lem-trf-nagata-invert-prime`), 1 of 1 original holes. Added: none. Remaining: none. No decomposition or new declarations.

The module compiled through lcompile.py in 1.6 seconds without diagnostics before final formatting. Delivery preflight supplies the final compilation and axiom probe.

## No longer needed

No imports, nodes, or modules pruned. The sole declared dependency `def-weil-pbc-module-localization` remains needed. The quotient-ring construction in the planned forward implication is unnecessary: Mathlib's `Submonoid.LocalizationMap.map_prime` gives that implication directly. The reverse implication uses the equivalent saturation claim x divides s*y implies x divides y, instead of explicitly constructing the cancelled quotient witness. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement or definition error found. Read Stacks Algebra Tag 0AFU, lemma-invert-prime-elements, clause (2), and its proof. The planned proof is valid; its localization and cancellation calculations have shorter existing Mathlib interfaces. The retained declaration docstring describes the original valid proof plan. No new statements require edge-case checks; closure induction includes the empty product and repeated prime factors, and the proof requires neither P nonempty nor x outside P.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
