## What changed

Completed the proof of `CategoryTheory.rawLocalization_finiteProduct_equivalence`
in `Sheaf.CategoryTheory.RawLocalizationFiniteProductEquivalence`, preserving its
signature, docstring and public imports. The proof constructs the localized component
functors from base-changed linear Hom maps. Tensor induction proves composition and
the canonical Hom comparison. The integral Hom equivalence, its scalar extension,
and `TensorProduct.piRight` give full faithfulness. Integral representatives and
isomorphisms tensored with one give essential surjectivity. Mathlib constructs the
equivalence and proves inverse linearity using locally scoped pointwise structures.

## Proved and sorry left

Closed the original hole in `CategoryTheory.rawLocalization_finiteProduct_equivalence`
(node `lem-pur-raw-localization-finite-product-equivalence`). Holes closed: 1 of 1.
Holes added: 0. Sorries left: none. Split-offs: none.
The prescribed single-file compiler passed cleanly in 9.6 seconds. The theorem
statement and imports match the original exactly; no lines exceed 100 characters.
The delivery preflight performs the remaining axiom and packet checks.

## No longer needed

None. No imports removed, no modules withdrawn, and no DAG dependencies bypassed.
All seven recorded dependencies are used through the existing raw localization API
or their recorded Mathlib declarations. The proof follows all six existing DAG steps,
so no node changes are needed. No new modules or declarations are introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The empty index case follows from integral
and localized full faithfulness into the empty product; integral essential surjectivity
supplies an object. This covers the zero localization and empty categories without
new nonemptiness assumptions. The module was present in the shared repository;
there was no quarantine or return entry to repair.

Several compile calls received no answer from the service (exit 124). Later calls
returned compiler diagnostics, and the final corrected file compiled cleanly. These
service delays required no tool modifications or changes to the mathematical route.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
