## What changed

Closed the sole hole in
`AlgebraicGeometry.Etale.unboundedProperOpenHorizontalComposition_of_normalization`
by specializing the already proved arbitrary-scheme theorem
`AlgebraicGeometry.Etale.etaleProperOpenHorizontalNormalization` to the supplied
squares and their composite. The public statement is unchanged.

To make that reuse acyclic, changed the unclaimed module
`Sheaf.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization`: replaced its
private import of `UnboundedProperOpenComposition` by the actual dependency
`ProperSupportSheafComposition` and included the small proved private
`open_compare_mono` it used from that import. Every existing declaration and public
import of that module is preserved verbatim. There are no other module edits. The normalization equation is repackaged once
for the whole family before applying it to the three squares, reducing repeated
kernel work.

Verification via `lcompile.py --all`: the repaired normalization module compiled
in 20.0 s, the item in 29.6 s, and its four direct importers in 25.0 s, 19.6 s,
12.9 s and 35.3 s respectively. The unchanged consumer copies were removed after
verification. No profiling options remain in the delivery.

Updated the item's node to record this specialization. Source: Stacks Tag 0F7D,
`lemma-shriek-proper-and-open-compose-horizontal` in `more-etale.tex`.
Change record: `coord/changes/K2-unbounded-proper-open-horizontal-import.md`.

Searches: Lean Finder found the generic right-derived factorization and composition
APIs; Loogle found `Functor.IsRightDerivedFunctor` and its postcomposition instance;
Mathlib grep found no complete geometric match. Local source search found the
already proved arbitrary-scheme theorem used here.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Etale.unboundedProperOpenHorizontalComposition_of_normalization`
(node `lem-amb-unbounded-proper-open-horizontal-composition`).
No holes added or split off. Neither delivered Lean module contains `sorry`.
The auxiliary module had zero holes before and has zero after this proof-import repair.

## No longer needed

Removed the private import
`Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition` from
`EtaleProperOpenHorizontalNormalization`; only its small proved private support
lemma was needed. No declaration, module or DAG node is withdrawn.

The item's old five proof dependencies are no longer needed as direct proof steps:
`lem-cbc-proper-support-sheaf-composition`, `lem-cbc-extension-zero-composition`,
`lem-weil-pbc-extension-by-zero-exact`, `lem-weil-pbc-kinjective-total-derived`, and
`lem-weil-pbc-localization-universal-property`. They remain used internally by the
reused theorem. Existing public imports are preserved for downstream compatibility.
The item's only new import is the proved horizontal-normalization module.

## Where the brief, the DAG or earlier work was wrong

The arbitrary-scheme horizontal-normalization theorem already proves the needed
result. Its private support-lemma import introduced a transitive dependency on this
Noetherian predecessor, preventing direct reuse until that unnecessary private
import was repaired. No mathematical statement or unit route needed correction.
There are no forced adaptations and no new nodes.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
