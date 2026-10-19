## What changed

Proved `semilocal_restriction_length` with its original signature. Two fully proved private
helpers calculate the restricted length of a maximal residue field and its localized length
(one at its own maximal ideal, zero elsewhere). Induction on `IsFiniteLength` combines
these calculations using length additivity and exactness of localization. Added the
proof-only import `Mathlib.RingTheory.Localization.Module` for localized linear maps.

## Proved and sorry left

Closed the one original hole: `semilocal_restriction_length`
(node `lem-exc-semilocal-restriction-length`). Added zero holes; zero sorries remain.
The private helpers `residue_restriction_length` and `localized_residue_length` are proved.
The zero module and zero ring are covered by the subsingleton induction case.

## No longer needed

Removed `WeilConjectures.RingTheory.SimpleFiltration` and the proof dependency
`lem-weil-pbc-finite-length-module-simple-filtration`: the defining induction principle of
Mathlib's `IsFiniteLength` already gives exactly the simple-extension induction needed.
Removed its obsolete top-level `tool_uses` approval from the node as well.
No other declared dependencies are pruned. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically sound. Its separately chosen composition series
and final regrouping are unnecessary: add one simple factor at a time and simplify the
single nonzero summand. The residue field degree is calculated using the explicit canonical
`Ideal.ResidueField.map` action and surjectivity of the maximal residue map; no arbitrary
field action or unproved data construction is used. The DAG proof is updated accordingly.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
