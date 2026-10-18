## What changed

Proved `AlgebraicGeometry.Etale.exact_couple_differential` without changing its
statement, hypotheses, universes, visibility, or either public import.
The existing `truncation_exchange_couple_morphism` supplies the exact couples,
structure-map identifications, three squares, and E₂ comparison. Mathlib
`CategoryTheory.conj_eqToHom_iff_heq` and `dcongr_heq` turn the heterogeneous
equalities into pointwise conjugation formulas inside the proof. These form a
`CoupleMorphism`; `derivedCoupleFunctoriality` supplies the page family, all
differential squares, and the successor kernel/projection equations. Only its finite-page
conclusion is used. The zero-page equality is the required conjugated exchange map.

Updated the existing node's proof, proof dependencies and proof origin to this route.
The repair removes all three duplicate private declarations named in the return:
`AlgebraicGeometry.Etale.family_map_eq`, `family_map_eq_shift`, and `initialG_eq`.
Their existing counterparts in `Sheaf.AlgebraicGeometry.TruncationExchangeAbutment`
are private, so the repaired proof instead uses the public, more general Mathlib
transport API directly. No helper is restated under another name.

Single-file remote compilation of the repaired proof passed in 4.7 seconds with no
errors or warnings. No definitions, existing statements, or public interfaces changed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Etale.exact_couple_differential`
(node `lem-weil-pbc-exact-couple-differential`).

Zero holes remain in the item; zero holes added and zero split off. This is a proof
from existing declarations, not a decomposition. Imported declarations retain their
existing proof obligations; no claim is made that the entire imported closure is sorry-free.

## No longer needed

Removed the three duplicate private transport helpers listed above. The proof does
not need to import `Sheaf.AlgebraicGeometry.TruncationExchangeAbutment`; its private
helpers are replaced by the existing Mathlib API.

Removed these private proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`
- `Sheaf.CategoryTheory.ExactCouple`
- `Sheaf.CategoryTheory.ExactCoupleMorphism`
- `Sheaf.CategoryTheory.TruncationCouple`
- `Sheaf.CategoryTheory.TruncationCoupleExact`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.BaseChange.Derived`
- `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.Algebra.Homology.ExactCouple.Basic`
- `WeilConjectures.CategoryTheory.ExactCouple`
- `WeilConjectures.CategoryTheory.TruncationCouple`

The direct proof no longer needs nodes `def-sp-truncation-couple`,
`def-weil-pbc-hypercohomology-filtrations`, `lem-sp-truncation-couple-exact`,
`prop-weil-pbc-inverse-image-exact`, `lem-weil-pbc-exact-functor-bounded-below`,
`lem-weil-pbc-derived-exchange-triangulated`, `def-weil-pbc-triangles-with-shift`,
`lem-sp-couple-morphism`, or `def-weil-pbc-direct-image` as separate proof steps.
The constructions and comparisons needed here are already the conclusion of
`lem-weil-pbc-truncation-couple-morphism`; their underlying infrastructure remains
available through that module. Removing a direct import does not assert that the module
leaves the entire targets' import closure.

The broad `lem-sp-couple-morphism` tool approval was withdrawn from this node's
`tool_uses`. The proof uses its existing finer prerequisite
`lem-sp-derived-couple-functoriality` directly as a generic tool for finite pages;
its declaration gives exactly the needed family and compatibility equations, without
any half-plane convergence, abutment, or limiting-page hypotheses. This is the same
exact-couple functoriality route below the unit level, not a bypass of any unit realization.
The independent reviewer can record the replacement tool approval if required.

## Where the brief, the DAG or earlier work was wrong

The DAG still expanded the exactness and exchange-square arguments even though
`truncation_exchange_couple_morphism` already states all those conclusions, including
the E₂ identification. Also, `Sheaf.CategoryTheory.ExactCoupleMorphism.coupleMorphism`
is currently commented out following the upstream synchronization; its finer existing
prerequisite `derivedCoupleFunctoriality` is available and suffices. No new intermediate
statement is needed. The blueprint unit's statement and realized steps are preserved.

The returned delivery unnecessarily duplicated three private abutment helpers. This
repair deletes those declarations entirely and applies Mathlib transport lemmas at
the six concrete alpha, f and initialG uses. No other module needs adaptation.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
