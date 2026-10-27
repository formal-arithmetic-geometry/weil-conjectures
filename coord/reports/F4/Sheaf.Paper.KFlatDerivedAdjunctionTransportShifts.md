## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.kflat_derived_adjunction_transport_shifts`
in `Sheaf.Paper.KFlatDerivedAdjunctionTransportShifts`, preserving its statement,
public imports, definitions and fixed shift instances. The proof identifies the whole
specified adjunction with transport of the exact-left adjunction using the proved
source-library theorem `Adjunction.derived_eq_ofNatIsoLeft` and the canonical
`leftDerivedFunctorIsoMapDerivedCategory_hom_fac` equation. Its unit and counit
formulas then follow by evaluation. `canonicalRightDerivedAdjunctionShift`,
`Functor.CommShift.ofIso_compatibility` and `Adjunction.commShift_ofNatIsoLeft`
prove compatibility with the published shifts.

Added private proof imports of
`WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction` and
`WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction`. Updated the item's
DAG proof, proof dependencies and proof origin to this shorter existing-library route.
No source-library file is changed.

Validation: `lcompile.py` compiled the final module successfully (13.1 seconds,
exit code 0), with no warnings. Import-direction checks passed for both added
proof imports. The only modified node fields are `proof`, `proof_deps` and
`proof_origin`.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.kflat_derived_adjunction_transport_shifts`
(node `lem-sfb-kflat-derived-adjunction-transport-shifts`). All three clauses are
proved: unit transport, counit transport and compatibility with every integer shift.
Original holes: 1; holes closed: 1; holes added: 0; holes left in this module: 0.
No statements were split off. Dependencies retain their own existing proof status.

## No longer needed

Removed the unused direct private imports:

- `Mathlib.CategoryTheory.Functor.Derived.Adjunction`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Localization.Predicate`

The proof does not independently reconstruct the two unit lifts, cancel their
factorizations, or extend equality through localization. The proved
`Adjunction.derived_eq_ofNatIsoLeft` already supplies transport by the derived-counit
universal property. Thus the item's direct proof edges to
`lem-sfb-abstract-derived-unit-factorization`,
`lem-weil-pbc-termwise-adjunction-homotopy`,
`lem-weil-pbc-exact-functor-derived-factorization`, and
`lem-weil-pbc-localization-universal-property` are replaced by the existing
canonical-comparison and derived-adjunction interfaces. These general results
remain transitively relevant to those interfaces; no module is withdrawn and
no global pruning is claimed. The unit's proper-base-change route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned direct comparison is valid but longer than necessary: the adopted
source library already proves `Adjunction.derived_eq_ofNatIsoLeft` and
`Adjunction.commShift_ofNatIsoLeft`. These identify the specified constructors
and transport the existing shifts, without choosing a new shift on the right
adjoint. The canonical comparison is definitionally the existing
`leftDerivedFunctorIsoMapDerivedCategory`, so no comparison repair is needed.

The proof uses no positivity or nonzero assumptions: zero and negative shifts,
identity scheme maps and zero coefficients are covered by the generic transport
lemmas. No statement, definition or target is changed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
