## What changed

In `Sheaf.Paper.DerivedInternalHomFilteredColimit`, proved
`WeilConjectures.SfbHomFilteredColimit.scalarComparison_existsUnique` in full, with
its existing signature and normalization. The proof extends local Hom sections
on slices, descends through the locally bijective sheafification unit, transposes
through the ordinary coefficient adjunction, and lifts through the Hom-product
limit. The signed differential calculation supplies the chain map. Bilinearity
gives the normalization for arbitrary scalar tensors; generator and projection
extensionality give uniqueness. All added private helpers are proved.

The construction handles arbitrary independent site and coefficient universes,
unbounded complexes, and zero rings or modules. It uses no finite-free basis,
flatness or continuity assumption. It does not choose data from a mere unproved
existence assertion.

`homValue` now calls the canonical projection API directly, as detailed in
`coord/changes/sfbHomValueProjection.md`. `HomComplexComponents` consequently
becomes a public import. A private import of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` supplies the
sheaf condition on slices. The old private projection-equality helper is removed,
and the existing scalar extensionality and component proofs use the API directly.
The ordinary-adjunction unit proof uses `simpa ... using!` to handle its dependent
coercions. No other module is changed.

The DAG's step 10 and proof origin record the implemented existence/uniqueness
argument. The remaining proof plans and their dependencies are preserved.

## Proved and sorry left

Closed one of the five original holes:
`WeilConjectures.SfbHomFilteredColimit.scalarComparison_existsUnique`.
Added zero holes and split off zero statements.

The four remaining original holes, all at node
`lem-sfb-dc-hom-filtered-colimit`, are:

- `WeilConjectures.SfbHomFilteredColimit.comparison_existsUnique`;
- `WeilConjectures.SfbHomFilteredColimit.filteredColimit_comparison`;
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_quasiIso`;
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_restriction`.

Their signatures and `sorry` bodies are unchanged. This is a partial proof
delivery, not a decomposition that relocates a hole. The strict scalar
naturality theorem now uses the proved comparison existence result.

The complete module compiled cleanly through `lcompile.py`, without warnings,
in 33.7 seconds in the final check (49.1 seconds with the former
projection implementation). The delivery tool performs the final checks.

## No longer needed

No public module or DAG dependency is pruned: the four remaining original
arguments still need their recorded dependencies. No import is removed.
The private `coefficientHomComponent_eq` helper is unnecessary because
`homValue` directly uses the projection it identifies. The new scalar existence
proof itself does not need the derived scalar-adjunction existence theorem,
tensor-Hom total-complex adjunction, finite-free presentations, filtered colimit
exactness, or K-flatness; these remain relevant to the unproved invertibility
and restriction parts.

## Where the brief, the DAG or earlier work was wrong

The existing mathematical statement and scalar evaluation formula are correct.
The private scalar extensionality proof unfolded the old coefficient projection
representation instead of using its product-projection API, making it sensitive
to elaboration of nested choices. The direct API avoids this and the associated
kernel conversion cost. No target is weakened and no public signature changes.

The available total-tensor/single-complex isomorphism is
`CochainComplex.mapBifunctorSingle₁Iso` in
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`; it may help the
remaining coefficient-tensor and scalar-restriction arguments. It is not imported
by this delivery because the proved scalar existence result does not use it.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
