# AlgebraicGeometry.fibre_dimension_eq_of_specializes_component_restrict

## Reason

Retire the unused Sheaf duplicate in favour of the existing proved upstream module
`WeilConjectures.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization`.
This is the DIFFERENT twin already listed in `coord/retire-items.tsv`.
The neighbourhood theorem has an identical signature. The upstream specialization
theorem is stronger: it omits the redundant hypothesis `hx'`. Applying that theorem
with the other arguments proves the old statement, as checked in a scratch Lean file.
Both upstream theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Old

Both declarations were duplicated in
`Sheaf.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization`:

```lean
theorem exists_fibre_dimension_open_of_flat_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x : X) (hx : f x ∈ U)
    (hcomponent : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    ∃ V : X.Opens, x ∈ V ∧
      ∀ y ∈ V, topologicalKrullDimAt (f.asFiber y) =
        topologicalKrullDimAt (f.asFiber x)

theorem fibre_dimension_eq_of_specializes_component_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x x' : X) (hx : f x ∈ U) (hx' : f x' ∈ U) (hsp : x' ⤳ x)
    (hcomponent : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    topologicalKrullDimAt (f.asFiber x') = topologicalKrullDimAt (f.asFiber x)
```

## New

The Sheaf module is withdrawn and contains no declarations. Its two DAG nodes now
attach to these existing upstream signatures, respectively:

```lean
theorem exists_fibre_dimension_open_of_flat_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x : X) (hx : f x ∈ U)
    (hcomponent : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    ∃ V : X.Opens, x ∈ V ∧
      ∀ y ∈ V, topologicalKrullDimAt (f.asFiber y) =
        topologicalKrullDimAt (f.asFiber x)

theorem fibre_dimension_eq_of_specializes_component_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x x' : X) (hx : f x ∈ U) (hsp : x' ⤳ x)
    (hcomponent : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    topologicalKrullDimAt (f.asFiber x') = topologicalKrullDimAt (f.asFiber x)
```

The mathematical node statements and dependency edges are preserved. The specialization
node's proof text records the stronger upstream statement. No upstream file is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization | R8 (assigned item) | Withdraw the unused duplicate; reattach both nodes upstream. |
| WeilConjectures.AlgebraicGeometry.FlatClosedFibreInterior | unclaimed | Existing DAG parent already imports the upstream module and uses its stronger signature at both calls; compiled unchanged. |
| WeilConjectures.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization | unclaimed | Existing replacement; compiled unchanged and checked both theorem axioms. |

`tools/downstream.py` reports zero modules downstream of the Sheaf module and no
external users of either declaration through it. Direct searches also find no
importers or declaration users in `quarantine/Sheaf`. The only external DAG parent
is `lem-sbc-flat-closed-fibre-interior`, already attached to the upstream consumer
listed above. The neighbourhood node and specialization node keep their dependency
relationship and both obtain upstream attachments in this delivery. The unit
`sk-prop-normal-form` has no realized statement or step naming this module; its
route is unchanged. No consumer adaptation is needed.

## Status

landed 20261020T221339-L-4176717 2026-10-20 (merge of deliver/R8/Sheaf.AlgebraicGeometry.FlatFibreComponentDimensionSpecialization)
