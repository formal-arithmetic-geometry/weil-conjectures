# AlgebraicGeometry.Scheme.etaleCohomology_isColimit_of_isDirected

## Reason

Retire the duplicate `Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit`,
as requested by its row in `coord/retire-items.tsv` and the human-approved
`coord/changes/retire-sheaf-twins-20261020.md` hand-off. The directed-index
statement already exists verbatim in the upstream twin. The filtered-index
statement already exists verbatim in its upstream extension module. The
current source has just one remaining direct importer. No upstream module,
target statement, definition, theorem signature, or mathematical route changes.

## Old

`Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit` locally declared:

```lean
theorem etaleCohomology_isColimit_of_isFiltered_coefficientSize
    (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).mapCocone c))

theorem etaleCohomology_isColimit_of_isDirected (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {I : Type (u + 1)} [PartialOrder I]
    [IsDirected I (· ≤ ·)] [Nonempty I]
    {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    Nonempty (IsColimit
      ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).mapCocone c))
```

The sole current direct consumer, `ConstantTorsionAcyclicDevissage`, had:

```lean
import Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit
```

## New

The duplicate is withdrawn using `deleted.txt`. Both displayed signatures
remain identical in the upstream library: the directed theorem is in
`WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimit`, and the
filtered theorem is in
`WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension`.
The latter publicly imports the former. Neither upstream file is modified.
The consumer changes only its proof import to:

```lean
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension
```

The DAG node `lem-weil-pbc-etale-directed-cohomology-colimit` points at the
existing upstream directed theorem. Its statement, proof, proof dependencies,
and unit route are unchanged. Its `lean.note` records the extension supplying
the general filtered-index theorem. The other node mentioning the old module
uses it only in historical `created.item` metadata, which is preserved.

## Users

Current-source inventory: `tools/downstream.py` with both declaration names
finds four downstream modules, one direct importer. No quarantined Lean source
imports the retired module. The retirement table's other listed consumers
already use upstream modules in the current source, so need no edits.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConstantTorsionAcyclicDevissage | unclaimed | Replace its proof-only import; same filtered theorem, unchanged proof and signature. |
| Sheaf.AlgebraicGeometry.LocallyConstantTorsionLocalAcyclicity | unclaimed | Transitive proof consumer; unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Transitive proof consumer; unchanged. |
| Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso | unclaimed | Transitive consumer; unchanged. |

No mathematical interface changes, so no target semantic review is reopened.
There are no forced adaptations of a module held by another group.

## Status

landed 20261020T211703-L-3488750 2026-10-20 (merge of deliver/E9/Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit)
