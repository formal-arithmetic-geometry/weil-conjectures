# AlgebraicGeometry.Etale.etaleStalkSpecialization_naturality

## Reason

Restore the assigned quarantined module from
quarantine/Sheaf/AlgebraicGeometry/SpecializationCospecializationArrows.lean.
The rework row records its failed global build. Compiling that archive against the
current library reports `Unknown identifier
existsUnique_strictHenselizationStalkRestriction` at line 81.
The specialized restriction API was retired in favor of the generic
PointedEtaleSectionCone API. EtaleStalkSpecialization already uses the generic API.

Migrate the proof's restriction witness and its germ-component equations to
(strictLocalSectionCone s).existsUnique_restriction and
PointedEtaleSectionCone.restriction. Use strictLocalNeighbourhoodSection in the
restriction naturality square. After the global-sections comparison naturality rewrite,
close the remaining definitional equality by rfl.

All declaration signatures, attributes, public imports, docstrings and definition bodies
are identical to the quarantine archive. Only this theorem's proof changes. The canonical
arrows retain precisely their existing constructions, including the unique restriction
witness used by etaleStalkSpecialization. No source-library module is changed.

## Old

```lean
theorem etaleStalkSpecialization_naturality
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : F ⟶ G) :
    (Scheme.pointSmallEtale s).sheafFiber.map a ≫ etaleStalkSpecialization s t G =
      etaleStalkSpecialization s t F ≫
        (Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber.map a
```

The archived proof chooses existsUnique_strictHenselizationStalkRestriction, rewrites
strictHenselizationSectionRestriction, and uses strictHenselizationNeighbourhoodSection.
These three names have been retired.

## New

The signature above is unchanged. The proof chooses
(strictLocalSectionCone s).existsUnique_restriction, rewrites
PointedEtaleSectionCone.restriction, uses strictLocalNeighbourhoodSection, and ends the
component naturality calculation with rfl. Its colimit-extensionality argument, adjunction
unit naturality, sheaf naturality, global-sections comparison naturality, and final
composition with globalGerm are retained.

## Users

The repository's downstream.py reports the assigned module unknown because it is
quarantined. A source search over lean/Sheaf, lean/WeilConjectures and quarantine/Sheaf
finds these consumers. The first two publicly import the module; the third consumes
its canonical arrows transitively. No consumer statement or definition changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StrictBaseFibreMapFactorization | unclaimed | Quarantined direct importer; all signatures and arrow definitions retained; no edit. |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationCompatibility | unclaimed | Quarantined direct importer; all signatures and arrow definitions retained; no edit. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Quarantined transitive consumer; all signatures and arrow definitions retained; no edit. |

## Status

landed 20261022T011836-L-3223403 2026-10-22 (merge of deliver/F2/Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows)

The restored module compiles through lcompile.py in 18.0 seconds. The archive has zero
sorry holes and the restoration has zero; none is added, closed, moved or split off.
The original DAG attachment and dependency route are preserved. Independent delivery
review and the maintainer's global build remain responsible for landing verification.
