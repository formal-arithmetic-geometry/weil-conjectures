# AlgebraicGeometry.derivedPullback_tensor_preserve_QCoh

## Reason

Restore the assigned quarantined module after the upstream synchronization. The archive
imports the retired Sheaf derived-pullback module alongside the adopted source affine
pullback theorem, causing the recorded duplicate derivedPullback declaration error.
The adopted source already supplies the same fully qualified theorem and complete proof.
Publicly re-export it instead of redeclaring it or importing incompatible twins.
This restores the assigned interface; it is neither withdrawal nor a compiling no-op.

The archived and adopted signatures differ only in IsAcyclicTensorKFlat versus
IsKFlatTensor. These have identical definition bodies: total tensor with any acyclic
complex is acyclic, with the same tensor order and sheaf monoidal structure.
A server-compiled example with the archived predicate body checks the entire former
conjunction by exact derivedPullback_tensor_preserve_QCoh f. The source theorem's
axioms are exactly propext, Classical.choice, Quot.sound.

## Old

```lean
theorem derivedPullback_tensor_preserve_QCoh {X Y : Scheme.{uX}} (f : X ⟶ Y)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings Y.toRingedSpace))] :
    (∀ E : schemeDerivedCategory Y, schemeDerivedQCohProperty Y E →
      schemeDerivedQCohProperty X ((derivedPullback f).obj E)) ∧
    (∀ P N : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P →
      schemeDerivedQCohProperty X (DerivedCategory.Q.obj P) →
      schemeDerivedQCohProperty X (DerivedCategory.Q.obj N) →
        schemeDerivedQCohProperty X
          (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N (curriedTensor _))))
```

## New

Publicly re-exported from WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh:

```lean
theorem derivedPullback_tensor_preserve_QCoh {X Y : Scheme.{uX}} (f : X ⟶ Y)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings Y.toRingedSpace))] :
    (∀ E : schemeDerivedCategory Y, schemeDerivedQCohProperty Y E →
      schemeDerivedQCohProperty X ((derivedPullback f).obj E)) ∧
    (∀ P N : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) P →
      schemeDerivedQCohProperty X (DerivedCategory.Q.obj P) →
      schemeDerivedQCohProperty X (DerivedCategory.Q.obj N) →
        schemeDerivedQCohProperty X
          (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N (curriedTensor _))))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh | R3 | Restore the assigned module with the canonical theorem; zero local holes. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed in repository; quarantined | Direct archived importer uses only the unchanged pullback conjunct; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportBase | unclaimed in repository; quarantined | Direct archived importer uses only the unchanged pullback conjunct; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnion | unclaimed in repository; quarantined | Direct archived importer uses only the unchanged pullback conjunct; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorPullback | unclaimed in repository; quarantined | Direct archived importer uses only the unchanged pullback conjunct; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed in repository; quarantined | Direct archived importer uses only the unchanged pullback conjunct; no adaptation. |

There are no live direct importers of the quarantined Sheaf module. The prescribed
downstream.py command reports unknown module because its source is quarantined;
searching both lean and quarantine finds exactly the five direct importers above.
All five calls use the first conjunct, whose signature is unchanged. Other archived
callers receive the theorem transitively and likewise use its first conjunct.
Live source-library callers already import the canonical theorem and remain unchanged.
No definition or source-library declaration is changed. No target statement changes.

The node keeps its original Sheaf module/file attachment, mathematical statement,
proof, proof_deps and unit. Its recorded Lean signature is refreshed to the canonical
predicate spelling exported by the restored module. Both affine cohomology nodes
remain required: the adopted theorem still uses them. No parent or unit is pruned.
The quarantine archive is untouched and deleted.txt is not used.

## Status

landed 20261020T221330-L-4175236 2026-10-20 (merge of deliver/R3/Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh)
