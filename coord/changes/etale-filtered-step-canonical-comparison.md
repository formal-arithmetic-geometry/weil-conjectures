# AlgebraicGeometry.Etale.etale_filtered_step_cohomology_compatibility

## Reason

Repair of reviewer X-ae896 E3. Bare Nonempty Iso did not determine a compatible
comparison. The explicit augmentation and total now supply a fixed comparison;
the factorization choice is unique by cancellation of a monic inclusion.
The finite-diagonal isomorphism is constructed from coproduct comparison and the
extension natural isomorphism. It contains no choice from an unproved Iso existence.

## Old

```lean
theorem etale_filtered_step_cohomology_compatibility (X : Scheme.{u}) (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) : HomologicalComplex.homologyMap (T.L.step q).arrow p ≫ (T.c p).hom = (Classical.choice (etale_filtered_step_cohomology_iso X K T p q)).hom ≫ (cohomology AddCommGrpCat.{u + 1} X p).map (DerivedCategory.Q.map (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)))
```

## New

```lean
theorem etale_filtered_step_cohomology_compatibility (X : Scheme.{u}) (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) : HomologicalComplex.homologyMap (T.L.step q).arrow p ≫ (T.c p).hom = (etaleFilteredStepCohomologyIso X K T p q).hom ≫ (cohomology AddCommGrpCat.{u + 1} X p).map (DerivedCategory.Q.map (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)))
```

Added public definition etaleFilteredStepCohomologyIso and public imports
Sheaf.AlgebraicGeometry.EtaleRestrictedTotalResolution and
Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsComparison because its exposed body
uses the actual augmentation, canonical lift, and their named properties.
Its data are homology of asIso(lift).symm followed by resolutionEtaleCohomologyIso.
All earlier public imports and both unchanged theorem signatures are retained.
No existing definition used in Challenge is changed. No target meaning changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleFilteredStepCohomology | P1 | Final proof selects the concrete comparison; compatibility statement changes as requested. |

The declaration-specific downstream search lists only the item itself as a user
of the compatibility theorem. The direct final-theorem consumer is
Sheaf.AlgebraicGeometry.EtalePresentationImageFiltration; it uses the unchanged
existential statement and compiles without adaptation. The transitive import
closure contains 237 modules; none uses the changed compatibility signature.
No module outside this item is adapted or written by this delivery.

## Status

landed 20261012T203946-L-831528 2026-10-12 (merge of deliver/P1/Sheaf.AlgebraicGeometry.EtaleFilteredStepCohomology)
