# proEtaleConstantRingPullbackComposition

## Reason

The stalk-coherence proof exceeded the 60-second single-file compile limit when
it unfolded the normalized derived compositor and its nested chosen witnesses.
Keep this exact construction but mark its body `@[no_expose]`, and expose its
identical defining formula as the proved theorem
`proEtaleConstantRingPullbackComposition_eq`.

In the unclaimed `ProEtaleDerivedPullbackCoherence`, replace the one explicit
unfolding with this equation, and remove its local `irreducible` attribute for the
now-hidden definition. Add the proved public characterization
`proEtaleConstantRingPullbackComposition_ordinary`: an ordinary comparison,
its formula on actual adjunction unit sections, and the identification of its
exact-derived image with the existing compositor. The witnesses are the already
uniquely normalized witnesses used by that module. No new choice or axiom is added.
Private proved helpers derive the actual adjunction's normalization and the
conjugate-unit formula. Add the proved public specialization
`proEtaleConstantRingPullback_underlyingUnit_isIso` of the existing private
`ringUnitComparison`. This lets the item remove its `import all` of the large
adjunction module and use only its public unit-comparison interface.

The item's proof uses this abstract characterization instead of importing the
private chosen comparison data. All existing public signatures and definition
bodies are unchanged. The export-transparency change is flagged for independent
review; its defining equality verifies the unchanged mathematical formula.

The returned packet also restored an optimized IteratedWeilMap, whose three
public imports are now quarantined. That ancillary restoration is omitted from
this repair. Neither its archived source nor its Lean attachment or dependencies
is altered. Current consumers are checked against the interface; quarantined
modules remain the responsibility of their rework assignments.

## Old

```lean
noncomputable def proEtaleConstantRingPullbackComposition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A k ⋙
        proEtaleConstantRingDerivedPullback A h ≅
      proEtaleConstantRingDerivedPullback A (h ≫ k) :=
  (proEtaleCanonicalPullbackComposition h k
    (proEtaleConstantRing V A) (proEtaleConstantRing W A)
    (proEtaleConstantRing Z A)
    (proEtaleConstantRingComparison k A)
    (proEtaleConstantRingComparison h A)).symm ≪≫
    eqToIso (congrArg (fun c ↦
      proEtaleRingDerivedPullback (h ≫ k)
        (proEtaleConstantRing V A) (proEtaleConstantRing Z A) c)
      (proEtaleConstantRingCompositeCoefficients_eq h k A))
```

## New

```lean
@[no_expose] noncomputable def proEtaleConstantRingPullbackComposition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A k ⋙
        proEtaleConstantRingDerivedPullback A h ≅
      proEtaleConstantRingDerivedPullback A (h ≫ k) :=
  (proEtaleCanonicalPullbackComposition h k
    (proEtaleConstantRing V A) (proEtaleConstantRing W A)
    (proEtaleConstantRing Z A)
    (proEtaleConstantRingComparison k A)
    (proEtaleConstantRingComparison h A)).symm ≪≫
    eqToIso (congrArg (fun c ↦
      proEtaleRingDerivedPullback (h ≫ k)
        (proEtaleConstantRing V A) (proEtaleConstantRing Z A) c)
      (proEtaleConstantRingCompositeCoefficients_eq h k A))
```

The new equality theorem has precisely this old defining formula as its right
side, proved by unfolding in the defining module. Public imports are unchanged.

## Users

Current direct importers and the additional textual user of the compositor are
listed below. Unchanged consumers are checked as temporary sandbox probes and
are not restored or modified by this delivery. No adopted source module changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison | unclaimed | Hide the unchanged compositor body and add its proved defining equation. |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence | unclaimed | Use the equation, remove the inapplicable local irreducibility attribute, and add both proved ordinary-comparison and underlying-unit interfaces. |
| Sheaf.AlgebraicGeometry.ProEtaleConstantModuleComparisonLocalization | unclaimed | Forced adaptation: replace the removed reducibility attribute and explicit unfolding with the defining-equation theorem. |
| Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence | G8 | Prove all coherence clauses through the characterization. |
| Sheaf.Paper.PullbackCoefficientIterateCoherence | unclaimed | Unchanged direct importer and compositor user. |
| Sheaf.Paper.IntegralFinitePullbackComposition | unclaimed | Unchanged direct importer and compositor user. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | M3 | Unchanged transitive importer and compositor user. |
| Sheaf.Paper.TateInverseLimitBaseChange | unclaimed | Unchanged direct importer; no mathematical data changes. |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | X7 | Unchanged direct importer; no mathematical data changes. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite | D5 | Unchanged transitive importer; definitions and statements have identical meaning. |
| Sheaf.AlgebraicGeometry.FrobeniusStalkTrivializationNormalization | unclaimed | Unchanged transitive importer; definitions and statements have identical meaning. |
| Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback | unclaimed | Unchanged transitive importer; definitions and statements have identical meaning. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection | unclaimed | Unchanged transitive importer; definitions and statements have identical meaning. |
| Sheaf.CategoryTheory.FilteredDerivedOperationLifts | unclaimed | Unchanged transitive importer; definitions and statements have identical meaning. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | Unchanged transitive importer; definitions and statements have identical meaning. |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | E8 | Unchanged transitive importer; definitions and statements have identical meaning. |

Sheaf.Paper.IteratedWeilMap and the other quarantined consumers retain their
archives, attachments, and dependencies. The return's missing sources are not
restored and no withdrawn stub is delivered. Target mathematical meanings are
unchanged; the independent reader checks the transparency interface change.

## Status

landed 20261020T233146-L-900134 2026-10-20 (merge of deliver/G8/Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence)
