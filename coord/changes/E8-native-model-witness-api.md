# CategoryTheory.ringedDerived_closed_symmetric_monoidal

## Reason

The existing proof of `CategoryTheory.ringedDerived_closed_symmetric_monoidal`
constructs exactly the native monoidal structure, native tensor representative comparison,
and native Koszul symmetry. Its public statement forgets those identifications. The
constant-coefficient tensor assertion fixes those same native structures, so reconstructing
this entire coherence witness duplicates an existing proof and repeatedly checks its
large dependent tensor types.

Retain the identifications in a proved private helper beside the original construction,
and obtain the original public theorem by forgetting them. Reuse that helper through a
private proof import in `ConstantNativePullbackMonoidal`. The construction remains in its
original module; the duplicated construction is removed from the new module.

## Old

`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`, currently unclaimed,
contains the complete native coherence construction in the proof of
`CategoryTheory.ringedDerived_closed_symmetric_monoidal`. Its signature, definitions,
attributes, and public and private imports are preserved verbatim.

```lean
theorem ringedDerived_closed_symmetric_monoidal :
    ∃ S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R),
      ∃ T : CoefficientTensorModels.{u, c, v, w} J R S,
        ∃ β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
          _ S.monoidal,
          Nonempty (RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
```

## New

A proved private helper,
`CategoryTheory.ringedDerived_closed_symmetric_monoidal_native`, retains the same
witness together with its monoidal equality, symmetry identification, and native
representative comparison equation. Its proof is the existing native construction;
the additional identifications are reflexivity and the already proved representative
comparison equation. The original public theorem applies the helper and forgets these
identifications.

```lean
private theorem ringedDerived_closed_symmetric_monoidal_native :
    ∃ S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R),
      S.monoidal = RingedDerivedNative.monoidal.{c, v, u, w} J R ∧
      ∃ T : CoefficientTensorModels.{u, c, v, w} J R S,
        ∃ β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
          _ S.monoidal,
        ∃ _hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β,
          HEq β (RingedDerivedNative.symmetric.{c, v, u, w} J R) ∧
          (∀ (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
            (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
            HEq (T.iso J R S P Q hP hQ)
              (RingedDerivedNative.tensorIso.{c, v, u, w} J R P Q (Or.inl hP)))
```

`Sheaf.Paper.ConstantNativePullbackMonoidal` imports that private proof API and replaces
its duplicate native-model construction by direct applications of the retained witness API. No definition is changed, no public
signature changes, and no proof hole is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal | unclaimed | Retain witness properties in a private helper; preserve the public statement. |
| Sheaf.Paper.ConstantNativePullbackMonoidal | E8 (new) | Reuse the existing construction with its native identifications. |
| Sheaf.Paper.CompletedTensorUnitInsertionData | E8 (new) | Unchanged public import of the original module. |
| Sheaf.Paper.CompletedTensorUnitInsertion | E8 | Unchanged application of the normalized comparison theorem. |
| Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel | unclaimed | Public theorem, instances and all definition bodies are unchanged; no adaptation. |
| Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete | unclaimed | Public theorem, instances and all definition bodies are unchanged; no adaptation. |
| Sheaf.Algebra.Homology.ScalarInternalHomAdjunction | unclaimed | Public theorem, instances and all definition bodies are unchanged; no adaptation. |
| Sheaf.Algebra.Homology.SitePerfectScalarHomComparison | unclaimed | Public theorem, instances and all definition bodies are unchanged; no adaptation. |
| Sheaf.CategoryTheory.FiniteFreeCompletionTransport | unclaimed | Public theorem, instances and all definition bodies are unchanged; no adaptation. |
| Sheaf.CategoryTheory.RingedSiteDualityMaps | U7 | Public theorem, instances and all definition bodies are unchanged; no adaptation. |
| Sheaf.Paper.FiniteProjectiveTensorProducts | unclaimed | Public theorem, instances and all definition bodies are unchanged; no adaptation. |
| Sheaf.Paper.RingedPushforwardCompletion | unclaimed | Public theorem, instances and all definition bodies are unchanged; no adaptation. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange | unclaimed | Public theorem, instances and all definition bodies are unchanged; no adaptation. |

`tools/downstream.py` lists these ten actual text users of the public theorem, including
the defining module. The 2,040 transitive importers keep the identical public interface.

Existing public consumers keep the same declarations, signatures, instances, and imports.
No forced adaptation is needed. The original coherence node keeps the same proof dependencies;
its native construction has not changed. The new native pullback node records the reused
coherence module as its proof dependency.

## Status

landed 20261022T025322-L-1275852 2026-10-22 (merge of deliver/E8/Sheaf.Paper.CompletedTensorUnitInsertion)
