# WeilConjectures.OpenTensorQuotient.ScalarCompatibility

## Reason

The assigned evaluation lemma is false for arbitrary independent finite and system isomorphisms: sign-twist just one comparison over a nonzero coefficient module (for example the identity open over a point with l=3). Naturality and invertibility do not force its normalization. This is not repaired by assuming its conclusion or by moving the hole.

The actual strict quotient argument needs only finite and sections. The proved scalar-unit equation projects exactly those fields; ScalarComparison.iso supplies all quotient transitions, and ScalarComparison.components supplies every finite component formula. No consumer projects systems or evaluation. Prune those surplus auxiliary fields and the false evaluation item. Construct the retained normalized finite data directly from the proved generic openScalarComparison, using o.projections for the ring square and cancelling its generator equation with the inverse comparison. The unit route sk-prop-sf-pf-coherence and its realized nodes are unchanged. No source-library declaration or target signature is edited. Target statement definitions do not mention ScalarCompatibility; this change concerns auxiliary witnesses inside proofs. The independent reader should confirm this boundary and the consumer audit.

## Old

```lean
structure ScalarCompatibility where
  finite : ∀ n : ℕ,
    IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o
  sections : ∀ (n : ℕ) (M : normalizedDVRModules l E U n) (V : X.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
    ((finite n).hom.app M).val.app (op V)
      (IntegralOpenReduction.finiteExtensionSection l E j o n M V a x) =
    IntegralOpenReduction.extensionSection l E j o
      ((scalarReductionRestriction l E U n).obj M) V a x
  systems : (IntegralOpenReduction.systemExtension l E j o).mapHomologicalComplex (.up ℤ) ⋙
      forgetSystems l E X ≅ forgetSystems l E U ⋙ extendTower l E j o
  evaluation : ∀ (C : CochainComplex (coefficientSequenceModules l E U) ℤ)
    (n : ℕ) (i : ℤ),
    HEq (((systems.hom.app C).app (op n)).f i)
      ((finite n).hom.app ((coefficientSequenceEvaluation l E U n).obj (C.X i)))
```

## New

```lean
structure ScalarCompatibility where
  finite : ∀ n : ℕ,
    IntegralOpenReduction.finiteExtension l E j o n ⋙ scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o
  sections : ∀ (n : ℕ) (M : normalizedDVRModules l E U n) (V : X.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject j)
    (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
    ((finite n).hom.app M).val.app (op V)
      (IntegralOpenReduction.finiteExtensionSection l E j o n M V a x) =
    IntegralOpenReduction.extensionSection l E j o
      ((scalarReductionRestriction l E U n).obj M) V a x
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenFactorQuotientRealization | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenQuotientScalarComparisonAssembly | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenQuotientScalarComparisonExistence | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenQuotientScalarComparisonLevelData | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenQuotientScalarComparisonTransition | R1 | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData | unclaimed | Construct the two retained fields directly from the proved generic open/scalar comparison. |
| Sheaf.SixFunctors.OpenQuotientScalarEvaluationCompatibility | R3 | Assigned R3 module withdrawn; its sole parent no longer imports or cites it. |
| Sheaf.SixFunctors.OpenQuotientScalarFiniteCompatibility | R4 | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenQuotientScalarSectionCompatibility | S1 | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenQuotientScalarSystemsCompatibility | S2 | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenTensorQuotientCochains | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenTensorQuotientCoefficientComparisons | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenTensorQuotientData | unclaimed | Remove unused systems/evaluation fields; finite, sections and ScalarComparison are unchanged. |
| Sheaf.SixFunctors.OpenTensorQuotientGeometry | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenTensorQuotientRoosNormalization | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |
| Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility | unclaimed | Same scalar-unit and strict-tower proofs; remove obsolete system-assembly claim from the docstring. |
| Sheaf.SixFunctors.RationalOperationsData | unclaimed | Uses only finite/sections or passes the record to another theorem; unchanged source compiles against the smaller record. |

The three other G7 helpers (finite, section and systems compatibility) stay in the library and are not edited; their modules leave this target route when their sole importing constructor stops importing them. The withdrawal is supported by the replacement constructor proof and by the parent DAG updates in this same packet. The withdrawn item has exactly one DAG parent, lem-sf-open-quotient-scalar-compatibility-data; quarantined sources were also searched.

## Status

landed 20261028T020709-L-2538604 2026-10-28 (merge of deliver/R3/Sheaf.SixFunctors.OpenQuotientScalarEvaluationCompatibility)
