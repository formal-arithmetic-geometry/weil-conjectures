# SheafOfModules.ringIso_tensor_transport

## Reason

Complete the assigned tensor-transport proof without changing its statement. Private generic
helpers avoid repeated elaboration of concrete sheaf tensors. Local reducibility settings
control elaboration of concrete sheaf tensors. A proved private existential package keeps
the native derived monoidal data abstract in the final scalar comparison.
The conservative interface check counts these file-level commands. They export no new
instance, notation, attribute or public import. The separate definitionally identical cache-constructor repair is documented in
`ringIsoCochainMonoidalExplicit.md`.

## Old

```lean
theorem ringIso_tensor_transport (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)] :
    Nonempty (RingIsoTensorTransport c)
```

The theorem body was `by sorry`. All public structures, instances, definitions and imports
preceding it already existed.

## New

```lean
theorem ringIso_tensor_transport (c : R ≅ S)
    [HasDerivedCategory.{wR} (scalarModules J R)]
    [HasDerivedCategory.{wS} (scalarModules J S)] :
    Nonempty (RingIsoTensorTransport c)
```

The proof assembles the actual restriction equivalence, normalized ordinary tensor and unit,
termwise tensor comparison, acyclicity, flatness, K-flatness and native derived comparison.
New helper declarations in this module are private. Their data are explicit constructions.
The generic signed-summand proof is private and follows the existing source proof.
The added noncomputable section, generic variables and opens support these private helpers.
All changed reducibility attributes are local. The scalar-extension comparison is locally
irreducible after its insertion and inverse formulas are proved. The native scalar-extension
functor and its tensor comparison are used through their existing APIs. File-local transparency options control elaboration without changing public data. The private proof section reduces
`synthInstance.maxSize` to 256; the derived proof explicitly unfolds its proposition and
uses the proved native-data package through its abstract witnesses. A private abstract constructor avoids
repeating inverse-tensor unit coherence at concrete sheaf tensors. A private tensor-predicate
transport lemma handles the K-flat test through an abstract monoidal equivalence. Existing public signatures, attributes and public imports remain verbatim. The
separate cache-constructor record documents the existing definition-body edits. The new public generic localization-square theorem belongs to its
own new Sheaf module and node. No target statement or meaning changes.

## Users

Read-only `tools/downstream.py` lists these twelve consumers. Three mention the theorem directly;
the other nine import it transitively. None uses any new private helper or local command.
All original consumer files remain applicable to exactly the same public declarations;
no consumer is adapted in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingIsomorphismTensorTransport | P3 | Private proof helpers and completed theorem. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Public interface unchanged. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Public interface unchanged. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Public interface unchanged. |
| Sheaf.Paper.CoefficientPointFlatKFlatComparison | unclaimed | Uses the theorem; signature unchanged. |
| Sheaf.Paper.ExternalRHomConePairing | unclaimed | Public interface unchanged. |
| Sheaf.Paper.ExternalRHomSignedCones | unclaimed | Public interface unchanged. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | unclaimed | Public interface unchanged. |
| Sheaf.Paper.FiniteFreeConstructibleScalarTransport | unclaimed | Uses the theorem; signature unchanged. |
| Sheaf.Paper.GlobalHomEvaluationFlatLift | unclaimed | Public interface unchanged. |
| Sheaf.Paper.PerAdicCommonStageTruncations | unclaimed | Public interface unchanged. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Public interface unchanged. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | K4 | Uses the theorem; signature unchanged. |

## Status

landed 20261022T011908-L-3230116 2026-10-22 (merge of deliver/P3/Sheaf.Algebra.Homology.RingIsomorphismTensorTransport)
