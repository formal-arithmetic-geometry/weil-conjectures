# CategoryTheory.singleton_site_module_comparison

## Reason

The complete proof needs a strong monoidal evaluation comparison and its total-tensor
comparison. Local irreducibility attributes keep elaboration from expanding the large
sheaf monoidal instance and three proved comparison constructions. The preflight's command
scan flags these attributes as a possible visibility change, so this record documents
those commands explicitly. They are local attributes, and no public construction changes.

## Old

No corresponding local attribute commands occurred after `end DerivedScalars`.
All existing public declaration signatures, definition/instance bodies and public imports
are retained verbatim. The original theorem body was `by sorry`.

## New

The added local commands are exactly:

```lean
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] punctualEvaluationMonoidal
attribute [local irreducible] punctualComplexEquivalence
attribute [local irreducible] punctualTotalTensorIso
```

The last three names are proved private constructions in this file. A standalone
`set_option backward.isDefEq.respectTransparency.types false` also controls only
elaboration of the subsequent proofs. These commands change no mathematical data and
export no global attribute. All added item declarations are private; its original public
theorem keeps its exact signature. The separately added, fully proved categorical theorem
is in `Sheaf.CategoryTheory.NormalizedDerivedAdjunctionTransport`, with its own new node.
There is no changed definition and no target meaning to reopen.

## Users

The following are all source import consumers, transitively, including the item. The
source-only dependency scan was independently checked over both library roots. No consumer
requires adaptation. Current claim holders are recorded at packet preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CoefficientSequenceGlobalSections | H3 | No adaptation: all existing definitions, signatures, instances and public imports are unchanged. |
| Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit | N1 | No adaptation: all existing definitions, signatures, instances and public imports are unchanged. |
| Sheaf.ProperBaseChange.SingletonSiteModuleComparison | C3 | Prove the original theorem using private helpers; existing interface unchanged. |
| Sheaf.RingTheory.CotangentBootstrap | unclaimed | No adaptation: all existing definitions, signatures, instances and public imports are unchanged. |
| Sheaf.RingTheory.CotangentFlatBaseChange | unclaimed | No adaptation: all existing definitions, signatures, instances and public imports are unchanged. |
| Sheaf.RingTheory.DerivedDiagonalCotangentVanishing | unclaimed | No adaptation: all existing definitions, signatures, instances and public imports are unchanged. |
| Sheaf.RingTheory.EtaleCotangentVanishing | unclaimed | No adaptation: all existing definitions, signatures, instances and public imports are unchanged. |
| Sheaf.RingTheory.KoszulQuotientCotangentVanishing | unclaimed | No adaptation: all existing definitions, signatures, instances and public imports are unchanged. |
| Sheaf.RingTheory.TorIndependentCotangentBaseChange | unclaimed | No adaptation: all existing definitions, signatures, instances and public imports are unchanged. |
| Sheaf.TraceFormula.OnePointDerivedRingIdentification | unclaimed | No adaptation: all existing definitions, signatures, instances and public imports are unchanged. |

## Status

landed 20261021T120327-L-3772964 2026-10-21 (merge of deliver/C3/Sheaf.ProperBaseChange.SingletonSiteModuleComparison)
