# EtaleGraphInterchangeData public presentation import

## Reason

The repaired OpenShrink proof uses EtaleGraphShrinkMiddlePasting. Its definition
imports reach EtaleGraphInterchangeData, whose current public import of
EtaleGraphComparisonBaseChange leads through EtalePairwiseProductGraphNormalization
back to OpenShrink. Removing the returned SidePasting import does not remove this
second cycle. InterchangeData needs the existing presentation definitions, not the
BaseChange coherence theorem. Replace that one public import. Every declaration,
signature, attribute and definition body in InterchangeData stays verbatim.

Rechecked this necessity after the return of 0d6fba0bd4f. The item now proves the side
calculation itself from the exchange cube and imports only MiddlePasting for the
intersection calculation. It has no import or DAG dependency on SidePasting.

The lost theorem export has two external textual consumers. OpenSupportCompactificationNaturality
already imports BaseChange directly and needs no edit. SfGraphCompactSupportCompositionBaseChange
needs a direct proof import; the original source against the narrowed imports reports unknown
identifier etaleGraphComparisonBaseChange, including at line 457. The original source with only this import addition compiled once in 44.2 seconds,
but failed the complete batch at 96 seconds. Profiling with the terminal private identity
cancellation optimized took 59.8 seconds and showed about nine seconds in the two
normalized proper-pasting rewrites. Use direct identity laws after left-associating
the composition word, and ordinary rw instead of erw for those two equations.
The DiagramPullback relocation and graph_chosenExact_comp proof and option changes
are dropped. Both supporting modules are unclaimed in current claim records. The final consumer compiles without profiling or warnings
in 53.3 seconds; all three unchanged direct importers also passed the batch check.

The definition node receives the matching dependency-only correction from the coherence
theorem to the presentation definition node, with its seven citers preserved and checked.
No target statement or mathematical definition changes.

## Old

In lean/Sheaf/AlgebraicGeometry/EtaleGraphInterchangeData.lean:

```lean
public import Sheaf.AlgebraicGeometry.EtaleGraphComparisonBaseChange
```

In lean/Sheaf/AlgebraicGeometry/SfGraphCompactSupportCompositionBaseChange.lean:

```lean
import Sheaf.AlgebraicGeometry.EtaleGraphComparisonInterchange
```

## New

In lean/Sheaf/AlgebraicGeometry/EtaleGraphInterchangeData.lean:

```lean
public import Sheaf.AlgebraicGeometry.EtaleGraphPresentation
```

In lean/Sheaf/AlgebraicGeometry/SfGraphCompactSupportCompositionBaseChange.lean:

```lean
import Sheaf.AlgebraicGeometry.EtaleGraphComparisonInterchange
import Sheaf.AlgebraicGeometry.EtaleGraphComparisonBaseChange
```

The final two lines of private elementaryInterchange_normalization change from

```lean
  erw [Category.comp_id, Category.comp_id]
```

to

```lean
  simp only [← Category.assoc]
  exact (Category.comp_id _).trans (Category.comp_id _)
```

Also in diagramRawInterchange_baseChange, replace exactly

```lean
  erw [reassoc_of% hp]
  erw [← nc]
```

with

```lean
  rw [reassoc_of% hp]
  rw [← nc]
```

These changes prevent rewrite matching from unfolding the large derived-functor
expressions while searching for the terminal identities and normalized pasting equations.
No profiling options are delivered. All definitions and
existing signatures remain verbatim; the public theorem proof remains verbatim.

## Users

The first three rows are all direct importers from tools/downstream.py --direct.
The next two rows are all external textual users of etaleGraphComparisonBaseChange
found by rg in both Lean roots. The theorem has no global attributes or instances;
all InterchangeData declarations remain verbatim, so transitive users keep their
mathematical interfaces. No adopted source-library module is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleGraphComparisonInterchange | unclaimed | Uses unchanged definitions and its existing pasting theorems; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleGraphNeighborhoodGeometry | unclaimed | Uses unchanged definitions and pullback geometry; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleGraphProductGeometry | unclaimed | Already publicly imports pairwise normalization; no source edit. |
| Sheaf.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange | unclaimed | Add the direct proof import of BaseChange and optimize the private terminal identity cancellation and two normalized pasting rewrites; every definition, signature and the public theorem proof remains verbatim. |
| Sheaf.SixFunctors.OpenSupportCompactificationNaturality | unclaimed | Already imports BaseChange directly; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleGraphComparisonOpenShrink | D5 | Uses MiddlePasting and proves side pasting directly, without either import cycle. |

## Status

landed 20261026T081423-L-1954771 2026-10-26 (merge of deliver/D5/Sheaf.AlgebraicGeometry.EtaleGraphComparisonOpenShrink)
