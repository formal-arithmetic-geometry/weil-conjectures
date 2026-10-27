# Sheaf.Paper.CondensedCompositorRealization: construction extraction

## Reason

The parent theorem needs four independent coherence steps, while those steps need
the actual construction declarations in their signatures. Moving the unchanged
construction layer to a data module avoids import cycles and makes each remaining
hole a strictly smaller public theorem.

## Change

`Sheaf.Paper.CondensedCompositorRealizationData` contains the original public
constructions and proved helpers with unchanged signatures and non-theorem bodies.
`Sheaf.Paper.CondensedCompositorRealization` publicly imports that module and
assembles the final `Laws` proof. Four new theorem modules contain the named
remaining holes and their DAG nodes.

The data module removes four unused direct imports listed in `report.md`; their
source declarations remain available elsewhere in the library. No existing module
outside this item is adapted.

## Verification

`lcompile.py --all` compiled all six sandbox modules in import order. The parent
statement and construction signatures are unchanged.

The upstream `ShriekComposition` source was quarantined on the worker's rework base and
was restored to the library on 2026-10-28 (fd9ee31c1ee). `Sheaf.Paper.RestoredLowerShriekComposition`
therefore re-exports `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition`
and declares only the abbreviation `condensedLowerShriekComp_padicAlgCl` of the library
`boundedConstructibleLowerShriekComp_padicAlgCl` (reviewer FIX): a second declaration under the
same name would clash with the library one in any module importing both. `condensedCompositor`
uses the abbreviation, recorded by `def-pur-restored-lower-shriek-composition`; no upstream source
module is modified.

## Old

The item module contained the construction declarations, the final compositor
theorem, and the direct import of the quarantined lower-shriek composition source.
The four coherence conclusions were still proof holes in that monolithic module.

## New

`Sheaf.Paper.CondensedCompositorRealizationData` contains the unchanged
construction layer, while the item module assembles the final theorem from that
layer and four strictly smaller theorem statements. The concrete lower-shriek
composition is the library's `ShriekComposition` definition, re-exported and named
`condensedLowerShriekComp_padicAlgCl` by `Sheaf.Paper.RestoredLowerShriekComposition`. The public signatures of the
retained declarations are unchanged.

## Users

The item module imports the data module and the four new theorem modules. The
new data module imports the restored lower-shriek definition. These are all new
modules in this delivery; no existing source-library module is adapted. The
parent theorem retains its public signature and now resolves the construction
through the data module, while the four theorem modules expose the smaller
statements recorded in their DAG nodes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CondensedCompositorRealization | P7 | Assembly imports the extracted data and theorem statements. |
| Sheaf.Paper.CondensedCompositorRealizationData | P7 | Supplies the unchanged construction declarations. |
| Sheaf.Paper.RestoredLowerShriekComposition | P7 | Re-exports the library composition and names it for the data module. |
| Sheaf.Paper.CondensedCompositorIntegralLaws | P7 | Exposes one remaining integral-law statement. |
| Sheaf.Paper.CondensedCompositorIntegralRefinement | P7 | Exposes one remaining refinement statement. |
| Sheaf.Paper.CondensedCompositorRealizationSquare | P7 | Exposes one remaining square statement. |
| Sheaf.Paper.CondensedCompositorSystemIndependence | P7 | Exposes one remaining system-independence statement. |

## Status

landed 20261027T210200-L-1668455 2026-10-27 (merge of deliver/P7/Sheaf.Paper.CondensedCompositorRealization)
`condensedCompositorRealization` proof is complete; the four smaller theorem
statements remain intentionally split for later workers. The lower-shriek
composition is the library definition, re-exported under an abbreviation.
