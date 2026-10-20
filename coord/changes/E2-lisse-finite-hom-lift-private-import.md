# AlgebraicGeometry.ProEtale.exists_lisse_finite_hom_lift

## Reason

Restore the quarantined module after the upstream sync moved the proved private
relative-tensor comparison to Sheaf.UpstreamExtra. The old private-proof import
cannot resolve Mod.relativeTensorRightIso; importing all declarations from its
new module restores the existing argument. No signature, definition, public
import, attribute or proof body is changed. No target meaning review is reopened.

## Old

```lean
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
```

## New

```lean
import all Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
```

The existing public import of the Sheaf.UpstreamExtra module is retained verbatim.
The ordinary importer still sees exactly the same public interface.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseFiniteHomLift | E2 | Restored private comparison access; compiles. |
| Sheaf.Paper.CoefficientFiniteDescentLisse | unclaimed (quarantined) | Its existing theorem application and import are unchanged; no adaptation required. |

The downstream.py scan reports the item as unknown because it is quarantined.
A direct source search across live Lean and the Sheaf quarantine found no live
consumer and only the archived direct consumer listed above. The archived direct
consumer is CoefficientFiniteDescentLisse, whose line 453 applies the unchanged
exists_lisse_finite_hom_lift. All transitive consumers retain the same interface.
The DAG attachment and proof dependencies remain intact. No source-library file
or quarantine archive is edited.

## Status

landed 20261020T145502-L-2400691 2026-10-20 (merge of deliver/E2/Sheaf.Paper.LisseFiniteHomLift)
