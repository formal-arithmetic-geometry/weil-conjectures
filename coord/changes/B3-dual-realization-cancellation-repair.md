# WeilConjectures.NativeDualRealization.dual_realization_comparison

## Reason

Restore the quarantined `lean/Sheaf/WeilSheaf/DualRealizationComparison.lean`
from its exact archive recorded in `coord/rework.tsv`. The recorded global-build failure
was a deterministic heartbeat timeout at archive line 634, during the final cancellation
of the realized Hom comparison and its inverse. Rewrite matching there unnecessarily
inspected the large concrete realization construction.

## Old

The final composite proof ended with:

```lean
    change ((a (op K)).hom ≫ (b (op K)).inv) ≫ (b (op K)).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
```

The archive also set:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

All original public declaration signatures and definition bodies are restored verbatim.

## New

Use a fully proved private categorical lemma, checked with abstract objects:

```lean
private theorem cancel_comparison
    {E : Type a} [Category.{b} E] {A B C : E} (i : A ≅ C) (j : B ≅ C) :
    (i.hom ≫ j.inv) ≫ j.hom = i.hom := by
  rw [Category.assoc, j.inv_hom_id, Category.comp_id]
```

The concrete proof now ends with:

```lean
    change ((a (op K)).hom ≫ (b (op K)).inv) ≫ (b (op K)).hom = _
    exact cancel_comparison (a (op K)) (b (op K))
```

Remove both transparency-disabling options. No definition, public signature, public
import, instance, or exported attribute changes. No mathematical node changes are needed:
the same inverse cancellation implements the existing third proof step. No target's
meaning changes. The profiled repair compiled in 47.6 seconds; development profiling
options are removed from the delivered file.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.WeilSheaf.DualRealizationComparison | B3 (this assignment) | Restored and repaired. |

An exact direct-import search over `lean/` and `quarantine/` finds no importers of this
module. Its DAG attachment and all proof dependencies remain intact. No consumer edits
or other-module adaptations are required.

## Status

landed 20261026T180817-L-3403424 2026-10-26 (merge of deliver/B3/Sheaf.WeilSheaf.DualRealizationComparison)
