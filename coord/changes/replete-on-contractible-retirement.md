# AlgebraicGeometry.Scheme.proetale_surjective_sections_of_epi_tower

## Reason

Retirement item in coord/retire-items.tsv, following the human's 2026-10-20
instruction recorded in coord/changes/retire-sheaf-twins-20261020.md.
The Sheaf module duplicates the adopted source module. The complete theorem,
from its declaration through the end of the namespace, is byte-identical in
both files: the same universes, hypotheses, two conclusions, and proof.
Both have zero holes. Keep the upstream declaration and retire only the copy.

The source proof implements the unit's prescribed route: weak contractibility
makes adjacent maps surjective on sections; recursion chooses lifts above the
specified index and uses transition maps below it; compatibility gives a tuple
identified with a section of the limit. Empty section sets and index zero need
no extra hypothesis. No unit route or target statement changes.

## Old

Sheaf.AlgebraicGeometry.ProEtaleReplete imports:

```lean
import Sheaf.AlgebraicGeometry.ProEtale.RepleteOnContractible
```

The declaration is attached to
lean/Sheaf/AlgebraicGeometry/ProEtale/RepleteOnContractible.lean.

## New

The consumer imports:

```lean
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteOnContractible
```

Delete lean/Sheaf/AlgebraicGeometry/ProEtale/RepleteOnContractible.lean via
sandbox deleted.txt. Reattach det-pe-replete-on-contractible to the existing
source declaration in
lean/WeilConjectures/AlgebraicGeometry/ProEtale/RepleteOnContractible.lean.
The name and statement of the theorem are unchanged. No upstream file changes.

The retired copy also publicly imported Sheaf.CategoryTheory.SiteCoveringAxioms.
Its sole consumer already publicly imports that module explicitly, so it retains
that interface without an additional import. All other public imports of the
copy are the source module's public imports too.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleReplete | unclaimed | Replace one private import; theorem signature and proof unchanged. |

This is the entire downstream set from tools/downstream.py with --uses
proetale_surjective_sections_of_epi_tower. A search of both Lean roots finds no
other import of the retired module. The adapted consumer's transitive import
closure has no pair Sheaf.Y and WeilConjectures.Y. The import-direction check
permits the replacement and finds no cycle.

## Status

landed 20261020T135434-L-1823527 2026-10-20 (merge of deliver/V8/Sheaf.AlgebraicGeometry.ProEtale.RepleteOnContractible)
