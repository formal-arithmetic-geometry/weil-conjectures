# CategoryTheory.kInjectiveHom_scalar_telescope

## Reason

The proof and statements do not use any declaration from
`Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`. The resolution functor and
augmentation are explicit parameters. Remove the unused public import to avoid
bringing unrelated derived-internal-Hom constructions into this module. The proof
uses the component projection API through a new private proof import.

## Old

```lean
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
```

The existing open command was:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

## New

The public import above is removed. The new private proof import is:

```lean
import WeilConjectures.Algebra.Homology.HomComplexComponents
```

The proof also opens the triangle API:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
```

The generic scalar-resolution and sequential-colimit helpers are before the
ringed-site variables. All additional notation and irreducibility attributes are
local. The three public definitions and the complete public theorem signature
remain verbatim. No target statement or definition changes.

## Users

`python3 tools/downstream.py Sheaf.Algebra.Homology.KInjectiveHomScalarTelescope`
reports zero downstream modules. A direct search of both library roots likewise
finds no importer. Thus there are no consumer adaptations. The unfinished parent
in the DAG still needs this theorem; this delivery preserves its attachment and
dependencies and does not withdraw it.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.KInjectiveHomScalarTelescope | H4 | Sole proof completed; unused public import removed; only private proof helpers added. |

## Status

landed 20261021T151123-L-1136553 2026-10-21 (merge of deliver/H4/Sheaf.Algebra.Homology.KInjectiveHomScalarTelescope)
