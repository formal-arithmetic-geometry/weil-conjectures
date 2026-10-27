# CategoryTheory.CondensedDerivedRestriction.internalInflationStructure

## Reason

Restore the assigned quarantined module `Sheaf.CategoryTheory.InternalInflationGradedCup`.
The current rework row records a failure after upstream sync 58206abfd. Compiling the
archived source reproduces its line 145 error:

```text
failed to synthesize instance of type class
  BraidedCategory (DerivedCategory (Modules A))
```

Upstream now provides `DerivedCategory.braidedCategory'` as an explicitly selected
canonical Koszul braiding, rather than a global instance. Its documentation directs
consumers to use it locally. The braided inflation assertion needs this braiding
on both the base and action derived categories.

## Old

The archive has the following context immediately before `internalInflationStructure`:

```lean
section ProfiniteGroup
variable [hCompact : CompactSpace G] [hHausdorff : T2Space G]
  [hDisconnected : TotallyDisconnectedSpace G]
include hCompact hHausdorff hDisconnected
```

The existential in the theorem is unchanged:

```lean
    (∃ b : (trivialDerived A G).Braided,
      b.toMonoidal = derivedTrivialMonoidal (A := A) (G := G)) ∧
```

It previously relied on an automatically available derived braiding.

## New

Enclose the existing `ProfiniteGroup` section in this context:

```lean
section CanonicalBraiding

-- The upstream derived braiding is a definition, so select its canonical Koszul
-- normalization explicitly for the braided inflation assertion below.
attribute [local instance] DerivedCategory.braidedCategory'
```

Close `CanonicalBraiding` immediately after `end ProfiniteGroup`. This selects the
upstream canonical derived braiding for both categories in `internalInflationStructure`.
It adds no instance parameters to that theorem. Every original declaration, definition
body, theorem statement, docstring and import is retained verbatim from the quarantine
archive. No attribute is exported. The four archived proof holes are retained, with
no additional holes. The node attachment, mathematical statement and proof plan stay
unchanged; no target definition or target statement is modified.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.InternalInflationGradedCup` | A2 | Restored with canonical local derived braidings. |

`tools/downstream.py` cannot resolve a module absent from `lean/`. An explicit import
scan of every Lean source in both `lean/` and `quarantine/` finds no direct importers.
A scan of all DAG statement dependencies, proof dependencies and proof-step uses finds
the parent `lem-sfb-internal-bar-character-roof-cup`; its dependency is preserved.
No consumer adaptation or withdrawal is requested. The unchanged unit route is
`sk-thm-sf-ctf-stability`, whose realized lists do not prescribe an alternative here.

## Status

landed 20261023T120510-L-620672 2026-10-23 (merge of deliver/A2/Sheaf.CategoryTheory.InternalInflationGradedCup)
