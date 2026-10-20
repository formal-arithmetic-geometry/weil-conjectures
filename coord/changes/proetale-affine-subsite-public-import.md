# AlgebraicGeometry.Scheme.ProEt.affineWeaklyEtale_sheafEquivalence

## Reason

The dense-subsite proof uses Mathlib directly. SiteCoveringAxioms is unnecessary
for every statement, definition and proof in this module. Remove its public
import together with the unused private proof dependencies. All existing
signatures, definitions and attributes remain identical.

## Old

```lean
public import Sheaf.CategoryTheory.SiteCoveringAxioms
```

## New

The import is removed. All other public imports remain verbatim. Private imports
of Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology and
Mathlib.AlgebraicGeometry.Cover.QuasiCompact supply the comparison proof.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence
--direct --uses IsSiteForCoverings` lists exactly the module below. The current
consumer has one textual use of IsSiteForCoverings and imports
SiteCoveringAxioms independently. The transitive downstream count is also one.
On 2026-10-21 the unchanged consumer compiled against the retained proof on the
server in 3.0 seconds; no adaptation is needed. No target statement uses any
changed definition: none changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints | unclaimed | Has its own private SiteCoveringAxioms import; no adaptation needed; original consumer compiled against the delivered module. |

## Status

landed 20261020T221211-L-4156571 2026-10-20 (merge of deliver/H2/Sheaf.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence)
