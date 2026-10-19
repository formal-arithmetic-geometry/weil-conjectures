# Sheaf.Paper.FiniteWindow public imports

## Reason

The finite-window argument uses the canonical truncation and cohomology APIs directly.
It does not use `IsSequentialHomotopyColimit` or the many extra imports of its module.
Removing the public import avoids exposing that unrelated API through FiniteWindow.
Every existing declaration and its visibility, type and definition are unchanged.
The added open commands only resolve notation and scoped instances in the private proofs;
they change no public declaration or instance.

## Old

```lean
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
```

## New

The unused import is removed. The other public imports are unchanged. Proof-only imports
include `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstructibleCompactness | U7 | Sole direct importer; it already imports TruncationsAndHomotopyColimits independently, so no adaptation is needed. Its import of FiniteWindow is proof-only. |

The direct importer already imports the removed dependency itself, and exposes no part of
FiniteWindow through a public import. Consequently all further downstream interfaces are
unchanged. The original consumer compiled against the new FiniteWindow in the same sandbox
in 3.5 seconds with no errors or warnings. No target statement or definition it uses changes
meaning.

## Status

landed 20261019T034338-L-423695 2026-10-19 (merge of deliver/W5/Sheaf.Paper.FiniteWindow)
