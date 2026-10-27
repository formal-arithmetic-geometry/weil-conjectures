# AlgebraicGeometry.cartesian_closure_refinement

## Reason

Prove the theorem using the canonical comparison of two pullbacks. Its statement needs
neither NagataSketchClosure nor RefinementCategory as a public import. Keep the former
as a private proof import and remove the latter. The theorem signature and all definitions
remain identical. Remove two unused private source-library proof imports; add Mathlib's
open-immersion/surjectivity criterion for isomorphisms as a private proof import.

## Old

```lean
public import Sheaf.Compactification.NagataSketchClosure
public import WeilConjectures.Compactification.RefinementCategory
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
```

## New

```lean
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Sheaf.Compactification.NagataSketchClosure
```

## Users

`python3 tools/downstream.py Sheaf.Compactification.CartesianClosureRefinement --uses
AlgebraicGeometry.cartesian_closure_refinement` reports zero downstream modules and only
the declaration's own module as a textual user. Direct import/declaration searches agree.
No consumer adaptation is required. The node's unfinished parents remain untouched and
can use the identical public theorem. No definition used by a target changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Compactification.CartesianClosureRefinement | M6 | theorem proved; public proof imports removed |

## Status

landed 20261023T105208-L-3524191 2026-10-23 (merge of deliver/M6/Sheaf.Compactification.CartesianClosureRefinement)
