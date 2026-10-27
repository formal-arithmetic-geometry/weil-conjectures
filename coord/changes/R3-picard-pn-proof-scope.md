# AlgebraicGeometry.ProjectiveSpace.picard_pn proof scope

## Reason

The delivery adds `open Scheme.Modules Opposite` inside namespace
AlgebraicGeometry.ProjectiveSpace to resolve names used by five proved private helpers
and the completed proof. The stage-3 static checker classifies any added open command
as a command that might change what importers see and requires this record. Lean open
commands do not export declarations or change elaborated signatures. The sole public
theorem's type and every public import remain byte-identical. No definition, instance,
notation, attribute or public declaration is added, changed or removed.

## Old

The file had this namespace-opening prefix:

```lean
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace
```

## New

```lean
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules Opposite
```

Private proof imports supply the cohomology comparison, scalar action, canonical module,
dimension-zero cohomology and existing exterior comparison. The proof-only imports of
Cohomology.Affine.Leray, AlternatingCechComputes and ProjectiveSpace.Differentials are
removed because no direct step needs them. The two modules explicitly realizing this
unit's route remain imported. No public import is removed or changed.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProjectiveSpace.PicardPn --uses
AlgebraicGeometry.ProjectiveSpace.picard_pn` reports zero downstream modules and only
the assigned module's own declaration as a textual use. Direct-import search agrees.
No consumer adaptations are needed. Axiom probing of the completed public theorem
reports exactly propext, Classical.choice and Quot.sound.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveSpace.PicardPn | R3 | Completes the proof; unchanged public type and public imports; proved private helpers and namespace openings only. |

## Status

landed 20261023T124251-L-1356928 2026-10-23 (merge of deliver/R3/Sheaf.AlgebraicGeometry.ProjectiveSpace.PicardPn)
