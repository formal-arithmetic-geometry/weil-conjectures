# AlgebraicGeometry.ProEtale.det_brown_hypotheses_ambient

## Reason

The completed proof uses the zero-object notation and the scoped internal-module
category instances. It adds two file-local opens. The delivery checker classifies
changes to these commands as an interface change and requests this record.
Every existing declaration signature, visibility, definition and public import
is preserved. No instance, notation or attribute declaration is added.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
```

## New

```lean
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open ZeroObject
open scoped CategoryTheory.Obj
```

## Users

`tools/downstream.py Sheaf.SixFunctors.BrownHypothesesAmbient
--uses det_brown_hypotheses_ambient` lists the two downstream modules below and
no external textual use of the theorem. Their source was inspected: the direct
consumer imports this module only for proofs; the indirect consumer imports that
consumer only for proofs. The two opens affect elaboration of this file, and no
consumer signature or target meaning changes. No consumer adaptation is needed.
The holder entries follow the current queue.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.BrownHypothesesAmbient | Z8 | Completed proof; two opens added; signature preserved. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Direct proof import; no source or statement change. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Indirect proof import; no source or statement change. |

## Status

landed 20261018T150153-L-3801371 2026-10-18 (merge of deliver/Z8/Sheaf.SixFunctors.BrownHypothesesAmbient)
