# AlgebraicGeometry.ProEtale.det_brown_hypotheses_ambient

## Reason

Restore the assigned quarantined module. The current rework row names
`quarantine/Sheaf/SixFunctors/BrownHypothesesAmbient.lean` and records a merge-queue
cluster-restore revert. That archive already contains a complete proof, with zero
holes. Restoring the theorem to its recorded module repairs the missing source;
it does not replace the theorem by an empty module or change its interface.

## Old

The recorded path `lean/Sheaf/SixFunctors/BrownHypothesesAmbient.lean` is absent.
The complete source survives at the quarantine path above. Its proof imports include:

```lean
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Sheaf.CategoryTheory.GrothendieckDerivedCoproducts
```

## New

The archived module is restored to its original Lean path, with every declaration,
public import, signature and proof preserved. The sole source difference is removing
this redundant private import:

```lean
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
```

`Sheaf.CategoryTheory.GrothendieckDerivedCoproducts` publicly imports that module.
Its instance and theorem remain available to the proof. No definition changes.
The existing DAG attachment and all mathematical dependencies remain intact.

## Users

`tools/downstream.py` cannot index the currently absent module (it reports
`unknown module(s)`). A source search of both `lean/` and `quarantine/` finds the
direct consumer below, and the four listed consumers of that consumer. None is
adapted: the restored theorem and complete public import interface are identical
to the archive. This changes no target statement or definition.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.BrownHypothesesAmbient | H4 | Restored complete module; zero holes. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | not adapted; quarantined | Direct proof import restored. |
| Sheaf.Paper.BrownExceptionalAdjoint | not adapted; quarantined | Indirect import; same interface. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not adapted; quarantined | Indirect import; same interface. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not adapted; quarantined | Indirect import; same interface. |
| Sheaf.Paper.MateOpenRestriction | not adapted; quarantined | Indirect import; same interface. |

## Status

landed 20261021T021015-L-2691127 2026-10-21 (merge of deliver/H4/Sheaf.SixFunctors.BrownHypothesesAmbient)
