# ProjectionFormulaArrows proof-local elaboration

## Reason

The new proofs use total tensor complexes abstractly.
Unfolding these constructions during unification causes deterministic heartbeat
exhaustion or the 60-second compile timeout. Local transparency registrations keep
the constructions abstract where the proofs use only their APIs. Preflight treats
these local commands and a removed private import as an interface change and
requires this record.

No declaration signature, visibility, public import, non-theorem body or target
statement changes. All six original holes are proved, every added helper is private
and proved, and no downstream file is adapted. The existing public import of
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` is preserved.

## Old

No local transparency registrations for the following constructions in this file.
The constructions themselves have their existing signatures and bodies, unchanged.
The old private proof imports included:

```lean
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.SplitPerfectTensorKInjective
```

## New

The same constructions retain their signatures and bodies. The following commands
are local to this module's proof elaboration:

```lean
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape
attribute [local irreducible] tensorAdjunctionTotal
attribute [local irreducible] tensorAdjunctionTotalInverse
attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap
```

The priority change chooses the existing canonical limit and colimit instances
directly instead of exploring unrelated constructions first. It adds no instance
or proof constant. The final full-file check including the axiom probe took 30.5
seconds.

Proof elaboration also scopes `backward.isDefEq.respectTransparency` and suppresses
unused-section-variable lint on proofs that must retain the original instance
binders. These options and local attributes are not inherited by importers.
Additional private proof imports supply finite-product comparisons, the sheaf
closed structure, dualizable-object flatness, homotopy-category orthogonality and
bounded devissage, mapping cones, homology exact sequences, and public K-flat
resolutions. The proof caches the family of total-tensor instances locally to
avoid repeated higher-order instance search. No private imported declaration
enters an existing public definition or signature.
The import of `SplitPerfectTensorKInjective` is removed: bounded triangulated
devissage proves the generic K-injectivity statement under its original hypotheses.
All six original public imports and all existing definition bodies are identical
to the current shared module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionFormulaArrows | P2 | Six completed proofs; local elaboration commands and private proof imports only. |
| Sheaf.Paper.ProjectionFormulaInverseNaturality | unclaimed | Uses total mate and mixed representative; unchanged signatures, definitions and exports. No adaptation. |
| Sheaf.Paper.ringedProjectionFormula_totalization_right | unclaimed | Uses total mate and inverse; unchanged signatures and definitions. No adaptation. |
| Sheaf.Paper.ProEtaleProjectionFormulaArrows | unclaimed | Uses total inverse; unchanged signature and definition. No adaptation. |
| Sheaf.Paper.ProjectionFormulaCompactified | unclaimed | Uses total inverse; unchanged signature and definition. No adaptation. |
| Sheaf.Paper.RingedStrictTowerProjectionMorphism | B6 | Uses mixed representative; unchanged signature and uniquely specified definition. No adaptation. |

`tools/downstream.py Sheaf.Paper.ProjectionFormulaArrows` reports 109 downstream
modules. Its `--uses tensorAdjunctionTotal`, `--uses tensorAdjunctionTotalInverse`
and `--uses mixedTensorRepresentative` queries give the users in this table.
None inherits a local transparency registration or a private proof import.
Thus all downstream statements retain their meaning; no target review is reopened.

## Status

landed 20261020T135419-L-1820853 2026-10-20 (merge of deliver/P2/Sheaf.Paper.ProjectionFormulaArrows)
