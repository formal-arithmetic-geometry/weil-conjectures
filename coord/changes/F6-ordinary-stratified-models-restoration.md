# Sheaf.Paper.OrdinaryPullbackStratifiedModels

## Reason

Restore the item from its exact archive in coord/rework.tsv. The old parent theorem module
and finite-projective proof dependency are quarantined through the completion-unit dependency
chain. The item uses the parent only for the already extracted ordinary construction.
Import that construction directly, and prove the needed finite-projective flatness from the
existing scalar-unit, finite-product and finite-free-retract APIs. Preserve the archived
public declarations and their types and data. In particular, do not withdraw the item or
its DAG attachment.

The new chart proof dependency exposes broad `CompletedCoefficientPushforward.modAbelian`
and `hasDerived` instances whose independent coefficient universe cannot be inferred from
this item's fixed coefficient size. Disable those instances and the two generic Subterminal
sheafification instances in this file; the existing canonical module category structures
and standard derived localizations are used instead. The fixed-universe proof helpers from the old dependency are used only in sections of
private helpers. Their local instance attributes end before the public declarations resume.
The same broad integral-operations instance exclusions as in the removed dependency keep
universe inference fixed. No instance declaration is changed.

The exact-restriction proofs additionally use the existing OrdinaryCompletedPullbackExact
statement, after proving that its projection-defined structural map gives the original
ordinary module pullback. All new helpers are private and proved.

## Old

```lean
public import Sheaf.Paper.OrdinaryCompletedIntegralPullback
import all Sheaf.Paper.FiniteProjectiveModelPullback
```

The old private modelObjectIso identifies modelModule with
FiniteProjectivePullback.model, and perfectModelPullback transfers the dependency's
private model_flat theorem across that isomorphism.

## New

```lean
public import Sheaf.Paper.OrdinaryIntegralPullbackConstruction
import all Sheaf.Paper.ScalarPerfectFiniteFree
import all Sheaf.Paper.StrictPerfectRingedPullbackModel
import Sheaf.Paper.OrdinaryCompletedPullbackExact
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
```

The private tensorModel is an abbreviation of the existing scalarPerfectFunctor.
Its unit and finite-free comparisons, followed by the finite-projective splitting,
prove tensorModel_flat. The unchanged original modelModule is identified with that
same tensor object by modelObjectIso; perfectModelPullback uses this flatness proof.
The actual scalar, module, complex, generator, square and local-comparison definitions
remain the archived definitions. Explicit standard derived-category instances in
modelModule_obj agree with those already fixed in completedConstantExtension.
Explicit standard instances in the new private counit proof select the same localization.

The old parent publicly reexports OrdinaryIntegralPullbackConstruction. The replacement
keeps the construction needed by all public signatures and removes the unrelated completion
and constructibility theorem reexports. No target signature or notion changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | F6 | Restored; two exactness holes closed; public declaration types and data preserved. |

`tools/downstream.py Sheaf.Paper.OrdinaryPullbackStratifiedModels --uses
WeilConjectures.OrdinaryStratifiedModels.ordinaryPullbackStratifiedModels` reports zero
downstream modules and only the item's own occurrence. A direct import search in both
lean/ and quarantine/ also finds no importing module. No importer needs adaptation.
The DAG attachment and dependencies for unfinished parents are retained. The module
is restored, not withdrawn; zero importers is not being used as a withdrawal argument.

## Status

landed 20261027T064447-L-2181793 2026-10-27 (merge of deliver/F6/Sheaf.Paper.OrdinaryPullbackStratifiedModels)
