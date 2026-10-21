# Restoring and proving the primed open lower-shriek base-change interface

## Reason

The assigned module is missing from lean/ after the cluster-restore rollback recorded in
coord/rework.tsv. Restore the authoritative quarantined module and prove its sole sorry.
Private helpers use the existing essential-image API to avoid restoring unrelated quarantine
modules. Preserve the upstream public interface, including its existing coefficient binders.

## Old

The live path is absent:
`lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/OpenLowerShriekBaseChange.lean`.
The source is preserved under the identical relative path in quarantine/.
Its sole hole, verbatim in its existing section context, is:

```lean
theorem isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange' (sq : IsPullback g' j' j g) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekBaseChange' Λ ℓ sq.toCommSq) :=
  sorry
```

## New

The same theorem signature is restored verbatim, with a complete proof. All other existing
signatures, declaration attributes, public imports and non-theorem bodies are identical to
the archive. Three fully proved private helper theorems and three private proof imports are
added. No public declaration is added beyond restoring those in the authoritative archive.
The only additional commands are file-local linter.unusedSectionVars and
linter.overlappingInstances settings; they suppress warnings inherited from the original
redundant coefficient binders rather than changing those binders. These settings affect no
importer. No target statement or mathematical definition changes meaning, so no new target
semantic review is required.

## Users

The live module is absent, so the live downstream scan reports an unknown module; a textual
scan of imports in both live roots and both quarantine roots finds only the archived consumer
below. Its declarations, definitions and coefficient restrictions see the same restored API.
There are no adapted consumer modules in this delivery. The parser comparison against the
archive checks every existing declaration's statement and every existing definition body.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Archived direct importer; identical restored API, no adaptation. |

## Status

landed 20261021T020115-L-2585690 2026-10-21 (merge of deliver/E3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange)
