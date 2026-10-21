# Compactification-independence proofs

## Reason

Close the three existing theorem holes in the assigned compactification-independence module.
The quarantined prerequisite cluster has independently returned to the shared library.

## Old

The current source and its quarantine baseline have three theorem holes: restriction
comparison invertibility and its two proper pushforward coefficient cases.

## New

Existing declaration signatures, visibility, attributes, public imports and all non-theorem
bodies are unchanged. Every hole is replaced by a complete proof. New private, proved helpers
transport cartesian open counit invertibility from abelian sheaves through module objects and
derived categories to the bounded constructible category, and cancel the other invertible
factors in proper interchange to obtain the proper-map unit. No public declaration is added.

Three private proof imports supply bounded constructible pullback, proper/open interchange,
and abelian extension-by-zero base change. A scoped object-notation opening and two linter
options preserve the original redundant coefficient binders. The module documentation now
explains the proof inputs. No target or definition changes, new nodes or new holes occur.

## Users

Only the assigned module is delivered, held by J4. Every existing public interface is
preserved, so no consumer adaptation is needed. All auxiliary restoration copies were
omitted after their modules returned to the shared library.

## Status

landed 20261021T061410-L-1769456 2026-10-21 (merge of deliver/J4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence)
