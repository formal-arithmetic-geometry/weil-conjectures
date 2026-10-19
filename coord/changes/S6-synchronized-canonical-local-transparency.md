# Local transparency in SynchronizedCanonicalMaps

## Reason

Elaborating the synchronized relations repeatedly unfolded the derived-category
localization models and exceeded the single-file compilation limit. Respecting
transparency and marking the two model definitions locally irreducible avoids that
unfolding. These commands affect only elaboration in this file. The conservative
interface check requests this record for command changes; no public declaration
signature, definition body, visibility, import or global attribute changes.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

There was no local irreducibility attribute before `SynchronizedIso`.

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

Before `SynchronizedIso`:

```lean
attribute [local irreducible] DerivedCategory HasDerivedCategory.standard
```

The three inductive definitions retain their original constructors and types.
The two theorems retain their original statements and now have complete proofs.
The local attribute and options are not exported to consumers.

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.SynchronizedCanonicalMaps --uses
SynchronizedPair` reported the following downstream module and the item itself.
A source search for the module import confirmed the sole direct consumer.
No consumer source adaptation is necessary, and no target statement changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | S6 | File-local elaboration settings; two proofs completed. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | R5 | Same public interface and meanings; no edit. |

## Status

landed 20261019T231340-L-576806 2026-10-19 (merge of deliver/S6/Sheaf.SixFunctors.SynchronizedCanonicalMaps)
