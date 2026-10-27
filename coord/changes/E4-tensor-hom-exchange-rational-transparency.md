# WeilConjectures.ConstructibleTensorHom rational interface restoration

## Reason

Restore the quarantined item recorded in `coord/rework.tsv` without withdrawing any
of its declarations or dependencies. The recorded build failed at the compositions
in `RationalDescent.normalization` (line 538) and `rationalDirectChange` (line 580),
with deterministic `isDefEq` heartbeat exhaustion. The later missing identifiers
were cascading errors. Both compositions should compare the published functors,
without expanding their chosen derived and scalar-localization constructions.

The unchanged archive now compiles against the published build (45.1 seconds).
The delivery additionally places four costly functor definitions behind local
irreducibility at the rational interface. This is a scoped elaboration repair;
it does not change any mathematical definition, statement, proof or public import.
The repaired module compiled without diagnostics in 35.3 seconds, compared with
45.1 seconds for the archive on this build. No heartbeat or time limit is raised.

## Old

Immediately before the existing `RationalDescent` docstring, no local transparency
restriction was present. The archived declarations and their signatures are kept
verbatim; `exists_family` retains its original proof hole.

## New

The following command is added before `RationalDescent`:

```lean
attribute [local irreducible] rationalDerivedPullback sfRationalConstructibleLocalization
  sfRationalScalarExtension rationalDerivedInternalHom
```

These are respectively the chosen derived pullback, raw scalar-localization
functor, chosen rational scalar transition and chosen rational internal Hom.
Their published functor types provide all interfaces used by this module. The
attributes are local to the current section and do not affect importers.

## Users

`tools/downstream.py Sheaf.Paper.TensorHomExchange --allow-missing --uses
RationalDescent rationalDirectChange` reports no current downstream modules.
A textual search of both `lean/` and `quarantine/` also finds no importer or
reference to this module's namespace outside its own archive. DAG parents and
its attachment remain in force; zero importers is not used to infer withdrawal.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TensorHomExchange | E4 | Restore every declaration, with local transparency restrictions for the rational interface. |

There are no consumer edits, new declarations, target changes or node changes.
The existing node `sk-thm-sf-tensor-hom` and its proof dependencies are preserved.

## Status

landed 20261024T214339-L-591849 2026-10-24 (merge of deliver/E4/Sheaf.Paper.TensorHomExchange)
