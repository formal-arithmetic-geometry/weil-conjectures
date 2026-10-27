# Sheaf.RingTheory.CotangentDifferentialPresheafSes proof elaboration commands

## Reason

The server preflight requests this record because its interface comparison detects
new `open`, `set_option` and `attribute` commands. The mathematical interface is
unchanged: every existing public definition, statement and public import is preserved.
The commands support the private proved construction of the differential sequence.
Irreducibility prevents repeated expansion of composed scalar-extension isomorphisms;
the generator formulas provide their subsequent API. The complete file compiles
without warnings in 48.4 seconds. No existing declaration receives a new attribute.

## Old

The existing scope command, verbatim:

```lean
open scoped ChangeOfRings
```

The new private helper names and their irreducibility attributes did not exist.
Neither new backward elaboration option was set in this module.

## New

The replacement scope command, verbatim:

```lean
open scoped ChangeOfRings TensorProduct
```

The new option commands, verbatim (the last restores transparency before `Sequence`):

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
```

The following commands occur after the respective private helpers' formula lemmas:

```lean
attribute [irreducible] tensorDesc
attribute [irreducible] tensorMap
attribute [irreducible] tensorIso
attribute [irreducible] polynomialBasisIso polynomialTensorIso
attribute [irreducible] tensorBaseChangeIso
attribute [irreducible] tensorBaseChangeNormalized
attribute [irreducible] tensorCancelIso
attribute [irreducible] aValue bValue
attribute [irreducible] valueOne valueTwo valueThree
attribute [irreducible] aMap bMap
attribute [irreducible] middleCoordinates
```

These names are all newly introduced private declarations. In particular, the complete
public `Sequence` record is textually identical to the original. No target statement
or definition used by a target has changed its meaning.

## Users

`python3 tools/downstream.py Sheaf.RingTheory.CotangentDifferentialPresheafSes
--uses sequence_nonempty Sequence` reports zero downstream Lean modules and only the
item itself as a textual user of the two names. Thus no consumer requires adaptation.
The DAG parents still need this item and are retained: cotangent transitivity triangle,
bar term identifications, colimit unramified algebra, bar diagram compatibility, and
bar arrow comparisons. This delivery does not withdraw any module or node.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.CotangentDifferentialPresheafSes | Z7 (this dispatch) | Private proof construction only; public interface preserved; compiles cleanly. |

No module held by another group is edited. No forced adaptations are necessary.

## Status

landed 20261024T022604-L-3015213 2026-10-24 (merge of deliver/Z7/Sheaf.RingTheory.CotangentDifferentialPresheafSes)
