# AlgebraicGeometry.Scheme.finiteExtensionReductionConeBound

## Reason

The full proof initially exceeded the unchanged 60-second delivery compile limit.
The imported constant-module comparison and finite-extension coefficient datum are
large constructions. Local irreducibility keeps elaboration on their proved formulas.
The resolution argument is now proved generically before specialization, and scalar
section comparisons use typed equality chains. The complete proof compiles in 21.5
seconds. No compilation limit is raised.

The preflight command scan conservatively flags the new local attribute and scoped
notation commands. This record documents their exact scope and lack of exported effect.

## Old

The original item has no local irreducibility attribute. Its namespace starts with:

```lean
namespace AlgebraicGeometry.Scheme
```

It then declares the existing `finiteExtensionCompletedModulesAbelian` instance and
`finiteExtensionReductionConeBound` theorem. Their public signatures, universes,
attributes, and definitions are retained verbatim; only the theorem proof is completed.

## New

The namespace now starts with these exact commands:

```lean
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] CompletedConstantReduction.constantChange_unit
  pbcPadicCoefficientDatum
```

A single `open scoped ZeroObject in` scopes zero-object notation to the private generic
flat-resolution theorem. All other added definitions and theorems are private and proved.
The imported definitions themselves, their signatures, their bodies, and their exported
attributes are unchanged. These commands affect elaboration only inside the item file.
All public imports are preserved, and the explicit coefficient-extension proof import is
also retained to keep the unit route explicit.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteExtensionReductionConeBound | E9 | Local proof elaboration uses the two irreducibility hints and scoped zero-object notation. |

`python3 tools/downstream.py Sheaf.Paper.FiniteExtensionReductionConeBound --uses
AlgebraicGeometry.Scheme.finiteExtensionReductionConeBound
AlgebraicGeometry.Scheme.finiteExtensionCompletedModulesAbelian` reports zero downstream
Lean importers and mentions only the item itself. The local attributes and scoped notation
have no external users. DAG parents keep the same statement and node. No consumer is
adapted, and no module held by another group is changed.

## Status

landed 20261021T100947-L-4179330 2026-10-21 (merge of deliver/E9/Sheaf.Paper.FiniteExtensionReductionConeBound)
