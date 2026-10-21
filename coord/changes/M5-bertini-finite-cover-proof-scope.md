# Sheaf.AlgebraicGeometry.BertiniFiniteCoverIrreducibleSystem proof scope

## Reason

The proof adds private tensor-pullback and zero-scheme comparison helpers. These use
namespace openings, a noncomputable section, backward-elaboration options, and a local
irreducibility attribute. Stage-3 preflight classifies the added commands as an interface
change and requires this record. No existing declaration signature, public import,
definition body, or target statement changes.

## Old

The existing scope commands before the theorem, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry
```

No tensor comparison helper or local tensor irreducibility attribute occurred there.

## New

The existing commands remain, followed by these proof-scope commands:

```lean
open Scheme.Modules Opposite MonoidalCategory

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The private helper declarations then use:

```lean
attribute [local irreducible] tensorPullback tensorPullbackObj
```

The added section ends before `end AlgebraicGeometry`. The attribute is local to that
section. These commands support proof elaboration; all comparison helpers are private and
proved. The public theorem's signature and all pre-existing public imports are identical
to the original text. Two new public results are declared only in their own new Sheaf
modules and have new DAG nodes: `AlgebraicGeometry.bertini_finiteCover_base_codimension`
and `AlgebraicGeometry.bertini_finiteCover_transverse_component`.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.BertiniFiniteCoverIrreducibleSystem --uses
AlgebraicGeometry.exists_open_geometricallyIrreducible_finiteCover_linearSystem` reports
zero downstream importers and one textual use, the declaration itself. Unfinished DAG
parents remain valid because the theorem's type is unchanged; no withdrawal is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BertiniFiniteCoverIrreducibleSystem | M5 | Private proof helpers and local elaboration scope; public signature unchanged. |
| Sheaf.AlgebraicGeometry.BertiniFiniteCoverBaseCodimension | M5 (new) | New proved exact-codimension lemma, used only by this proof. |
| Sheaf.AlgebraicGeometry.BertiniFiniteCoverTransverseComponent | M5 (new) | New separate codimension-two witness lemma, with its own node and source proof. |

No other group's module is adapted. No source-library declaration is changed.

## Status

landed 20261021T130053-L-2509187 2026-10-21 (merge of deliver/M5/Sheaf.AlgebraicGeometry.BertiniFiniteCoverIrreducibleSystem)
