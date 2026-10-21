# Sheaf.Paper.LisseLatticeReducedOpen

## Reason

The completed proof introduces private comparison constructions, local continuity
instance synthesis, and local reducibility settings. The interface checker treats
new `open`, `variable`, `section`, and `attribute` commands conservatively as an
interface change and requires this record. The first preflight also identified a
private instance registered globally; it is now a private theorem with a
`local instance` attribute. No existing definition or statement is changed.

## Old

The original file had this declaration preamble, verbatim:

```lean
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale
```

Its only theorem was `exists_lisse_lattice_reduced_open`, with the exact public
signature retained by the delivery and body `:= by sorry`. It had no local proof
helpers or continuity instance.

## New

The declaration preamble is:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale
```

The continuity assertion is a theorem, avoiding the proposition-definition and
class-definition-reducibility warnings of the intermediate private definition.
The added continuity helper and its registration are, verbatim:

```lean
private theorem baseChange_cont {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.proEtaleBaseChange f).IsContinuous (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Y) := AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback f

attribute [local instance] baseChange_cont
```

All other added declarations are private proved helpers. The file additionally
opens the `CategoryTheory.Obj` and `CategoryTheory.Functor` scopes and uses two
`CoefficientTransport` sections with explicit section variables. Every added
reducibility attribute is local, including the attribute on
`continuous_restriction_adjunction`; these settings control elaboration within
this proof file. The theorem's original signature, visibility, and six public
imports are unchanged. There is no new global instance, notation, public
abbreviation, or public definition. No target statement or its defining data
changes, so no target statement review is reopened.

## Users

`tools/downstream.py Sheaf.Paper.LisseLatticeReducedOpen --uses
exists_lisse_lattice_reduced_open` reports zero downstream modules and only the
item itself as a textual user. A direct search of the two library roots and the
quarantine finds no current Lean importers. The unfinished DAG parents are
preserved; this delivery does not withdraw the item or change their statements.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.LisseLatticeReducedOpen` | D5 | Completes its theorem with private helpers and local elaboration settings. |

No other module is adapted and no source-library declaration is changed.

## Status

landed 20261021T214741-L-1846754 2026-10-21 (merge of deliver/D5/Sheaf.Paper.LisseLatticeReducedOpen)
