# Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal

## Reason

The proof needs category, scheme-module, and tensor-product names and the
backward elaborator transparency options used by the imported stalk API.
This record documents the added source context for independent review. No public declaration signature, definition, attribute, notation,
or public import changes. All five new helper theorems are private and proved.

## Old

The original context included `set_option warn.sorry false`; after its three options was:

```lean
universe u v w

namespace Module
```

The only public declaration was, and remains, the following signature:

```lean
theorem finitePresentation_localizedModule_atPrime_of_flat
    {A : Type u} {B : Type v} {N : Type w}
    [CommRing A] [CommRing B] [AddCommGroup N]
    [Algebra A B] [Module B N] [Module.Finite B N]
    [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime]
    (hflat : @Module.Flat A (LocalizedModule q.primeCompl N) _ _
      (Module.compHom (LocalizedModule q.primeCompl N) (algebraMap A B))) :
    Module.FinitePresentation (Localization.AtPrime q) (LocalizedModule q.primeCompl N)
```

## New

The file's public section is noncomputable. The unnecessary original
`set_option warn.sorry false` command is removed, so normal hole warnings remain
enabled and the source hole census sees no false marker in an option name.
The added context is:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
```

The public signature above is textually unchanged. Its proof replaces its
single `sorry`; the additional imports are private proof imports. Namespace
opens and elaborator options are local source commands, not exported notation
or instances. The theorem has the same meaning and assumptions; no target
statement or target definition changes.

## Users

`tools/downstream.py Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal --uses
Module.finitePresentation_localizedModule_atPrime_of_flat` reports 49 downstream
modules and only the item's own declaration as a textual use. There are no
consumer adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal | P8 | Same theorem signature; proof completed with private helpers and proof-local context commands. |

## Status

landed 20261024T015527-L-2413714 2026-10-24 (merge of deliver/P8/Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal)
