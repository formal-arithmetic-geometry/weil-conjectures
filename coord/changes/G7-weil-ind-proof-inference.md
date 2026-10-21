# WeilIndSheafCategory proof-inference commands

## Reason

The four new proofs use explicit Kan-extension preservation witnesses. During
these proofs three generic backwards instance searches are disabled, then
restored with their original default priority. Local irreducibility prevents
unfolding the chosen ind-extension and its normalized unit. These are proof
elaboration controls: every existing public declaration, definition body, public
import and exported instance registration is preserved. The preflight interface
scanner conservatively classifies the added `attribute` and `omit` commands as
an interface change, so this record documents them explicitly.

## Old

The original ind-extension section began verbatim with:

```lean
section IndExtension
universe w
variable {C B : Type w} [SmallCategory C] [SmallCategory B]
  [Abelian C] [Abelian B]
```

It contained no commands changing the three Kan-extension instance registrations
or the local reducibility of `zlIndMap` and `zlIndMapIso`.

## New

Before the original variables, disable the generic search rules:

```lean
attribute [-instance] Functor.hasLeftKanExtension_of_preserves
attribute [-instance] Functor.hasPointwiseLeftKanExtension_of_preserves
attribute [-instance] Functor.PreservesLeftKanExtension.preserves
```

After the section restore the same registrations with their original default
priority:

```lean
attribute [instance] Functor.hasLeftKanExtension_of_preserves
attribute [instance] Functor.hasPointwiseLeftKanExtension_of_preserves
attribute [instance] Functor.PreservesLeftKanExtension.preserves
```

Inside the section, after proving the explicit Kan-extension characterization,
and again after the section (because the first command is local), use:

```lean
attribute [local irreducible] zlIndMap zlIndMapIso
```

Three private helper declarations have a scoped `omit [Abelian C] in` to keep
an unused assumption out of their types. All new transparency options are scoped
to individual declarations. None of these local changes exports a new attribute
on a public declaration or changes a target's meaning. No definition is replaced
by an arbitrary choice or by a proof hole.

## Users

`tools/downstream.py Sheaf.Paper.WeilIndSheafCategory` lists 58 transitive
consumers. A textual search for `zlIndMap`, `zlIndMapIso` and the two named
Kan-extension existence instances finds no consumer outside the item itself.
`tools/downstream.py ... --uses zlIndMap zlIndMapIso
Functor.hasLeftKanExtension_of_preserves
Functor.hasPointwiseLeftKanExtension_of_preserves
Functor.PreservesLeftKanExtension.preserves` confirms that only the item uses
the first two names and no checked module uses the other names.
The modified commands affect only elaboration inside the item; the three
generic Mathlib instance registrations are restored before the module ends.
Thus all 58 consumers retain the same public signatures, definitions and
instance registrations, and none needs adaptation. No consumer is edited.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.WeilIndSheafCategory` | G7 | Four theorem proofs; private proved helpers and proof elaboration commands. |

No existing declaration's signature or visibility changes. The source-library
modules and their attributes are untouched. No target-statement review reopens.

## Status

landed 20261021T101049-L-4603 2026-10-21 (merge of deliver/G7/Sheaf.Paper.WeilIndSheafCategory)
