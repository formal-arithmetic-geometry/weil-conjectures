# CompactSupportCondensedRealization interface

## Reason
The module adds the component-level identity refinement theorem and removes a local asynchronous elaboration option so the file compiles within the required file timeout.

## Old
The module had no public `systemRefinement_id_component` declaration and used `set_option Elab.async false`.

## New
The module declares `systemRefinement_id_component` with the component identity statement and no longer sets `Elab.async` to false.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompactSupportCondensedRealization | H1 | adds a component identity theorem and speeds elaboration |
| direct importers of Sheaf.Paper.CompactSupportCondensedRealization | various | interface remains compatible; theorem is additive |

## Status
landed 20261027T180628-L-3884265 2026-10-27 (merge of deliver/H1/Sheaf.Paper.CompactSupportCondensedRealization)
