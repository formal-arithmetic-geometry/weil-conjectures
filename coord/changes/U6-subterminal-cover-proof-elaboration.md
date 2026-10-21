# SheafOfModules.SubterminalCover.shortExact proof elaboration

## Reason

The proof uses the existing `HasSheafify` hypothesis at the declared coefficient
universe. Disabling the essentially-small sheafification instance during proof
elaboration avoids competing universe constraints, as in the local-calculus module.
The command is scoped with `in` separately to each private helper and the original
public theorem. It therefore does not remove an instance for importing modules.
No definition, existing signature, public import or mathematical statement changes.
The new elaboration options are file-local.

## Old

No local instance-removal command preceded these declarations. The original theorem
ended in `:= by sorry`.

## New

Each proved helper and the public theorem are individually preceded by:

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
```

The original public theorem has a complete proof from the existing local-calculus
theorem. Private helpers provide naturality, matrix splittings, comparison isomorphisms,
and joint reflection of short exactness. There are no new public declarations.

## Users

`tools/downstream.py Sheaf.CategoryTheory.SubterminalCoverModuleSES --uses shortExact`
reports zero downstream modules and only the declaration's own occurrence.
No existing consumer requires adaptation; future consumers see identical signatures,
definitions, public imports, and the same instance environment.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SubterminalCoverModuleSES | U6 | Proof completed; scoped elaboration commands |

## Status

landed 20261021T144013-L-36035 2026-10-21 (merge of deliver/U6/Sheaf.CategoryTheory.SubterminalCoverModuleSES)
