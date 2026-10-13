# finite presentation binary gluing proof interface

## Reason

The completed proof needs a private locality helper and its proof-only imports. The
stage-3 interface check also observes the local `open CategoryTheory.Limits
SheafOfModules` command used by that helper. These changes support elaboration of the
existing theorem; no public declaration, statement, definition, or exported meaning
changes.

## Old

The module imported the generic gluing proof module and contained the target theorem
with a `sorry` proof.

## New

The generic gluing import is replaced by proof-only imports of the concrete binary
submodule restriction properties and finite-presentation locality tools. The new
locality helper and `open` command are private to this module's proof context.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ModuleFinitePresentationBinaryGluing | D4 | Existing theorem signature and public meaning unchanged; proof is complete. |

## Status

landed 20261013T120801-L-3469876 2026-10-13 (merge of deliver/D4/Sheaf.AlgebraicGeometry.ModuleFinitePresentationBinaryGluing)
