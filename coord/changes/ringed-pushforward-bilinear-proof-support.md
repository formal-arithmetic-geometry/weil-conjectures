# SheafOfModules.ringedPushforward_bilinear_transfer proof-support commands

## Reason

Prove the existing theorem at independent site and coefficient universes. The proof uses
private tensor-universal-property helpers and local reducibility settings to avoid unfolding
the localization monoidal structure during sectionwise calculations. No existing public
signature, definition or public import changes.

## Old

The original setup is, verbatim:

```lean
namespace SheafOfModules

set_option autoImplicit false
```

The theorem body is `by sorry`. Its proof-only import of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal` supplies a theorem
whose site and coefficient universes coincide.

## New

The setup adds, verbatim:

```lean
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
```

These settings are local to elaboration of this module. Existing global attributes and
instances are unchanged. Four proved private lemmas supply existence, uniqueness and the
naturality of the canonical pure tensor, at independent universes. A private noncomputable
restriction-of-scalars construction supplies the sectionwise bilinear map with explicit
additivity and scalar equations. The original public theorem signature stays verbatim.
The unused proof-only import is removed. No target statement or target-used definition changes.

## Users

`tools/downstream.py` reports zero downstream modules, with text use only in the item itself.
The existing statement and its public imports are preserved, so no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedPushforwardBilinearTransfer | P6 | One theorem hole closed with private proof support. |

## Status

landed 20261023T131717-L-2141770 2026-10-23 (merge of deliver/P6/Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedPushforwardBilinearTransfer)
