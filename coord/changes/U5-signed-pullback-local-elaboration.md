# signedLineScalarPullbackSquare_of_normalized proof elaboration

## Reason

The completed proof needs to identify module restrictions, ring restrictions and
pushforward section actions. Local reducibility attributes expose these wrappers,
while local irreducibility attributes keep tensor and scalar-extension constructions
behind their existing APIs. These settings follow the proved neighboring signed scalar
and pullback modules. `import all` grants the proof access to existing private proved
basis-chart helpers. Neither import is public. All added helpers are private and fully
proved; they occur only in theorem proofs. No existing public signature, definition,
visibility, public import or exported attribute changes. No target meaning changes.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The original file had no local reducibility settings and its sole theorem ended in
`by sorry`.

## New

The original options are retained. Proof-only imports are added:

```lean
import all Sheaf.Paper.SignedLineScalarTensorTower
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackLocalizationOfUniverses
```

Local reducibility exposes `sheafCompose`, coefficient restriction functors, unit
modules, `PresheafOfModules.restrictOver`, `Over.forget`, site pushforward,
module pushforward and the adjunction-unit section abbreviation. Local irreducibility
seals `changeOfRingsOfUniverses`, `scalarExtensionSection`, `siteSheafTensorRight` and
`siteSheafTensorTmul`. The unused-section-variable linter is disabled for the private
helpers, which retain the surrounding explicit sheafification assumptions. All settings
are local to this file. `allowUnsafeReducibility` only permits local elaboration
attributes; every proof is kernel checked.

## Users

`tools/downstream.py Sheaf.Paper.SignedLineScalarPullbackNaturality --direct` has one
importer. The theorem-name search also finds only the defining file and that consumer.
The public signature is verbatim unchanged, so no consumer adaptation is required.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SignedLineScalarPullbackNaturality | U5 | Complete proof and private helpers. |
| Sheaf.Paper.SignedLineScalarPullbackSquare | not adapted | Identical public interface. |

## Status

landed 20261025T204943-L-3065032 2026-10-25 (merge of deliver/U5/Sheaf.Paper.SignedLineScalarPullbackNaturality)
