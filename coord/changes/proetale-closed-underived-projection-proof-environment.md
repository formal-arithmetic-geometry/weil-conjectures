# Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection proof environment

## Reason

The stage-3 preflight flags added namespace, universe, variable, open and attribute
commands as changing the module environment. They support private proved helpers
and prevent repeated expansion of inverse-image and scalar-extension constructions.
Existing public signatures, definition bodies and public imports remain verbatim.

## Old

The original environment contains:

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ProEtaleClosedProjection
```

There were no local reducibility attributes or general-site helper section.
Both existing theorem bodies were `by sorry`; their signatures are unchanged.

## New

The additional notation and elaboration commands are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ChangeOfRings
```

The local transparency controls, applied after their required implementation
calculations, are exactly:

```lean
attribute [local irreducible] regularInverseIso proEtaleModuleInverseImage
  inverseSection scalarIdentification
attribute [local irreducible] coefficientInverseIso
attribute [local irreducible] extensionTensorIso
```

The generic restriction/sheafification helpers use a bounded section:

```lean
section
universe s h
variable {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  {R₀ B₀ : Sheaf J RingCat.{u + 1}}
```

Its three declarations are private and proved, and `end` closes the section.
Every additional helper declaration is private and proved. The scopes do not
alter any existing public declaration or propagate local attributes to consumers.
No compiler timeout, heartbeat or kernel-checking setting changes.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection
--uses adjunction_exists adjunction projection coefficientModule CoefficientLinear
closed_underived_projection` reports zero downstream modules. Each of the six
existing declarations is mentioned only in the item itself. The current claim
record names E7. No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection | E7 | Private proof environment only; public API unchanged. |

## Status

landed 20261021T134333-L-862793 2026-10-21 (merge of deliver/E7/Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection)
