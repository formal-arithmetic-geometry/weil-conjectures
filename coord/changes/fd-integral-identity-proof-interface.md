# WeilConjectures.fdIntegralIdentityRationalEquivalence

## Reason

The assigned theorem is proved without changing its signature. Preflight classifies the
new section commands, private instance registrations, and local reducibility attributes
as an interface change requiring this record. They support the proof of semilinearity,
exactness, and the prescribed shift normalization. The local irreducibility settings
prevent repeated expansion of chosen equivalences and triangulation data during final
assembly. Explicit category arguments avoid repeating expensive inference. The private theorem `localizedExact` constructs the actual shift by Mathlib localization
and packages it with exactness and all integer normalization equations. It accepts the
published localization functors and their defining equalities, so the resulting equations
use their existing shift instances directly. Final assembly uses its existential witness,
keeping the shift data abstract while checking the remaining properties. No shift is chosen
from an unproved existence theorem. The private `integralEquivalence` also exposes its
actual restriction functors directly, while retaining the unit and counit from
`integralEquivalenceAux`; no mathematical data changes.

## Old

The existing options and namespace header were:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures
```

The public theorem had its current signature and proof `by sorry`. None of the private
helpers or instance registrations in the new proof existed.

## New

The existing namespace and public theorem signature are unchanged. The helper proofs use:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Before the public theorem, the original options are restored and the following local
attributes retain abstract interfaces for the chosen objects:

```lean
attribute [local irreducible] integralEquivalence integralEquivalenceAux
  localizedEquivalenceAux
  sfRationalTriangulationDatum sfRationalCoefficientEquiv pbcRationalCoefficientEquiv
  ScalarLocalization.extensionHom ScalarLocalization.localization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The new private instances are `integralEquivalence_additive`,
`integralEquivalence_inverse_additive`, `integralEquivalence_shift`,
`integralEquivalence_inverse_shift`, `integralEquivalence_tri`, and
`integralEquivalence_inverse_tri`. Their targets involve the new private definition
`integralEquivalence`; they supply its additive, shift, and triangulated structures.
All six are proved. They provide no new public mathematical signatures. The temporary
section and its variables end before the existing public theorem. All additional
imports are private proof imports. No existing definition, theorem signature, public
import, or target statement is changed, and no declaration is removed.

## Users

`tools/downstream.py Sheaf.Paper.FdIntegralIdentityRationalEquivalence --uses
fdIntegralIdentityRationalEquivalence` reports zero downstream modules and one textual
user, the item itself. No consumer adaptation is needed. Future consumers receive the
same theorem statement; the proof remains on the same integral and raw rational categories.
The item remains attached to its node and parents; no withdrawal is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FdIntegralIdentityRationalEquivalence | R6 | Complete proof; private helpers, proof imports, and local proof elaboration interfaces. |

## Status

landed 20261022T013434-L-3580282 2026-10-22 (merge of deliver/R6/Sheaf.Paper.FdIntegralIdentityRationalEquivalence)
