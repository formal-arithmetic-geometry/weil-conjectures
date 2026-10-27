# AlgebraicGeometry.ProEtale.scalarModelImmersionExtension proof context

## Reason

Fill the existing theorem proof without changing any public declaration signature,
definition, or public import. The static interface check conservatively flags new
file-local proof elaboration commands. The extra zero-object scope permits the
identity-cover zero model. Local irreducibility keeps large coefficient functors
and adjunctions folded during proof elaboration; the backward transparency option
respects those local annotations. These commands do not export attributes, instances,
notation, or altered reducibility to importers. All retained helpers are private and proved. The returned duplicate `local_model_iso` is removed;
a private `import all Sheaf.Paper.IntegralContinuousCokernelLocalModel` exposes the existing
private `ContinuousRingUniverse.model_of_iso`, which is applied directly. This proof-only
import is acyclic and does not change what importers see.
No target statement or definition changes meaning, and no consumer needs adaptation.

## Old

The previous proof context (verbatim):

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
```

## New

The delivered proof context (verbatim):

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.openImmersionLowerShriek CondensedRing.upperStarLowerStarAdjunction
  CondensedRing.openImmersionLowerShriekUpperStarAdjunction CondensedRing.upperStarComp
  CondensedRing.comapPullbackHomCompIso
```

The existing assertion definition is byte-identical, as is the theorem signature.
The old theorem body was `by sorry`; it is now proved through private helpers.
Every new import is private. The actual proof and its dependency route are recorded
in the module docstring, DAG node, and report.

## Users

`python3 tools/downstream.py Sheaf.Paper.ScalarModelImmersionExtension --uses
ScalarModelImmersionExtensionAssertions scalarModelImmersionExtension` reports
these two transitive importers, and no occurrence of either declaration in them.
Neither file is edited. The claim records contain no current matching holder.
Local proof elaboration commands do not propagate through their private import
of this module, and the public API and definitions remain identical.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Public API unchanged; no adaptation. |

## Status

landed 20261024T015536-L-2415838 2026-10-24 (merge of deliver/P9/Sheaf.Paper.ScalarModelImmersionExtension)
