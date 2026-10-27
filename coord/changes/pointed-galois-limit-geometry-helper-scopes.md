# Sheaf.AlgebraicGeometry.FundamentalGroup.PointedGaloisLimitGeometry

## Reason

The delivery preflight conservatively flags section-scoped variable and local
attribute commands added for proved private helpers. These commands scope the
proof, and do not change an existing public signature or definition. Record their
scope explicitly. No other module is edited.

## Old

The existing public-section and namespace header is verbatim:

```lean
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite PreGaloisCategory

namespace AlgebraicGeometry.Scheme.UniversalCover
```

No helper sections followed normalSectionAlgebraMap.

## New

The existing header, public imports, definitions, and theorem signature are
unchanged. After normalSectionAlgebraMap, add these scoped helper section headers:

```lean
section Labels

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
  (G : ProfiniteGrp.{u})
  [∀ Y : X.FiniteEtale, MulAction G ((FiniteEtale.fiber x).obj Y)]
  [IsFundamentalGroup (FiniteEtale.fiber x) G]

attribute [local instance] FiniteEtale.fiberFunctor
-- proved private helpers
end Labels

section Charts

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
  (G : ProfiniteGrp.{u}) (E : OpenNormalSubgroup G ≌ Index x)
-- proved private helpers
end Charts
```

Both sections close before the existing public theorem. The instance attribute
is local; the variables bind only private helpers declared inside their sections.
No public declaration can refer to a private definition through its signature or
its definition body. The public theorem's proof is completed from these helpers.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FundamentalGroup.PointedGaloisLimitGeometry | E4 | Private proof sections only; existing public API unchanged. |

`tools/downstream.py` reports zero downstream modules and only the assigned module
itself as a textual user of exists_pointedGaloisLimitGeometry. No consumer needs
adaptation. No target statement or definition used in its signature changes.

## Status

landed 20261023T123452-L-1194281 2026-10-23 (merge of deliver/E4/Sheaf.AlgebraicGeometry.FundamentalGroup.PointedGaloisLimitGeometry)
