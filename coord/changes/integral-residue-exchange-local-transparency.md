# integralResidueExchange_comparison

## Reason

The proof uses the new typed derived-functor wrappers. Within this module, their
transparency is relaxed to identify them with the actual functors in the unchanged
statement. Preflight conservatively classifies the added local attribute command as
an interface edit, so this record declares it explicitly. The option and attributes
control elaboration only. No existing signature, definition body, visibility, global
attribute, target type, or mathematical meaning changes. No consumer needs adaptation.

## Old

The existing module has no `backward.defeqAttrib.useBackward` option or local wrapper
transparency attributes. Its namespace begins verbatim:

```lean
namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]
```

## New

Add this proof elaboration option before the existing public section:

```lean
set_option backward.defeqAttrib.useBackward true
```

The namespace prefix becomes:

```lean
namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar
  residueExchangeReduction

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]
```

The theorem signature remains byte for byte the old signature. Its `sorry` is replaced
by the proof described in the report. The wrappers themselves are actual constructions
in a new module; this local command does not export a change to their attributes.

## Users

`tools/downstream.py Sheaf.Paper.IntegralResidueExchange --uses integralResidueExchange_comparison`
lists six transitive downstream modules and identifies `IntegralFiniteExchangeComparison`
as the sole external textual caller. All six are listed below. They need no edit:
local proof elaboration commands do not change imported declarations or their types.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueExchange | C2 | Local elaboration of its new proof only; signature unchanged. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No mathematical or interface change; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Calls the identical theorem signature; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No mathematical or interface change; no adaptation. |
| TargetsCheck | unclaimed | No target statement or meaning changes; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No mathematical or interface change; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No mathematical or interface change; no adaptation. |

## Status

landed 20261016T050636-L-3699071 2026-10-16 (merge of deliver/C2/Sheaf.Paper.IntegralResidueExchange)
