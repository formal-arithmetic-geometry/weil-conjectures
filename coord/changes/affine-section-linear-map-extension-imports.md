# AlgebraicGeometry.Scheme.affine_section_linear_map_extension import interface

## Reason

The theorem uses Mathlib's quasi-coherence predicate and scheme module interface.
`Sheaf.AlgebraicGeometry.Coherent` supplies a custom coherent predicate and derived-Hom
infrastructure that neither the statement nor the proof uses. Replace it with the two
Mathlib statement imports and use `Mathlib.AlgebraicGeometry.Modules.Tilde` only in proofs.
The explicit PushforwardContinuous import is redundant with Modules.Sheaf.
Every existing declaration signature, visibility, and definition remains identical.
No target definition or target statement changes its mathematical meaning.

## Old

```lean
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
```

## New

```lean
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

import Mathlib.AlgebraicGeometry.Modules.Tilde
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineSectionLinearMapExtension
--direct --uses affine_section_linear_map_extension` identifies one direct importer
and the following two declaration occurrences. The transitive import closure has
277 modules; the only direct importer imports this module without `public` and
already publicly imports `Coherent` and PushforwardContinuous itself. Consequently
no downstream declaration loses an imported name or instance through this change.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineSectionLinearMapExtension | X3 | Statement and visibility unchanged; replace imports and prove the theorem from Mathlib. |
| Sheaf.AlgebraicGeometry.IdealPowerQuotientAffineLiftingSection | unclaimed | Calls the unchanged theorem; separately imports both removed dependencies. No adaptation needed. |

No module other than the claimed item is adapted by this delivery.

## Status

landed 20261013T122232-L-3592247 2026-10-13 (merge of deliver/X3/Sheaf.AlgebraicGeometry.AffineSectionLinearMapExtension)
