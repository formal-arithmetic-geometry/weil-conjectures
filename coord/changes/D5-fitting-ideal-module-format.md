# LinearMap.fittingIdealZero

## Reason

The assigned item and its only dependency FittingIdealZero were legacy non-module files.
The required module-format item cannot import the original dependency: lcompile reports
``cannot import non-`module` Sheaf.RingTheory.FittingIdealZero from `module```.
Convert the unclaimed dependency to the project module format. Preserve the definition body
and signature verbatim, and make all three original imports public to preserve their visibility.
Convert the assigned item as well, with its statement dependency publicly imported and its
proof dependency privately imported. The theorem signature is unchanged.

## Old

```lean
import Sheaf.RingTheory.PresentationFittingIdeal
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Zeroth Fitting ideal of a finite module

Source: Stacks Project, More on Algebra, Tags 07Z8 and 07ZA (blueprint: def-trf-fitting-ideal-zero).

This module chooses a finite free surjection and takes its zeroth kernel-minor ideal.  The
recorded presentation-independence theorem makes this choice independent of the surjection.
-/

universe u v

namespace LinearMap

/-- The zeroth Fitting ideal of a finitely generated module, obtained from a finite free
surjection.  Independence of the chosen surjection is
`presentationFittingIdeal_independence_baseChange` (blueprint: def-trf-fitting-ideal-zero). -/
noncomputable def fittingIdealZero {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] : Ideal R :=
  let h := Module.Finite.exists_fin' R M
  let hn := Classical.choose_spec h
  let π := Classical.choose hn
  π.presentationFittingIdeal 0

end LinearMap
```

The item's original imports were:

```lean
import Sheaf.RingTheory.FittingIdealZero
import Sheaf.RingTheory.PresentationFittingIdeal
import Mathlib.RingTheory.Finiteness.Prod
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.RingTheory.PresentationFittingIdeal
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Zeroth Fitting ideal of a finite module

Source: Stacks Project, More on Algebra, Tags 07Z8 and 07ZA (blueprint: def-trf-fitting-ideal-zero).

This module chooses a finite free surjection and takes its zeroth kernel-minor ideal.  The
recorded presentation-independence theorem makes this choice independent of the surjection.
-/

@[expose] public section

universe u v

namespace LinearMap

/-- The zeroth Fitting ideal of a finitely generated module, obtained from a finite free
surjection.  Independence of the chosen surjection is
`presentationFittingIdeal_independence_baseChange` (blueprint: def-trf-fitting-ideal-zero). -/
noncomputable def fittingIdealZero {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] : Ideal R :=
  let h := Module.Finite.exists_fin' R M
  let hn := Classical.choose_spec h
  let π := Classical.choose hn
  π.presentationFittingIdeal 0

end LinearMap
```

The item has a copyright header, `module`, `@[expose] public section`, and imports:

```lean
public import Sheaf.RingTheory.FittingIdealZero
import Mathlib.RingTheory.Ideal.Operations
```

## Users

`tools/downstream.py Sheaf.RingTheory.FittingIdealZero --uses LinearMap.fittingIdealZero`
lists only the item downstream. The definition's elaborated type and value are preserved;
no target meaning changes and no other consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.FittingIdealZero | unclaimed | Module conversion; definition unchanged. |
| Sheaf.RingTheory.FittingIdealDirectSum | D5 | Module conversion and complete proof. |

## Status

landed 20261023T123435-L-1188192 2026-10-23 (merge of deliver/D5/Sheaf.RingTheory.FittingIdealDirectSum)
