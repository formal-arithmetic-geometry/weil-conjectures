/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Complements on fraction rings

## Main results

- `IsFractionRing.map_algebraMap` — the map of fraction fields `IsFractionRing.map hj` induced by
  an injective ring map `j : A →+* B` extends `j`.
-/

@[expose] public section

namespace IsFractionRing

variable {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing K] [Algebra A K]
  [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L] {j : A →+* B}

/-- The map of fraction fields induced by an injective ring map `j : A →+* B` extends `j`:
```
  A ---j---> B
  |          |
  v          v
  K -------> L
```
-/
@[simp]
lemma map_algebraMap (hj : Function.Injective j) (a : A) :
    map (K := K) (L := L) hj (algebraMap A K a) = algebraMap B L (j a) :=
  IsLocalization.map_eq _ a

end IsFractionRing
