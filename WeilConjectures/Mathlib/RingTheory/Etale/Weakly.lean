/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localizations are weakly étale

A localization map `R → S⁻¹R` is weakly étale (Stacks, Tag 092J (1)): it is flat, and the
multiplication `S⁻¹R ⊗[R] S⁻¹R → S⁻¹R` is bijective.

This is ported from the `proetale` project (`Proetale.Mathlib.RingTheory.WeaklyEtale.Localization`).

## Main results

- `Algebra.WeaklyEtale.of_isLocalization`: a localization of `R` is a weakly étale `R`-algebra.
-/

@[expose] public section

namespace Algebra.WeaklyEtale

/-- If `T` is the localization of `R` at a submonoid `S`, then `T` is weakly étale over `R`. -/
@[stacks 092J "(1)"]
theorem of_isLocalization (R : Type*) [CommRing R] (S : Submonoid R)
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization S T] :
    Algebra.WeaklyEtale R T where
  flat := IsLocalization.flat T S
  flat_lmul' :=
    RingHom.Flat.of_bijective
      (f := (Algebra.TensorProduct.lmul' R (S := T)).toRingHom)
      (IsLocalization.bijective_linearMap_mul' (R := R) (A := T) S)

/-- The canonical localization `R → Localization S` is weakly étale. -/
instance localization (R : Type*) [CommRing R] (S : Submonoid R) :
    Algebra.WeaklyEtale R (Localization S) :=
  of_isLocalization R S _

end Algebra.WeaklyEtale
