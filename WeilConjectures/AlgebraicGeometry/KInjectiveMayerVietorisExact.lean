/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisDegreewise

/-! # Exactness of the concrete direct-image Mayer--Vietoris complex

## References

* Stacks Project, Cohomology, Tag 08BV, using Tag 01EB and Tag 01EA.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

/-- The concrete restriction/direct-image diagram is short exact for a cover and
an arbitrary complex with injective terms. K-injectivity is not needed here. -/
theorem schemeMayerVietorisComplex_shortExact
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    (schemeMayerVietorisComplex X U V I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact schemeMayerVietorisComplex_degreewise_shortExact X U V hcover I n (hI n)

end AlgebraicGeometry
