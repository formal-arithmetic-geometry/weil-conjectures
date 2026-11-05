/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.StrictSquareArrowUniversal

/-!
# Universal localized arrows to derived restriction of pro-étale scalars

Let `q : R →+* S` be a ring morphism and `δ : Φ₁ ⟶ Φ₀ ⋙ Res_q` a termwise arrow of functors to
pro-étale sheaves of modules. On a complex `P` such that `Φ₁(P)` is K-flat and the transposes
`S ⊗_R Φ₁(Pⁱ) ⟶ Φ₀(Pⁱ)` of `δ` are invertible, the localized arrow
`Functor.strictSquareArrow Φ₁ Φ₀ Res_q δ P` is a universal arrow to derived restriction of
scalars: derived extension of scalars is computed on K-flat complexes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

-- As in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars`.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

variable {Y : Scheme.{u}} {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
  {C : Type*} [Category C] [Preadditive C]
  (Φ₁ : C ⥤ Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R))
  (Φ₀ : C ⥤ Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} S)) [Φ₁.Additive] [Φ₀.Additive]

end AlgebraicGeometry.ProEtale
