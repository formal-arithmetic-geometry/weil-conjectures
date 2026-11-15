/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Open-complement cohomological-dimension condition

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
`sk-prop-a1-kummer/def-exc-open-complement-bound.md` (blueprint:
`theorem-f-shriek-finite-coefficients--1`).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The open-complement condition at a finite coefficient ring: higher direct images along
an open immersion vanish above the prescribed bound, and all higher direct images of
constructible coefficient sheaves remain constructible.

Source: blueprint node `theorem-f-shriek-finite-coefficients--1`, order 1914
(blueprint: theorem-f-shriek-finite-coefficients--1).

Proof: This is a definition. The first conjunct is clause (1) of the node: for every
sheaf of `A`-modules on `Vₑₜ` and every integer `q` strictly above `c`, the `q`th
cohomology sheaf of the canonical right-derived direct image is zero. The second
conjunct is clause (2): for every constructible sheaf and every integer `q`, that
same cohomology sheaf is constructible on `Tₑₜ`.
-/
def HasOpenComplementCondition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (c : ℕ) : Prop :=
  (∀ (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      (q : ℤ), (c : ℤ) < q →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj M)))) ∧
    (∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
      IsConstructibleEtaleModuleSheaf F →
      IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) j).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))))

end AlgebraicGeometry.Scheme

end
