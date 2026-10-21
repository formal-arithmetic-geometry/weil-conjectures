/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound
import Sheaf.Paper.StrictHenselizationFunctoriality

/-!
# Universal finite cohomological dimension for torsion coefficients

Source: Zheng, Künneth formula for nearby cycles, Definition A.1 and the sentence
before Remark A.2, p. 1 (blueprint: lem-trf-finite-type-torsion-universal-star).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finite type morphism with torsion coefficients satisfies the universal
nearby-cycle finiteness condition.

Source: Zheng, Künneth formula for nearby cycles, Definition A.1 and the sentence before
Remark A.2, p. 1 (blueprint: lem-trf-finite-type-torsion-universal-star).
Proof: after an arbitrary base change, cover the source by affine charts over affine
charts of the target. Each chart morphism is of finite type and has a uniform fibre
dimension bound. The torsion strict-local Gabber bound gives vanishing above twice this
bound, and strict-localization functoriality identifies the chart calculation with the
original base-changed morphism. The bound is uniform on each chart and the base change
was arbitrary.
-/
theorem finiteTypeTorsion_universalStar
    {X Y : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    (m : ℕ) (hm : 1 ≤ m) (hΛ : ∀ a : Λ, (m : Λ) * a = 0)
    (g : X ⟶ Y) [LocallyOfFiniteType g] :
    ∀ (Y' : Scheme.{u}) (b : Y' ⟶ Y),
      ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
        (x' : Spec (.of Ω) ⟶ pullback g b),
        ∃ U : (pullback g b).Opens, x' (IsLocalRing.closedPoint Ω) ∈ U ∧
          ∃ N : ℕ, ∀ (q : ℕ), N < q →
            ∀ (F : Sheaf (Scheme.strictHenselizationScheme x').smallEtaleTopology
                (ModuleCat.{u + 1} Λ)),
              IsZero
                ((DerivedCategory.Plus.homologyFunctor
                    (Sheaf (Scheme.strictHenselizationScheme
                      (x' ≫ pullback.snd g b)).smallEtaleTopology
                      (ModuleCat.{u + 1} Λ)) (q : ℤ)).obj
                  ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)
                      (Scheme.strictHenselizationMap (pullback.snd g b) x')).obj
                    ((DerivedCategory.Plus.singleFunctor
                      (Sheaf (Scheme.strictHenselizationScheme x').smallEtaleTopology
                        (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  sorry

end AlgebraicGeometry
