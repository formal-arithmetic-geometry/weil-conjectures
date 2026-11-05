/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement

/-!
# Cartesian coefficient sheaves

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-cartesian-coefficients/_section.md`, assertions (1), (2), and the final paragraph
(blueprint: sk-prop-sfb-cartesian-coefficients).

The assertions below use the published coefficient comparison and module pullback.
The inverse-image lift and its comparison with extension of scalars are actual constructions.
The signed lines are the recorded Tate twists, including their sectionwise module encoding.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}}

/-- The normalized finite signed comparisons over the recorded constant coefficient map.
The first-line formula fixes the map on root tensors; the second clause retains all
Kummer identifications. Every signed comparison includes zero, tensor and evaluation
normalizations, and is an isomorphism of coefficient modules in every degree.
Source: blueprint finite coefficients and powers and duals paragraphs
(blueprint: sk-prop-sfb-cartesian-coefficients). -/
@[irreducible] def CartesianFiniteTwistAssertions (ℓ : ℕ) [Fact ℓ.Prime] (f : X ⟶ Y)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] : Prop :=
  ∀ (A : Type u) [CommRing A] [Finite A],
    ∃ β : ∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* (ULift.{u + 1} A)),
      SpSignedComparison f (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A))
        (Scheme.tateFiniteCoefficient X (ULift.{u + 1} A))
        (StrictTower.constantRingIso (ULift.{u + 1} A) f)
        (Scheme.tateFiniteLine Y ℓ (ULift.{u + 1} A) r a)
        (Scheme.tateFiniteLine X ℓ (ULift.{u + 1} A) r a),
      (∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* (ULift.{u + 1} A)) (V : Y.ProEt)
        (b : (Scheme.tateFiniteCoefficient Y (ULift.{u + 1} A)).obj.obj (op V))
        (z : (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (r + 1))).obj.obj (op V)),
        (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
          ((β r a).signed 1).hom).val.app (op V)
            (Scheme.tateFiniteTensor Y ℓ (ULift.{u + 1} A) r a V b z) =
          Scheme.tateFiniteTensor X ℓ (ULift.{u + 1} A) r a ((Scheme.proEtaleBaseChange f).obj V)
            ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
              (CommRingCat.of (ULift.{u + 1} A))).hom.app (op V) b)
            ((Scheme.proEtaleRootsOfUnityDirectImageMap f (ℓ ^ (r + 1))).hom.app
              (op V) z)) ∧
      (∀ (r n : ℕ) (h : r ≤ n) (a : ZMod (ℓ ^ (r + 1)) →+* (ULift.{u + 1} A)),
        (Scheme.proEtaleRingModulePullback f _ _ _).map
          (spFiniteKummer Y ℓ (ULift.{u + 1} A) r n h a) ≫ ((β r a).signed 1).hom =
        ((β n (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ h))
          (ZMod (ℓ ^ (r + 1)))))).signed 1).hom ≫ spFiniteKummer X ℓ (ULift.{u + 1} A) r n h a)

end AlgebraicGeometry.ProEtale
