/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.TraceFormula.PurityDevissage
public import WeilConjectures.SmoothPurity.OrientationCanonical
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs

/-! # Étale lower shriek is left adjoint to pullback

The already established geometric smooth-purity theorem identifies the exceptional
pullback with pullback tensored by its value on the unit. In relative dimension zero,
that value is isomorphic to the unit. This argument requires no Weil equivariance.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (h : U ⟶ X) [Etale h.left]

/-- Geometric purity in relative dimension zero identifies the relative dualizing
object with the unit. -/
def purityEtaleUpperShriekUnitIso :
    (boundedConstructibleUpperShriek ℓ h).obj (𝟙_ _) ≅ 𝟙_ _ := by
  have : SmoothOfRelativeDimension 0 h.left := inferInstance
  let e := (nonempty_iso_tateTwist_upperShriekUnit ℓ h 0).some
  exact e.symm ≪≫ (ObjectProperty.fullyFaithfulι _).preimageIso
    (((shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).app _)
      ≪≫ tateTwistDerivedZeroIso ℓ U.left)

/-- Étale exceptional pullback agrees with ordinary derived pullback on every
bounded constructible object. -/
def purityEtaleUpperShriekIsoUpperStar :
    boundedConstructibleUpperShriek ℓ h ≅
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := U) h.left := by
  have : IsIso (upperShriekUnitTensorMapNatTrans ℓ h) := by
    apply NatIso.isIso_of_isIso_app
    intro K
    exact isIso_upperShriekUnitTensorMap_of_smooth ℓ h K
  exact (Functor.leftUnitor _).symm ≪≫ (asIso (upperShriekUnitTensorMapNatTrans ℓ h)).symm ≪≫
    Functor.isoWhiskerLeft _
      ((tensoringRight _).mapIso (purityEtaleUpperShriekUnitIso ℓ h) ≪≫ rightUnitorNatIso _) ≪≫
    Functor.rightUnitor _

/-- For étale `h`, the compactification-defined `Rh_!` is left adjoint to `h^*`. -/
theorem nonempty_boundedConstructibleLowerShriekUpperStarAdjunction_of_etale :
    Nonempty (boundedConstructibleLowerShriek ℓ h ⊣
      boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := U) h.left) :=
  ⟨(boundedConstructibleUpperShriekAdjunction ℓ h).ofNatIsoRight
    (purityEtaleUpperShriekIsoUpperStar ℓ h)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
