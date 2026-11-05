/-
Copyright (c) 2026 The Weil conjectures formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (u9 C1), after a suggestion of Nailin Guan (Zulip #1864)
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4CoefficientInterface

/-! # The concrete instance with OPAQUE coefficient rings

Same statement and proof as `purity_finiteCoefficientIntegralTateOneReading_pullback_coeffSyn`,
but in a module importing the synonyms, where `coeffRingObj` / `coeffType` (and the rebuilt
inputs) are not exposed: neither the elaborator nor the kernel can unfold the coefficient rings,
so every comparison is syntactic. -/

set_option profiler true
set_option profiler.threshold 0

public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
namespace K4CoefficientInterface

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) {k : Type u} [Field k] [NeZero (ℓ : k)] {X Y : Scheme.{u}} (g : X ⟶ Y)
  (f : Y ⟶ Spec (.of k))

/-- The concrete instance over opaque coefficient rings. -/
theorem finiteTateReading_pullback :
    (coeffComparison ℓ E n X).map ((coeffPullInv ℓ E n g).app (integralTateTwistOne Y ℓ E)) ≫
        (coeffComparison ℓ E n X).map
          ((Mod.extendScalars (coeffReduction ℓ E n X)).map
            (upperStarIntegralTateTwistOneIso ℓ E g f).hom) ≫
        (coeffTateReadingIso ℓ E n (g ≫ f)).hom =
      (coeffPullbackIso ℓ E n g).hom.app
          ((Mod.extendScalars (coeffReduction ℓ E n Y)).obj (integralTateTwistOne Y ℓ E)) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} (coeffType.{u} ℓ E n)) g).map
          (coeffTateReadingIso ℓ E n f).hom ≫
        coeffTatePull ℓ E n g :=
  purity_reading_composition_named (CondensedRing.upperStar (coeffRingObj.{u} ℓ E n) g)
    (coeffComparison ℓ E n Y) (coeffComparison ℓ E n X)
    (ProEtale.upperStar (ModuleCat.{u + 1} (coeffType.{u} ℓ E n)) g) (coeffPullbackIso ℓ E n g)
    (Mod.extendScalars (coeffReduction ℓ E n Y))
    (CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E) g ⋙
      Mod.extendScalars (coeffReduction ℓ E n X))
    (coeffPullInv ℓ E n g) (integralTateTwistOne Y ℓ E)
    ((Mod.extendScalars (coeffReduction ℓ E n X)).map
      (upperStarIntegralTateTwistOneIso ℓ E g f).hom)
    (coeffReductionIso ℓ E n (g ≫ f)) (coeffReductionIso ℓ E n f)
    ((freeFunctorCompUpperStarIso (coeffRingObj.{u} ℓ E n) g).hom.app
      (rootsOfUnitySheaf Y (ℓ ^ n)))
    ((Mod.freeFunctor (condensedRingObj (coeffRingObj.{u} ℓ E n) X)).map
      (upperStarRootsOfUnitySheafHom g (ℓ ^ n)))
    (coeffRootReadingIso ℓ E n (g ≫ f)) (coeffRootReadingIso ℓ E n f) (coeffTatePull ℓ E n g)
    (coeffTateReadingIso ℓ E n (g ≫ f)) (coeffTateReadingIso ℓ E n f)
    (coeffTateReadingIso_eq ℓ E n (g ≫ f)) (coeffTateReadingIso_eq ℓ E n f)
    (coeffHred ℓ E n g f) (coeffHread ℓ E n g f)

end K4CoefficientInterface
end AlgebraicGeometry.ProEtale
