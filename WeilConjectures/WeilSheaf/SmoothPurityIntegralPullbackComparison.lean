/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange

/-! # The underlying integral coefficient pullback -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable {X U : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g] (l : ℕ) [Fact l.Prime]

/-- The integral pullback commutes with forgetting the coefficient action. -/
noncomputable def purityIntegralPullbackForgetIso :
    Mod.forget (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X) ⋙
        (g)^*[Ab.{u + 1}] ≅
      (g)^*⟦Profinite.continuousMapRingObj ℤ_[l]⟧ ⋙
        Mod.forget (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) U) :=
  CondensedRing.upperStarForgetIso (Profinite.continuousMapRingObj ℤ_[l]) g

/-- The underlying pullback comparison at an integral coefficient module. -/
noncomputable def purityIntegralPullbackUnit
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X)) :=
  (purityIntegralPullbackForgetIso g l).hom.app M

/-- The coefficient-extension functor used by the integral pullback. -/
noncomputable def purityIntegralExtension :=
  Mod.extendScalars (condensedPullbackHom (Profinite.continuousMapRingObj ℤ_[l]) g)

/-- Factor the integral pullback before evaluating it on a module. -/
noncomputable def purityIntegralPullbackFactorIso :
    (g)^*⟦Profinite.continuousMapRingObj ℤ_[l]⟧ ≅
      ((g)^*[Ab.{u + 1}].mapMod
        (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X)) ⋙
          purityIntegralExtension g l :=
  Iso.refl _

variable {K : Type u} [Field K] (f : U ⟶ Spec (.of K)) {ζ : ℕ → K}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ l = ζ n)

/-- Transport the root trivialization through the factored pullback. -/
noncomputable def purityIntegralTateTrivialization :
    (g)^*⟦Profinite.continuousMapRingObj ℤ_[l]⟧.obj (tateModule X l) ≅
      (g)^*⟦Profinite.continuousMapRingObj ℤ_[l]⟧.obj (𝟙_ _) := by
  let e := (purityIntegralExtension g l).mapIso
    (upperStarMapModTateModuleIsoUnit g f l hζ hζ' ≪≫ (g)^*[Ab.{u + 1}].mapModUnitIso)
  exact (purityIntegralPullbackFactorIso g l).app _ ≪≫ e ≪≫
    ((purityIntegralPullbackFactorIso g l).app _).symm

end AlgebraicGeometry.ProEtale
