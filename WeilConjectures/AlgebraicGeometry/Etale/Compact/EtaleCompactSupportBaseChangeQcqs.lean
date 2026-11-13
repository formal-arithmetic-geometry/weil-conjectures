/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement

/-!
# Arbitrary base change for compact support on qcqs etale sites
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For finite constant coefficients, compact support computed with a fixed compactification
commutes with arbitrary change of qcqs base, naturally in the bounded below complex. -/
theorem etale_compactSupport_baseChange_qcqs
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Y' : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y' ⟶ Y) (c : Compactification f) :
    Nonempty
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c ⋙
          (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus ≅
        (upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f g)).mapDerivedCategoryPlus ⋙
          rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
            (c.baseChange g)) := by
  let sq : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  have : IsIso (baseChange (ModuleCat.{u + 1} Λ)
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq) :=
    isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite
      (c.isPullback_g_ofIsPullback sq).flip
  let e := asIso (baseChange (ModuleCat.{u + 1} Λ)
    (c.isPullback_g_ofIsPullback sq).flip.toCommSq)
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (extensionZeroBaseChangeDerivedPlusIso Λ (c.isPullback_i_ofIsPullback sq)) _ ≪≫
    Functor.associator _ _ _⟩

end AlgebraicGeometry.Etale
