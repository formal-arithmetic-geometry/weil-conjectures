/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.CompletionInternalHomQuotientIso
import WeilConjectures.AlgebraicGeometry.CompletionInternalHomQuotientAnnihilation

/-! # Internal Hom factorization through ideal-power quotients

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, construction of the map.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Postcomposition with the level-n quotient kills the level-n ideal product of
internal Hom. Maps into that quotient factor uniquely through the level-m source
quotient whenever n ≤ m.

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, construction of its map;
Section 0EHN, equation 0880. -/
theorem completion_internal_hom_quotient {X : Scheme.{u}}
    (I : X.IdealSheafData) (F G : X.Modules) (m n : ℕ) (h : n ≤ m) :
    (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2
        (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) G F) ≫
      SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
        (𝟙 G) (formalModuleQuotientπ I n F) = 0) ∧
    IsIso (SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
      (formalModuleQuotientπ I m G) (𝟙 (formalModuleQuotient I n F))) := by
  constructor
  · exact completion_internal_hom_quotient_annihilation I F G n
  · exact completion_internal_hom_quotient_isIso I F G m n h

end AlgebraicGeometry
