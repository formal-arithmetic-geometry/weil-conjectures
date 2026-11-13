/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.ModuleCechResolutionColumns
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation

/-! # Affine acyclicity makes the beta augmentation a quasi-isomorphism

## References

* [Stacks, Cohomology of Schemes, Tag 01XD]
* [Stacks, Cohomology of Sheaves, Tags 01ET and 01EQ]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

local instance localInst_ModuleCechBetaAffineQuasiIso_1
    (R : Type u) [Ring R] (J : Type u) [Small.{u} J] :
    HasLimitsOfShape (Discrete J) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

/-- The augmentation from the Cech complex of a quasi-coherent module into the total
Cech complex of an injective resolution is a quasi-isomorphism when every finite
intersection is affine. No covering hypothesis is needed
(Stacks, Tags 01XD, 01ET and 01EQ). -/
theorem moduleCechBeta_quasiIso_of_affine {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (F : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    (I : InjectiveResolution F) : QuasiIso (moduleCechBeta U I) := by
  let A := (CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat
  let a : A ⟶ (moduleCechDouble U I).X 0 :=
    (CategoryTheory.cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (Opposite.op ⊤) isTerminalTop.op).map
        (I.ι.f 0).val)
  have ha : a ≫ (moduleCechDouble U I).d 0 1 = 0 := by
    let G := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.forgetToPresheafModuleCat (Opposite.op ⊤) isTerminalTop.op ⋙
        CategoryTheory.cechComplexFunctor U
    change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
    rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]
  have hcol := moduleCech_resolution_columns U F I (by
    intro n y p hp
    exact subsingleton_openModuleCohomology_of_isAffineOpen X F _ (hU n y) p hp) ha
  apply HomologicalComplex₂.quasiIso_of_column_augmentation
    (moduleCechDouble U I) A a ha (moduleCechBeta U I)
  · intro n
    rfl
  · exact hcol

end AlgebraicGeometry.Scheme.Modules
