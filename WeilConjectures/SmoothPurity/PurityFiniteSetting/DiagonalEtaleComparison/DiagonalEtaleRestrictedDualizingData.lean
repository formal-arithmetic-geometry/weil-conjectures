/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData

/-! # Dualizing transport over the restricted target

Source: diagonal-dualizing proof Steps 1--2; orientation-charts proof Step 3.
(blueprint: def-pur-diagonal-etale-restricted-dualizing-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison

/-- Transport between the two restricted dualizing objects through their common source.
The construction uses the specified normalized exceptional locality, evaluated on the
monoidal unit, and the ordinary/pro-etale pullback comparison. It contains no diagonal
section invariant or alpha, target-open rho, or coefficient-unit change.
Source: diagonal-dualizing proof Steps 1--2, orientation-charts proof Step 3.
(blueprint: def-pur-diagonal-etale-restricted-dualizing-transport). -/
def restrictedDualizingTransport (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsNoetherian X] [IsNoetherian Z] [IsNoetherian Y]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j]
    (v : U ⟶ Z) [Etale v] [IsSeparated v]
    (w : v ≫ g = j ≫ f)
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    (vO : O.toScheme ⟶ (g ⁻¹ᵁ V.1).toScheme)
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j)
    (hv : vO ≫ (g ⁻¹ᵁ V.1).ι = O.ι ≫ v) :
    (OrientationRefinement.pull P jO).obj
        (OrientationRefinement.omega P (f ∣_ V.1) (V.1.ι ≫ aY)) ≅
      (OrientationRefinement.pull P vO).obj
        (OrientationRefinement.omega P (g ∣_ V.1) (V.1.ι ≫ aY)) := by
  letI := P.noetherian (V.1.ι ≫ aY)
  letI := P.noetherian ((f ∣_ V.1) ≫ V.1.ι ≫ aY)
  letI := P.noetherian ((g ∣_ V.1) ≫ V.1.ι ≫ aY)
  letI := P.noetherian (O.ι ≫ j ≫ f ≫ aY)
  have : Etale (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : Etale jO := Etale.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : Etale (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : Etale vO := Etale.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : IsSeparated (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : IsSeparated jO := IsSeparated.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : IsSeparated (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : IsSeparated vO := IsSeparated.of_comp vO (g ⁻¹ᵁ V.1).ι
  have he : vO ≫ (g ∣_ V.1) = jO ≫ (f ∣_ V.1) := by
    apply (cancel_mono V.1.ι).mp
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
      ← Category.assoc, hv, ← Category.assoc, hj]
    simp only [Category.assoc, w]
  let unitCongr {q q' : O.toScheme ⟶ V.1.toScheme}
      [HasCompactification q] [HasCompactification q'] (heq : q = q') :
      Etale.dualizingComplex P.Coefficient q =
        Etale.dualizingComplex P.Coefficient q' := by
    cases heq
    rfl
  exact Dnc.pullComparison P jO _ ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) O.toScheme).mapDerivedCategory.mapIso
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) jO).app _ ≪≫
          (Etale.tensorMateEtalePrecompLocalityIso
            P.Coefficient N jO (f ∣_ V.1)).app (𝟙_ _) ≪≫
          eqToIso (unitCongr he.symm) ≪≫
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} P.Coefficient) vO).app _ ≪≫
            (Etale.tensorMateEtalePrecompLocalityIso
              P.Coefficient N vO (g ∣_ V.1)).app (𝟙_ _)).symm) ≪≫
      (Dnc.pullComparison P vO _).symm

end WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
