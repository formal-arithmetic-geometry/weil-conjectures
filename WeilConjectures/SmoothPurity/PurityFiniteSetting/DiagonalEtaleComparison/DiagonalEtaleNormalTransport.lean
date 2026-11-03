/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSectionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.DiagonalOrientationRefinementData

/-! # The canonical normal comparison on an etale correspondence

The comparison factors through the actual normal cone of the common source diagonal.
No DNC orientation, beta comparison or localInverse occurs in its construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison

/-- The normal comparison induced by the two actual Rees zero-fibre maps.
Only the diagonal geometry, never beta or the DNC isomorphism, enters it.
(blueprint: def-pur-diagonal-etale-normal-transport). -/
def normalTransport (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V)
    (K : P.AffineDiagonalGeometry g aY d V)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j]
    (v : U ⟶ Z) [Etale v] [IsSeparated v]
    (w : v ≫ g = j ≫ f)
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    (vO : O.toScheme ⟶ (g ⁻¹ᵁ V.1).toScheme)
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j)
    (hv : vO ≫ (g ⁻¹ᵁ V.1).ι = O.ι ≫ v) :
    (OrientationRefinement.pull P jO).obj
        (OrientationRefinement.normal P f aY d V H) ≅
      (OrientationRefinement.pull P vO).obj
        (OrientationRefinement.normal P g aY d V K) := by
  letI := H.smoothDimension
  letI := K.smoothDimension
  have : Etale (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : Etale jO := Etale.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : Etale (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : Etale vO := Etale.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : IsSeparated (jO ≫ (f ⁻¹ᵁ V.1).ι) := by rw [hj]; infer_instance
  have : IsSeparated jO := IsSeparated.of_comp jO (f ⁻¹ᵁ V.1).ι
  have : IsSeparated (vO ≫ (g ⁻¹ᵁ V.1).ι) := by rw [hv]; infer_instance
  have : IsSeparated vO := IsSeparated.of_comp vO (g ⁻¹ᵁ V.1).ι
  have : QuasiCompact jO := inferInstance
  have : QuasiCompact vO := inferInstance
  have : SmoothOfRelativeDimension 0 jO :=
    (Etale.iff_smoothOfRelativeDimension_zero jO).mp inferInstance
  let h := jO ≫ (f ∣_ V.1)
  have hdim : SmoothOfRelativeDimension (0 + d) h :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + d) (jO ≫ (f ∣_ V.1)))
  have : SmoothOfRelativeDimension d h :=
    Eq.mp (congrArg (fun n => SmoothOfRelativeDimension n h) (Nat.zero_add d)) hdim
  have he : vO ≫ (g ∣_ V.1) = h := by
    apply (cancel_mono V.1.ι).mp
    dsimp only [h]
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι,
      ← Category.assoc, hv, ← Category.assoc, hj]
    simp only [Category.assoc, w]
  exact (normal P d (f ∣_ V.1) h (V.1.ι ≫ aY) jO rfl).symm ≪≫
    normal P d (g ∣_ V.1) h (V.1.ι ≫ aY) vO he

end WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
