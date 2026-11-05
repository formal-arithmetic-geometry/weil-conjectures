/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.BoundedOpenForget
public import WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionForgetSquare
public import WeilConjectures.WeilSheaf.Native.Projection.BoundedProjectionIso
public import WeilConjectures.WeilSheaf.Native.Projection.BoundedForgetNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.GeometricProjectionNaturality
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion

/-! # The open projection square on Weil complexes -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  (j : U ⟶ Z) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] [QuasiCompact j]

local notation "jb" => geometricFiberHom (k₀ := k₀) j
local notation "Λ" => Profinite.padicAlgClRingObj l

/-- The bounded open forget comparison is a restriction of the composite realization square. -/
lemma projectionOpenForgetIso_hom_app (M : WeilComplex k₀ l U) :
    ((projectionOpenForgetIso k₀ l j).hom.app M).hom =
      (projectionOpenCompositeForgetIso k₀ l j).hom.app M.obj := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the open projection isomorphism gives the geometric open projection map. -/
theorem projectionForgetSquare_open :
    ProjectionForgetSquare (projectionOpenForgetIso k₀ l j)
      (compactProjectionForgetUpperStarIso k₀ l j)
      (compactProjectionForgetTensorIso k₀ l U) (compactProjectionForgetTensorIso k₀ l Z)
      (nativeBoundedOpenProjectionIso (k₀ := k₀) (l := l) j).hom
      ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l jb).
        invProjectionComparisonNatTrans (fun _ _ ↦ inferInstance)) := by
  let B := CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ jb.left
  have h₀ : ProjectionForgetSquare (ProEtaleWeilSheaf.nativeOpenForgetIso k₀ l j)
      (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l j).symm
      (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l U)
      (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l Z)
      (ProEtaleWeilSheaf.nativeOpenProjectionIso k₀ l j).hom
      (B.uncurriedInvProjectionComparisonNatTrans (fun _ _ ↦ inferInstance)) :=
    ProEtaleWeilSheaf.nativeOpenProjection_forgetSquare k₀ l j
  have h := projectionForgetSquare_of_iso _ _ _ _
    (projectionRealizationCompIso k₀ l U) (projectionRealizationCompIso k₀ l Z) _ _ h₀
  intro M N
  apply ObjectProperty.hom_ext
  have hm := h M.obj N.obj
  let b := CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l jb
  have hg : (inv (b.projectionComparison ((compactProjectionForget k₀ l U).obj M)
      ((compactProjectionForget k₀ l Z).obj N))).hom =
    inv (B.projectionComparison ((compactProjectionForget k₀ l U).obj M).obj
      ((compactProjectionForget k₀ l Z).obj N).obj) := by
    change (boundedConstructible _).ι.map (inv (b.projectionComparison _ _)) = _
    rw [Functor.map_inv, CondensedRing.boundedConstructibleOpenImmersionProjectionComparison_hom]
  change _ ≫ _ ≫ _ = _ ≫ _ ≫
    (inv (b.projectionComparison ((compactProjectionForget k₀ l U).obj M)
      ((compactProjectionForget k₀ l Z).obj N))).hom
  rw [hg]
  simp only [nativeBoundedOpenProjectionIso_hom_app, projectionOpenForgetIso_hom_app,
    compactProjectionForgetTensorIso_hom_app, compactProjectionForgetUpperStarIso_hom_app]
  exact hm

end AlgebraicGeometry.WeilComplex
