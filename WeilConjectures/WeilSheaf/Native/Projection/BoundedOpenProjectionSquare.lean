/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.BoundedOpenForget
public import WeilConjectures.WeilSheaf.Native.Projection.BoundedProjectionIso
public import WeilConjectures.WeilSheaf.Native.Projection.BoundedForgetNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.GeometricProjectionNaturality
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion

/-! # The open projection square on Weil complexes -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Endofunctor

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

local instance : IsOpenImmersion (jb).left :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsOpenImmersion) j
    (comp_over j (Spec (CommRingCat.of k₀))) ‹_›

/-- The bounded open forget comparison is a restriction of the composite realization square. -/
lemma projectionOpenForgetIso_hom_app (M : WeilComplex k₀ l U) :
    ((projectionOpenForgetIso k₀ l j).hom.app M).hom =
      (projectionOpenCompositeForgetIso k₀ l j).hom.app M.obj := rfl

omit [QuasiCompact j] in
/-- The inverse bounded open projection comparison has the ambient inverse as its component. -/
lemma projectionOpenProjectionComparison_inv_hom (M : WeilComplex k₀ l U)
    (N : WeilComplex k₀ l Z) :
    (inv ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l
        jb).projectionComparison
      ((compactProjectionForget k₀ l U).obj M)
        ((compactProjectionForget k₀ l Z).obj N))).hom =
      inv ((CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ
        (jb).left).projectionComparison ((compactProjectionForget k₀ l U).obj M).obj
          ((compactProjectionForget k₀ l Z).obj N).obj) := by
  have h := CondensedRing.boundedConstructibleOpenImmersionProjectionComparison_hom l jb
    ((compactProjectionForget k₀ l U).obj M) ((compactProjectionForget k₀ l Z).obj N)
  change ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l
      jb).projectionComparison
    ((compactProjectionForget k₀ l U).obj M)
      ((compactProjectionForget k₀ l Z).obj N)).hom = _ at h
  rw [ObjectProperty.hom_inv]
  exact IsIso.inv_eq_inv.mpr h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the open projection isomorphism gives the geometric open projection map. -/
theorem projectionForgetSquare_open :
    ProjectionForgetSquare (projectionOpenForgetIso k₀ l j)
      (compactProjectionForgetUpperStarIso k₀ l j)
      (compactProjectionForgetTensorIso k₀ l U) (compactProjectionForgetTensorIso k₀ l Z)
      (nativeBoundedOpenProjectionIso (k₀ := k₀) (l := l) j).hom
      ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l
        jb).invProjectionComparisonNatTrans
        (fun _ _ ↦ inferInstance)) := by
  let B := CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ (jb).left
  have h₀ : ProjectionForgetSquare (ProEtaleWeilSheaf.nativeOpenForgetIso k₀ l j)
      (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l j).symm
      (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l U)
      (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l Z)
      (ProEtaleWeilSheaf.nativeOpenProjectionIso k₀ l j).hom
      (B.uncurriedInvProjectionComparisonNatTrans (fun _ _ ↦ inferInstance)) := by
    apply (projectionForgetSquare_uncurried_iff _ _ _ _ _ _).2
    intro M N
    exact ProEtaleWeilSheaf.map_nativeOpenProjectionIso_hom_app k₀ l j M N
  have h := projectionForgetSquare_of_iso _ _ _ _
    (projectionRealizationCompIso k₀ l U) (projectionRealizationCompIso k₀ l Z) _ _ h₀
  apply (projectionForgetSquare_monoidal_iff _ _ _ _ _ _).2
  intro M N
  apply ObjectProperty.hom_ext
  have hm := (projectionForgetSquare_uncurried_iff _ _ _ _ _ _).1 h M.obj N.obj
  let b := CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ l jb
  have hg := projectionOpenProjectionComparison_inv_hom k₀ l j M N
  change _ ≫ _ ≫ _ = _ ≫ _ ≫
    (inv (b.projectionComparison ((compactProjectionForget k₀ l U).obj M)
      ((compactProjectionForget k₀ l Z).obj N))).hom
  rw [hg]
  change ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)).mapDerivedCategory ⋙
      (adicSheafEquivCondensedMod l _).functor.mapDerivedCategory).map
        (((nativeBoundedOpenProjectionIso j).hom.app (M, N)).hom) ≫
      ((projectionOpenForgetIso k₀ l j).hom.app _).hom ≫
      (CondensedRing.openImmersionLowerShriek Λ (jb).left).mapDerivedCategory.map
        (((compactProjectionForgetTensorIso k₀ l U).hom.app (M, (upperStar j).obj N)).hom ≫
          ((compactProjectionForget k₀ l U).obj M).obj ◁
            ((compactProjectionForgetUpperStarIso k₀ l j).hom.app N).hom) =
    ((compactProjectionForgetTensorIso k₀ l Z).hom.app ((extensionByZero j).obj M, N)).hom ≫
      ((projectionOpenForgetIso k₀ l j).hom.app M).hom ▷
        ((compactProjectionForget k₀ l Z).obj N).obj ≫ _
  simp only [nativeBoundedOpenProjectionIso_hom_app, projectionOpenForgetIso_hom_app,
    compactProjectionForgetTensorIso_hom_app, compactProjectionForgetUpperStarIso_hom_app]
  exact hm

end AlgebraicGeometry.WeilComplex
