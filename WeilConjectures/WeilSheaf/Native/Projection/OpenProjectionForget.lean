/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionIso
public import WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionForgetFormal
public import WeilConjectures.WeilSheaf.Native.Projection.UncurriedComparison
public import WeilConjectures.PoincareDuality.ProjectionFormula

/-! # The canonical open projection formula under condensed realization -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

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
  (j : U ⟶ Z) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j]

local notation "jb" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))
local notation "Λ" => Profinite.padicAlgClRingObj l

local instance : IsOpenImmersion jb :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsOpenImmersion) j _ ‹_›

/-- The inverse mate of the pullback comparison is invertible for extension by zero. -/
instance isIso_nativeOpenForgetInverseMate :
    IsIso ((mateEquiv (derivedExtensionByZeroUpperStarAdjunction k₀ l j)
      (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ jb)).symm
      (TwoSquare.mk _ _ _ _ (derivedCondensedRealizationUpperStarIso k₀ l j).inv)).natTrans := by
  apply NatIso.isIso_of_isIso_app
  intro M
  let e := Functor.isoHComp
    (IsoAlgebra.mapOfNatIsoCompForgetIso
      (adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l j
        (comp_over j (Spec (CommRingCat.of k₀))))).symm
    (adicOpenImmersionLowerShriekCompCondensedModIso l _ jb).symm
  exact isIso_inverseMate_of_extension_image
    (derivedExtensionByZeroUpperStarAdjunction k₀ l j)
    (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ jb)
    (derivedCondensedRealizationUpperStarIso k₀ l j).symm M
    ((derivedCondensedRealization k₀ l U).obj M)
    ((Functor.mapDerivedCategorySquareIso e).app M).symm

/-- The open forget comparison fixed by its mate, the canonical pullback comparison. -/
def nativeOpenForgetIso :
    nativeOpenExtension k₀ l j ⋙ derivedCondensedRealization k₀ l Z ≅
      derivedCondensedRealization k₀ l U ⋙
        (CondensedRing.openImmersionLowerShriek Λ jb).mapDerivedCategory :=
  (asIso ((mateEquiv (derivedExtensionByZeroUpperStarAdjunction k₀ l j)
    (CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ jb)).symm
    (TwoSquare.mk _ _ _ _ (derivedCondensedRealizationUpperStarIso k₀ l j).inv)).natTrans).symm

/-- The canonical open projection isomorphism lies over the geometric projection formula. -/
lemma map_nativeOpenProjectionIso_hom_app
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l U))
    (N : DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) :
    (derivedCondensedRealization k₀ l Z).map ((nativeOpenProjectionIso k₀ l j).hom.app (M, N)) ≫
      (nativeOpenForgetIso k₀ l j).hom.app
        ((nativeDerivedTensor k₀ l U).obj (M, (nativeOpenPull k₀ l j).obj N)) ≫
      (CondensedRing.openImmersionLowerShriek Λ jb).mapDerivedCategory.map
        ((condensedRealizationTensor k₀ l U).hom.app (M, (nativeOpenPull k₀ l j).obj N) ≫
          (derivedCondensedRealization k₀ l U).obj M ◁
            (derivedCondensedRealizationUpperStarIso k₀ l j).inv.app N) =
    (condensedRealizationTensor k₀ l Z).hom.app ((nativeOpenExtension k₀ l j).obj M, N) ≫
      (nativeOpenForgetIso k₀ l j).hom.app M ▷ (derivedCondensedRealization k₀ l Z).obj N ≫
      inv (CondensedRing.openImmersionProjectionComparison Λ jb
        ((derivedCondensedRealization k₀ l U).obj M)
        ((derivedCondensedRealization k₀ l Z).obj N)) := by
  let adj := derivedExtensionByZeroUpperStarAdjunction k₀ l j
  let adj' := CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ jb
  let ρ' := Functor.uncurryCompIsoOfIso (CondensedRing.leftDerivedUpperStarTensorIso Λ jb)
  have hu := compactProjectionOpen_unitSquare_of_inverseMate adj adj'
    (derivedCondensedRealizationUpperStarIso k₀ l j).symm
  have hr := Functor.comparisonCompatible_uncurried
    (derivedCondensedRealizationUpperStarIso k₀ l j).symm
    (condensedRealizationTensor k₀ l U) (condensedRealizationTensor k₀ l Z)
    (nativePullTensor k₀ l j) (CondensedRing.leftDerivedUpperStarTensorIso Λ jb)
    (comparisonCompatible_derivedCondensedRealization k₀ l j)
  have hg' : adj'.homEquiv _ _
      (CondensedRing.openImmersionProjectionComparison Λ jb
        ((derivedCondensedRealization k₀ l U).obj M)
        ((derivedCondensedRealization k₀ l Z).obj N)) =
      (Functor.uncurry.obj (curriedTensor _)).map
        (Prod.mkHom (adj'.unit.app ((derivedCondensedRealization k₀ l U).obj M)) (𝟙 _)) ≫
          ρ'.inv.app
            ((CondensedRing.openImmersionLowerShriek Λ jb).mapDerivedCategory.obj
              ((derivedCondensedRealization k₀ l U).obj M),
                (derivedCondensedRealization k₀ l Z).obj N) := by
    rw [CondensedRing.openImmersionProjectionComparison, Adjunction.projectionComparison,
      Adjunction.projectionMap_app_app, Equiv.apply_symm_apply]
    simp [Adjunction.projectionMapTranspose, ρ', Functor.uncurryCompIsoOfIso,
      Functor.uncurry_obj_map]
  have h := compactProjectionOpen_forget_of_unit_at adj adj'
    (derivedCondensedRealization k₀ l U) (derivedCondensedRealization k₀ l Z)
    (nativeOpenForgetIso k₀ l j) (derivedCondensedRealizationUpperStarIso k₀ l j).symm
    (condensedRealizationTensor k₀ l U) (condensedRealizationTensor k₀ l Z)
    (nativePullTensor k₀ l j) ρ' M N ((nativeOpenProjectionIso k₀ l j).app (M, N))
    (asIso (CondensedRing.openImmersionProjectionComparison Λ jb
      ((derivedCondensedRealization k₀ l U).obj M)
      ((derivedCondensedRealization k₀ l Z).obj N))).symm hu hr
    (nativeOpenProjectionIso_inverse_unit k₀ l j M N) hg'
  simpa only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
    whiskerRight_id, whiskerLeft_id, Category.id_comp, Category.comp_id,
    Iso.symm_hom, Iso.symm_inv, asIso_hom, asIso_inv] using h

end AlgebraicGeometry.ProEtaleWeilSheaf
