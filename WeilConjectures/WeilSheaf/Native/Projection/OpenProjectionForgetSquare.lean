/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionForget
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionPasting
public import WeilConjectures.WeilSheaf.Native.Projection.GeometricProjectionNaturality

/-! # The canonical open projection formula under condensed realization, as a forget square

The statement is the instantiation of `compactProjectionOpen_forget_of_unit_at` in the
spelling of `ProjectionForgetSquare` (uncurried tensor functors, `Prod.mkHom` maps), so that no
conversion between whiskering and uncurried spellings is needed on the concrete terms. -/

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

/-- The canonical open projection isomorphism lies over the inverse geometric projection
comparison: the forget square in uncurried form. -/
theorem nativeOpenProjection_forgetSquare :
    ProjectionForgetSquare (nativeOpenForgetIso k₀ l j)
      (derivedCondensedRealizationUpperStarIso k₀ l j).symm
      (condensedRealizationTensor k₀ l U) (condensedRealizationTensor k₀ l Z)
      (nativeOpenProjectionIso k₀ l j).hom
      ((CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ jb).
        uncurriedInvProjectionComparisonNatTrans (fun _ _ ↦ inferInstance)) := by
  intro M N
  let adj := derivedExtensionByZeroUpperStarAdjunction k₀ l j
  let adj' := CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ jb
  let ρ' := Functor.uncurryCompIsoOfIso (CondensedRing.leftDerivedUpperStarTensorIso Λ jb)
  have : IsIso ((mateEquiv adj adj').symm
      (TwoSquare.mk _ _ _ _ (derivedCondensedRealizationUpperStarIso k₀ l j).symm.hom)).natTrans :=
    isIso_nativeOpenForgetInverseMate k₀ l j
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
                (derivedCondensedRealization k₀ l Z).obj N) :=
    CondensedRing.projection_open_homEquiv Λ jb _ _
  have h := compactProjectionOpen_forget_of_unit_at adj adj'
    (derivedCondensedRealization k₀ l U) (derivedCondensedRealization k₀ l Z)
    (nativeOpenForgetIso k₀ l j) (derivedCondensedRealizationUpperStarIso k₀ l j).symm
    (condensedRealizationTensor k₀ l U) (condensedRealizationTensor k₀ l Z)
    (nativePullTensor k₀ l j) ρ' M N ((nativeOpenProjectionIso k₀ l j).app (M, N))
    (asIso (CondensedRing.openImmersionProjectionComparison Λ jb
      ((derivedCondensedRealization k₀ l U).obj M)
      ((derivedCondensedRealization k₀ l Z).obj N))).symm hu hr
    (nativeOpenProjectionIso_inverse_unit k₀ l j M N) hg'
  -- both sides are the generic statement up to `Iso.app_hom`, `Iso.symm_hom`, `asIso_inv` and
  -- the definition of the uncurried inverse comparison, all definitional
  exact h

end AlgebraicGeometry.ProEtaleWeilSheaf
