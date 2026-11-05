/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionIso
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationCoherence
public import WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionForgetFormal
public import WeilConjectures.WeilSheaf.Native.Projection.UncurriedComparison
public import WeilConjectures.WeilSheaf.Native.Projection.GeometricOpenProjectionTranspose

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
  rw [NatTrans.isIso_iff_isIso_app]
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

-- The forget square of the open projection isomorphism is `nativeOpenProjection_forgetSquare`
-- (`WeilConjectures.WeilSheaf.Native.Projection.OpenProjectionForgetSquare`).

end AlgebraicGeometry.ProEtaleWeilSheaf
