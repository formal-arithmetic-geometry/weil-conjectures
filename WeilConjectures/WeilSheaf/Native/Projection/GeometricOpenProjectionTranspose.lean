/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.GeometricProjectionNaturality
public import WeilConjectures.WeilSheaf.Native.Projection.UncurriedComparison
public import WeilConjectures.PoincareDuality.ProjectionFormula

/-! # The geometric open projection transpose -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The geometric open adjunction has an invertible unit. -/
instance projection_isIso_geometricOpen_unit :
    IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).unit :=
  inferInstanceAs
    (IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j).unit)

/-- The tensor isomorphism used by pullback has inverse its monoidal multiplication. -/
lemma projection_leftDerivedUpperStarTensorIso_inv_app
    (M N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    Functor.LaxMonoidal.μ (upperStar Λ j).leftDerivedFunctor M N =
      ((leftDerivedUpperStarTensorIso Λ j).inv.app M).app N := by
  rw [← cancel_epi (((leftDerivedUpperStarTensor Λ j).app M).app N)]
  exact (Functor.Monoidal.δ_μ (upperStar Λ j).leftDerivedFunctor M N).trans
    (NatTrans.congr_app ((leftDerivedUpperStarTensorIso Λ j).hom_inv_id_app M) N).symm

/-- The geometric projection comparison is the expected unit transpose. -/
lemma projection_open_homEquiv
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).homEquiv _ _
      (openImmersionProjectionComparison Λ j M N) =
      (Functor.uncurry.obj (curriedTensor _)).map
        (Prod.mkHom
          ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).unit.app M)
          (𝟙 _)) ≫
        (Functor.uncurryCompIsoOfIso (leftDerivedUpperStarTensorIso Λ j)).inv.app
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj M, N) := by
  rw [openImmersionProjectionComparison, Adjunction.homEquiv_projectionComparison_uncurried,
    projection_leftDerivedUpperStarTensorIso_inv_app]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
