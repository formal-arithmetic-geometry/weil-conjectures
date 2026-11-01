/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantCtf

/-! The closed adjunction unit on a tensor supported on a closed subscheme. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The derived closed unit is invertible on a twist tensored with a supported coefficient.

Source: Stacks Tags 0G75 and 0G76; closed essential image and termwise adjunction.
(blueprint: lem-pur-closed-supported-cup-closed-unit-iso).

Proof: the supported constant sheaf is flat. Thus its derived tensor with the shifted
Tate line is the shift of the ordinary tensor sheaf. Restriction of that sheaf to the
open complement is zero, since restriction is monoidal and kills the supported factor.
The closed essential-image theorem makes its ordinary closed unit an isomorphism.
Exact inverse image and closed direct image descend this unit to the derived category;
the single and shift comparisons identify it with the displayed adjunction unit.
Uniqueness of right adjoints transports the conclusion to any adjunction with this
fixed left adjoint. -/
theorem closedSupportedCup_closedUnitIso (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (a : ℕ) (t : ℤ)
    {R : P.FunctorialCupDerived true Z ⥤ P.FunctorialCupDerived true X}
    (adj : (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).mapDerivedCategory ⊣ R) :
    IsIso (adj.unit.app
      (P.functorialCupTarget true X a t ⊗ P.functorialCupSourceObject true i)) := by
  let U := i.openComplement.ι
  let A := ModuleCat.{u + 1} P.Coefficient
  let F := ProEtale.upperStar A U
  let G := ProEtale.upperStar A i
  let K := P.functorialCupTarget true X a t ⊗ P.functorialCupSourceObject true i
  let S := P.functorialCupSource true i
  letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  letI := F.mapDerivedCategoryOplaxMonoidal
  have hcomp : IsCompl (Set.range i.base) (Set.range U.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact isCompl_compl.symm
  letI : IsNoetherian X :=
    isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of P.field.k))
  letI : TopologicalSpace.NoetherianSpace X := inferInstance
  letI : QuasiCompact U := AlgebraicGeometry.Etale.quasiCompact_of_noetherianSpace U
  have hsource : IsZero (F.mapDerivedCategory.obj
      (P.functorialCupSourceObject true i)) := by
    have hz : IsZero (F.obj S) := by
      change IsZero (F.obj ((ProEtale.lowerStar A i).obj (P.constant Z)))
      exact ProEtale.isZero_upperStar_lowerStar_of_disjoint A i U
        (disjoint_range_of_range_eq_compl U i
          i.range_eq_compl_range_openComplement_ι).symm (P.constant Z)
    have hz0 : IsZero ((DerivedCategory.singleFunctor _ 0).obj
        (F.obj S)) :=
      (DerivedCategory.singleFunctor _ 0).map_isZero hz
    exact hz0.of_iso ((F.mapDerivedCategorySingleFunctor 0).app
      S)
  have htensor : IsZero (F.mapDerivedCategory.obj
      (P.functorialCupTarget true X a t) ⊗ F.mapDerivedCategory.obj
        (P.functorialCupSourceObject true i)) := by
    change IsZero ((tensorLeft (F.mapDerivedCategory.obj
      (P.functorialCupTarget true X a t))).obj
        (F.mapDerivedCategory.obj (P.functorialCupSourceObject true i)))
    exact (tensorLeft _).map_isZero hsource
  have hK : IsZero (F.mapDerivedCategory.obj K) := by
    have hδ : IsIso (Functor.OplaxMonoidal.δ F.mapDerivedCategory
      (P.functorialCupTarget true X a t)
      (P.functorialCupSourceObject true i)) := by
      change IsIso ((F.mapDerivedCategoryTensorComparison.app
        (P.functorialCupTarget true X a t)).app
        (P.functorialCupSourceObject true i))
      infer_instance
    letI := hδ
    exact htensor.of_iso (asIso (Functor.OplaxMonoidal.δ F.mapDerivedCategory
      (P.functorialCupTarget true X a t)
      (P.functorialCupSourceObject true i)))
  have hess := ProEtale.rightDerivedFunctor_lowerStar_essImage_of_isZero
    (R := P.Coefficient) i U hcomp hK
  letI := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl (R := P.Coefficient)
    i U hcomp
  let can := (ProEtale.upperStarLowerStarAdjunction A i).mapDerivedCategoryRightDerivedAdjunction
  obtain ⟨M, ⟨e⟩⟩ := hess
  have hcan : IsIso (can.unit.app K) := by
    exact Adjunction.isIso_unit_app_of_iso can e.symm
  let eR := adj.rightAdjointUniq can
  have hu := Adjunction.unit_rightAdjointUniq_hom_app adj can K
  letI : IsIso (can.unit.app K) := hcan
  have : IsIso (adj.unit.app K ≫ eR.hom.app (G.mapDerivedCategory.obj K)) := by
    rw [hu]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (eR.hom.app (G.mapDerivedCategory.obj K))


end WeilConjectures.PurityFiniteSetting
