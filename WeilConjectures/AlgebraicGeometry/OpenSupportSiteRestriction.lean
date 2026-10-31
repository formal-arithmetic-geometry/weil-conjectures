/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

/-! # Open support kernels under restriction to the etale site

(blueprint: lem-pur-open-support-site-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

private def pointwiseKernel {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {F G : C ⥤ D} (η : F ⟶ G) : C ⥤ D where
  obj X := kernel (η.app X)
  map f := kernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm
  map_id X := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

private def pointwiseKernelIso {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {F G : C ⥤ D} (η : F ⟶ G) : kernel η ≅ pointwiseKernel η :=
  NatIso.ofComponents
    (fun X ↦ PreservesKernel.iso ((evaluation C D).obj X) η)
    (by
      intro X Y f
      apply (cancel_mono (kernel.ι (η.app Y))).1
      simp only [PreservesKernel.iso_hom, pointwiseKernel, Category.assoc, kernel.lift_ι]
      erw [kernelComparison_comp_ι]
      rw [← Category.assoc]
      erw [kernelComparison_comp_ι]
      exact (kernel.ι η).naturality f)

open AlgebraicGeometry
private def etaleSupportOpenIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Etale.sectionsWithSupport AddCommGrpCat.{u + 1} j ≅
      kernel (Etale.openImmersionRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit :=
  (pointwiseKernelIso
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit).symm ≪≫
      kernel.mapIso _ _ (Iso.refl _)
        (Functor.isoWhiskerRight (Etale.upperStarIsoOpenImmersionRestriction
          AddCommGrpCat.{u + 1} j) (Etale.lowerStar AddCommGrpCat.{u + 1} j)) (by
          simpa only [Iso.refl_hom, Category.id_comp, Functor.isoWhiskerRight_hom,
            Etale.upperStarIsoOpenImmersionRestriction,
            Etale.upperStarIsoLocalizationRestriction,
            Etale.openImmersionRestrictionLowerStarAdjunction] using
            Adjunction.unit_leftAdjointUniq_hom
            (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j)
            (Etale.openImmersionRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j))

private def proetaleSupportOpenIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ProEtale.sectionsWithSupport AddCommGrpCat.{u + 1} j ≅
      kernel (ProEtale.openImmersionRestrictionLowerStarAdjunction
        AddCommGrpCat.{u + 1} j).unit :=
  (pointwiseKernelIso
    (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit).symm ≪≫
      kernel.mapIso _ _ (Iso.refl _)
        (Functor.isoWhiskerRight (ProEtale.upperStarIsoOpenImmersionRestriction
          AddCommGrpCat.{u + 1} j) (ProEtale.lowerStar AddCommGrpCat.{u + 1} j)) (by
          simpa only [Iso.refl_hom, Category.id_comp, Functor.isoWhiskerRight_hom,
            ProEtale.upperStarIsoOpenImmersionRestriction,
            ProEtale.upperStarIsoLocalizationRestriction,
            ProEtale.openImmersionRestrictionLowerStarAdjunction] using
            Adjunction.unit_leftAdjointUniq_hom
            (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j)
            (ProEtale.openImmersionRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j))

/-- Restriction from the pro-etale site commutes with the open support kernel.
Source: the open-restriction adjunctions and their pointwise units; Stacks 09XP.
(blueprint: lem-pur-open-support-site-restriction).

Proof: replace each inverse image along the open immersion by the explicit site
restriction, using uniqueness of left adjoints. The unit identity for that uniqueness
isomorphism identifies their kernels. Under comparison direct image the explicit
restriction units are definitionally equal. Direct image preserves kernels; compute
these kernels pointwise in the functor category and compose the resulting natural
isomorphisms. -/
theorem AlgebraicGeometry.ProEtale.nonempty_sectionsWithSupport_comparisonLowerStarIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (ProEtale.sectionsWithSupport AddCommGrpCat.{u + 1} j ⋙
        ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X ≅
      ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X ⋙
        Etale.sectionsWithSupport AddCommGrpCat.{u + 1} j) := by
  let R := ProEtale.comparisonLowerStar AddCommGrpCat.{u + 1} X
  let P := (ProEtale.openImmersionRestrictionLowerStarAdjunction
    AddCommGrpCat.{u + 1} j).unit
  let E := (Etale.openImmersionRestrictionLowerStarAdjunction
    AddCommGrpCat.{u + 1} j).unit
  let C := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
  let D := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let W := (Functor.whiskeringRight C C D).obj R
  let V := (Functor.whiskeringLeft C D D).obj R
  have h : Functor.whiskerRight P R = Functor.whiskerLeft R E := rfl
  exact ⟨Functor.isoWhiskerRight (proetaleSupportOpenIso j) R ≪≫
    PreservesKernel.iso W P ≪≫ kernelIsoOfEq h ≪≫ (PreservesKernel.iso V E).symm ≪≫
    Functor.isoWhiskerLeft R (etaleSupportOpenIso j).symm⟩
