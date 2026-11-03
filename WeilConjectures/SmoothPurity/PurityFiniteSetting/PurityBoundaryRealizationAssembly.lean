/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Open.OpenComplementCondition
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityBoundaryComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityAffineLineGeometry
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityBoundarySupportChart
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityBoundarySupportedTranspose

/-! # Assembly of affine-line boundary realization -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

private theorem inverse_chart_apply {R : Type*} [CommRing R]
    {M N K L : ModuleCat R} (sh : M ≅ N) (edge : K ≅ N) (s : K ≅ L)
    (g : L → M) (hf : ∀ x : K, edge.hom x = sh.hom (g (s.hom x))) (v : M) :
    g ((sh ≪≫ edge.symm ≪≫ s).hom v) = v := by
  have hx := hf (edge.inv (sh.hom v))
  have hx' : sh.hom v = sh.hom (g (s.hom (edge.inv (sh.hom v)))) := by
    simpa only [Iso.inv_hom_id_apply] using hx
  simpa only [Iso.trans_hom, Iso.symm_hom, ConcreteCategory.comp_apply] using
    sh.toLinearEquiv.injective hx'.symm

/-- The realization follows from the two normalization identities, the comparison
isomorphisms and the Gysin evaluation bijection. Every existence and uniqueness
assertion is constructed here from those maps.
Source: affine-line boundary realization, steps 4--7.
(blueprint: lem-pur-affine-line-boundary-data). -/
theorem affine_line_boundary_realization_data (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    P.AffineLineBoundaryRealization h Y a := by
  let χ : P.BoundarySupportedHom Y := supportedCohomologyHom P (zeroSection Y) 2
  have hg := P.gysin_structure_statement h Y a
  have hb := boundaryEtaleValue_boundedBelow P h Y a
  let := boundaryExceptionalComparison_isIso P h Y
  let := boundaryImageComparison_isIso P Y ⟨P.boundaryEtaleValue h Y, hb⟩
  refine ⟨χ, hb,
    asIso (P.boundaryExceptionalComparison h Y),
    asIso (P.boundaryImageComparison Y ⟨P.boundaryEtaleValue h Y, hb⟩),
    P.boundaryTransportCounit h Y hb, rfl, rfl, boundaryTransportCounit_eq P h Y hb,
    affine_line_boundary_comparison P h Y a, ?_⟩
  intro c
  obtain ⟨b, hbmap, _⟩ := hg.2.2.2.2.2.2
  let sh : (localClasses P Y 0).obj (P.gysinValue h Y) ≅
      (localClasses P Y 2).obj (P.gysinClosed h Y) :=
    (globalSectionsFunctor (Modules P) Y).mapIso
    (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
      (2 : ℤ) 0 2 (add_zero 2)).app (P.gysinClosed h Y))
  have hfun : (fun v ↦ (c.edge 2).app (P.gysinClosed h Y) v) =
      (fun v ↦ sh.hom (P.gysinSupportToSections h Y a
        ((c.supportIso 2).hom.app (P.gysinEtaleInput h Y) v))) :=
    funext (boundary_support_chart P h Y a c)
  have hbijEdge : Function.Bijective ((c.edge 2).app (P.gysinClosed h Y)) := by
    change Function.Bijective (fun v ↦ (c.edge 2).app (P.gysinClosed h Y) v)
    rw [hfun]
    exact sh.toLinearEquiv.bijective.comp
      (hg.2.2.2.2.2.1.comp ((c.supportIso 2).app
        (P.gysinEtaleInput h Y)).toLinearEquiv.bijective)
  let : IsIso ((c.edge 2).app (P.gysinClosed h Y)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbijEdge
  let edge := asIso ((c.edge 2).app (P.gysinClosed h Y))
  let e := sh ≪≫ edge.symm ≪≫ (c.supportIso 2).app (P.gysinEtaleInput h Y)
  have hchart (v : (localClasses P Y 0).obj (P.gysinValue h Y)) :
      P.gysinSupportToSections h Y a (e.hom v) = v := by
    exact inverse_chart_apply sh edge ((c.supportIso 2).app (P.gysinEtaleInput h Y))
      (P.gysinSupportToSections h Y a) (boundary_support_chart P h Y a c) v
  have hbij : Function.Bijective (fun m ↦ e.hom (P.gysinHomToSections h Y m)) :=
    e.toLinearEquiv.bijective.comp hg.2.2.2.1
  have hex (α : P.gysinSupport h Y) :
      ∃! m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
        e.hom (P.gysinHomToSections h Y m) = α := by
    obtain ⟨m, hm⟩ := hbij.2 α
    exact ⟨m, hm, fun m' hm' ↦ hbij.1 (hm'.trans hm.symm)⟩
  refine ⟨b, edge, e, hbmap, rfl, rfl, hex, ?_, ?_, ?_⟩
  · intro m
    have hm : P.gysinSupportToHom h Y a (e.hom (P.gysinHomToSections h Y m)) = m := by
      apply hg.2.2.2.1.1
      exact hchart (P.gysinHomToSections h Y m)
    have hn := boundary_supported_transpose P h Y a hb
      (e.hom (P.gysinHomToSections h Y m))
    change (χ.hom.app (P.gysinInput h Y)) (e.hom (P.gysinHomToSections h Y m)) =
      ((lowerStar (Modules P) (zeroSection Y)).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constant Y) ≫
        (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.map
          (P.gysinSupportToHom h Y a (e.hom (P.gysinHomToSections h Y m))) ≫
            P.boundaryTransportCounit h Y hb at hn
    rw [hm] at hn
    exact hn
  · intro m
    exact boundaryEtaleAntecedent_unique P h Y hb m
  · intro δ _hδ
    exact hex ((δ 1).app ⟨P.gysinInput h Y, trivial⟩ (P.gysinKummerSection h Y a c b))

end WeilConjectures.PurityFiniteSetting
