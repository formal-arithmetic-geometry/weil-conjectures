/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryModel.CoordinateBoundaryGeometricPullbackDefs
public import WeilConjectures.AlgebraicGeometry.SupportHomPair.Transport.CoordinateBoundaryPullbackAux
import WeilConjectures.AlgebraicGeometry.SupportHomPair.Transport.CoordinateBoundarySiteAgreementAux
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Equivalence

/-! # From open coordinate classes to normalized supported boundaries
Source: Milne, Theorem 9.4 and Example 9.5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Functor.mapDerivedCategoryPlus
  Functor.sheafPushforwardContinuous Etale.lowerStar ProEtale.lowerStar
  Scheme.Etale Scheme.ProEt Scheme.instCategoryEtale Scheme.instCategoryProEt
  MorphismProperty MorphismProperty.Comma.instCategory
  coordinateEtaleInput coordinateProInput coordinateLineMap
  Sheaf.supportedSectionsFunctor DerivedCategory.Plus.homologyFunctor

/-- The coefficient-adjusted map on the actual open-complement section groups.
Source: Milne Section 9 (blueprint: aux-lem-pur-coordinate-boundary-from-open). -/
def coordinateEtaleOpenPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (g : T ⟶ Y)
    (e : etaleSupportHomTransport P (zeroSection Y) (zeroSection T) (coordinateLineMap g)) :
    (Sheaf.sectionHypercohomologyFunctor (Line Y).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.mk (zeroSection Y).openComplement.ι) 1).obj
        (P.coordinateEtaleInput h (Line Y)) ⟶
    (Sheaf.sectionHypercohomologyFunctor (Line T).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.mk (zeroSection T).openComplement.ι) 1).obj
        (P.coordinateEtaleInput h (Line T)) := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ (coordinateLineMap g)).IsContinuous
      (etaleSupportHomPair P (zeroSection Y)).topology
      (etaleSupportHomPair P (zeroSection T)).topology :=
    Etale.isContinuous_overPullback (coordinateLineMap g)
  exact (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1).map
      (e.openDerivedMap.app (P.coordinateEtaleInput h (Line Y))) ≫
    (Sheaf.sectionHypercohomologyFunctor (Line T).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.mk (zeroSection T).openComplement.ι) 1).map
        (P.coordinateEtaleCoefficientPullback h (coordinateLineMap g))

/-- The ordinary open-class equation determines both supported boundary equations
and their normalized supported-Hom representatives.
Source: Milne Theorem 9.4 and Example 9.5.
Proof: apply naturality of the normalized snake boundary to the ordinary open class,
then use normalized supported-Hom compatibility. For the pro-etale equation, replace
the source class by its site image, use the coherent coefficient square, the ordinary
boundary equation, and the target site equation. Finally apply pro-etale normalized
supported-Hom compatibility.
(blueprint: aux-lem-pur-coordinate-boundary-from-open). -/
theorem coordinate_boundary_from_open (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (g : T ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (D : CoordinateBoundaryModel P Y) (D' : CoordinateBoundaryModel P T)
    (e : etaleSupportHomTransport P (zeroSection Y) (zeroSection T) (coordinateLineMap g))
    (p : proEtaleSupportHomTransport P (zeroSection Y) (zeroSection T) (coordinateLineMap g))
    (v : siteSupportHomTransport P (zeroSection Y))
    (v' : siteSupportHomTransport P (zeroSection T))
    (he : e.Compatible (hB := Etale.isContinuous_overPullback (coordinateLineMap g))
      D.chiEtale D'.chiEtale (P.coordinateEtaleInput h (Line Y)) 2)
    (hp : p.Compatible (hB := Scheme.ProEt.isContinuous_overPullback (coordinateLineMap g))
      D.chiPro D'.chiPro (P.coordinateProInput h (Line Y)) 2)
    (hv : P.CoordinateBoundarySiteAgreement h a D v)
    (hv' : P.CoordinateBoundarySiteAgreement h (g ≫ a) D' v')
    (hc : SupportHomSquareCoherent P (zeroSection Y) (zeroSection T)
      (coordinateLineMap g) e p v v')
    (hopen : P.coordinateEtaleOpenPullback h g e
        (P.coordinateEtaleOpenClass h Y a D.complementIso) =
      P.coordinateEtaleOpenClass h T (g ≫ a) D'.complementIso) :
    P.CoordinateBoundaryPullback h g a D D' e p := by
  let : (MorphismProperty.Over.pullback @Etale ⊤ (coordinateLineMap g)).IsContinuous
      (etaleSupportHomPair P (zeroSection Y)).topology
      (etaleSupportHomPair P (zeroSection T)).topology :=
    Etale.isContinuous_overPullback (coordinateLineMap g)
  let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤
      (coordinateLineMap g)).IsContinuous
      (proEtaleSupportHomPair P (zeroSection Y)).topology
      (proEtaleSupportHomPair P (zeroSection T)).topology :=
    Scheme.ProEt.isContinuous_overPullback (coordinateLineMap g)
  have hE : e.coefficientGroupMap (hB := Etale.isContinuous_overPullback
      (coordinateLineMap g)) (P.coordinateEtaleCoefficientPullback h (coordinateLineMap g)) 2
      (D.alphaEtale P h a) = D'.alphaEtale P h (g ≫ a) := by
    have hh := e.boundary_coefficient_apply
      D.boundaryEtale D'.boundaryEtale D.etale_normalized D'.etale_normalized
      (P.coordinateEtaleCoefficientPullback h (coordinateLineMap g)) 1
      (P.coordinateEtaleOpenClass h Y a D.complementIso)
      (P.coordinateEtaleOpenClass h T (g ≫ a) D'.complementIso) hopen
    convert hh using 1 <;> rfl
  refine ⟨e.coefficientCompatible_of_compatible _ _ _ _ he _ _ hE, ?_⟩
  apply p.coefficientCompatible_of_compatible _ _ _ _ hp
  have hsquare := coordinate_boundary_coefficient_square P h (zeroSection Y)
    (zeroSection T) (coordinateLineMap g) e p v v' hc 2
  have hgroup := ConcreteCategory.congr_hom hsquare (D.alphaEtale P h a)
  change (v.coefficientGroupMap (hB := Scheme.isContinuous_toProEt (Line Y))
      (𝟙 (P.coordinateProInput h (Line Y))) 2 ≫
    p.coefficientGroupMap (hB := Scheme.ProEt.isContinuous_overPullback
      (coordinateLineMap g)) (P.coordinateProCoefficientPullback h (coordinateLineMap g)) 2)
      (D.alphaEtale P h a) = _ at hgroup
  simpa only [ConcreteCategory.comp_apply, hv.1, hE, hv'.1] using hgroup

end WeilConjectures.PurityFiniteSetting
