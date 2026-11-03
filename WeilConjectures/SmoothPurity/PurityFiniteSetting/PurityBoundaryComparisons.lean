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
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityAffineLineGeometry
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportAmplitude
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # The prescribed closed-support comparison maps -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary exceptional twist remains bounded below.
Source: closed-support amplitude and affine-line open-complement bound.
Proof: apply the closed amplitude estimate to the twist in degree zero; shifting
by two lowers its lower bound by two.
(blueprint: lem-pur-boundary-comparisons). -/
theorem boundaryEtaleValue_boundedBelow (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h Y) := by
  obtain ⟨d, hj, _, hopen⟩ := affine_line_boundary_geometry P h Y a
  let := hj
  have hij : Set.range (zeroSection Y).base =
      (Set.range (openImmersion Y).base)ᶜ := by
    rw [show Set.range (openImmersion Y).base =
      (Set.range (zeroSection Y).base)ᶜ from AffineSpace.range_basicOpen_ι_coord Y]
    simp only [compl_compl]
  have hcd (M : EtSheaves P (Punctured Y)) (q : ℤ) (hq : (2 * d : ℕ) < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (Modules P) (openImmersion Y)).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) :=
    (hopen.1 M q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((Etale.lowerStar (Modules P) (openImmersion Y)).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)).symm)
  have hK : DerivedCategory.homologyConcentratedIn 0 0 (P.gysinEtaleInput h Y).obj := by
    change DerivedCategory.homologyConcentratedIn 0 0
      ((DerivedCategory.singleFunctor _ 0).obj (P.twistEtale h (Line Y)))
    exact ⟨inferInstance, inferInstance⟩
  have hb := (Etale.closedImmersion_rightAdjoint_amplitude P.Coefficient
    (zeroSection Y) (openImmersion Y) hij 0 0 ((2 * d : ℕ) : ℤ) (by positivity) hcd).1
      (P.gysinEtaleInput h Y).obj hK
  let := hb.1
  exact ⟨-2, DerivedCategory.TStructure.t.isGE_shift
    ((etClosed P (zeroSection Y)).obj (P.gysinEtaleInput h Y).obj) 0 2 (-2) (by omega)⟩

/-- The actual comparison is invertible, since the bounded-below comparison unit is.
Source: comparison full faithfulness and uniqueness of ordinary right adjoints.
(blueprint: lem-pur-boundary-comparisons). -/
theorem boundaryExceptionalComparison_isIso (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    IsIso (P.boundaryExceptionalComparison h Y) := by
  have := firstComparisonTransformation_isIso P (lineProjection Y) (zeroSection Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)
  dsimp only [boundaryExceptionalComparison, firstComparison]
  infer_instance

/-- The direct-image comparison is the canonical qcqs comparison mate.
Source: canonical direct-image mate and exact closed pushforward.
(blueprint: lem-pur-boundary-comparisons). -/
theorem boundaryImageComparison_isIso (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (B : DerivedCategory.Plus (EtSheaves P Y)) :
    IsIso (P.boundaryImageComparison Y B) := by
  have := isIso_comparisonDirectImageCanonicalMate P.Coefficient (zeroSection Y)
  dsimp only [boundaryImageComparison, imageComparison]
  infer_instance

/-- Transport of the ordinary counit through the specified comparison isomorphisms.
Every factor is constructed, with no pro-etale exceptional adjunction assumed.
Source: affine-line boundary realization, site-transport step.
(blueprint: lem-pur-boundary-comparisons). -/
def boundaryTransportCounit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h Y)) :
    (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.obj
        (P.gysinValue h Y) ⟶ (P.gysinInput h Y).obj⟦(2 : ℤ)⟧ :=
  let := boundaryExceptionalComparison_isIso P h Y
  let := boundaryImageComparison_isIso P Y ⟨P.boundaryEtaleValue h Y, hb⟩
  (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.map
      (inv (P.boundaryExceptionalComparison h Y)) ≫
    inv (P.boundaryImageComparison Y ⟨P.boundaryEtaleValue h Y, hb⟩) ≫
    (nu P (Line Y)).map (P.boundaryEtaleCounit h Y) ≫
    ((nu P (Line Y)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h Y).obj

/-- The transported counit satisfies its defining equality.
Source: inverse cancellation in the two canonical comparison isomorphisms.
(blueprint: lem-pur-boundary-comparisons). -/
theorem boundaryTransportCounit_eq (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h Y)) :
    P.boundaryImageComparison Y ⟨P.boundaryEtaleValue h Y, hb⟩ ≫
      (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.map
        (P.boundaryExceptionalComparison h Y) ≫ P.boundaryTransportCounit h Y hb =
    (nu P (Line Y)).map (P.boundaryEtaleCounit h Y) ≫
      ((nu P (Line Y)).commShiftIso (2 : ℤ)).hom.app (P.gysinEtaleInput h Y).obj := by
  let := boundaryExceptionalComparison_isIso P h Y
  let := boundaryImageComparison_isIso P Y ⟨P.boundaryEtaleValue h Y, hb⟩
  simp [boundaryTransportCounit]

/-- Every pro-etale realizing morphism has exactly one ordinary etale antecedent.
Source: full faithfulness of bounded-below site comparison.
Proof: cancel the invertible exceptional comparison and the single-functor comparison,
then use the comparison Hom bijection. Cancellation also proves uniqueness.
(blueprint: lem-pur-boundary-comparisons). -/
theorem boundaryEtaleAntecedent_unique (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h Y))
    (m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y) :
    ∃! f : (DerivedCategory.singleFunctor (EtSheaves P Y) 0).obj
        (P.constantEtale Y) ⟶ P.boundaryEtaleValue h Y,
      ((comparisonUpperStar (Modules P) Y).mapDerivedCategorySingleFunctor 0).inv.app
        (P.constantEtale Y) ≫ (nu P Y).map f ≫
          P.boundaryExceptionalComparison h Y = m := by
  let := boundaryExceptionalComparison_isIso P h Y
  let s := ((comparisonUpperStar (Modules P) Y).mapDerivedCategorySingleFunctor 0).app
    (P.constantEtale Y)
  have hf := bijective_comparisonUpperStar_mapDerivedCategory_map
    ((DerivedCategory.singleFunctor _ 0).obj (P.constantEtale Y))
    (P.boundaryEtaleValue h Y) hb
  obtain ⟨f, hf⟩ := hf.2 (s.hom ≫ m ≫ inv (P.boundaryExceptionalComparison h Y))
  change (nu P Y).map f = s.hom ≫ m ≫ inv (P.boundaryExceptionalComparison h Y) at hf
  have hfm : s.inv ≫ (nu P Y).map f ≫ P.boundaryExceptionalComparison h Y = m := by
    calc
      _ = s.inv ≫ (s.hom ≫ m ≫ inv (P.boundaryExceptionalComparison h Y)) ≫
          P.boundaryExceptionalComparison h Y := by rw [hf]
      _ = m := by simp
  refine ⟨f, hfm, fun g hg ↦ ?_⟩
  apply (bijective_comparisonUpperStar_mapDerivedCategory_map
    ((DerivedCategory.singleFunctor _ 0).obj (P.constantEtale Y))
    (P.boundaryEtaleValue h Y) hb).1
  apply (cancel_epi s.inv).1
  apply (cancel_mono (P.boundaryExceptionalComparison h Y)).1
  change (s.inv ≫ (nu P Y).map g) ≫ P.boundaryExceptionalComparison h Y =
    (s.inv ≫ (nu P Y).map f) ≫ P.boundaryExceptionalComparison h Y
  simpa only [s, Iso.app_inv, Category.assoc] using hg.trans hfm.symm

end WeilConjectures.PurityFiniteSetting
