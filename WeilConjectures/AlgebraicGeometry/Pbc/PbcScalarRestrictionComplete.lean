/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension

/-! # Exact coefficient restriction preserves intrinsic completeness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
    (W : Scheme.{u})

/-- The completed scalar inclusion in the published coefficient presentation.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pbc-scalar-restriction-complete). -/
private theorem pbcScalarModelCoefficientSquare :
    WeilConjectures.completedCoefficientMap l E F i W ≫
        (WeilConjectures.purCoefficientIso l F W).inv =
      (WeilConjectures.purCoefficientIso l E W).inv ≫ pbcScalarCoefficientMap l E F i W := by
  let eR := WeilConjectures.purCoefficientIso l E W
  let eS := WeilConjectures.purCoefficientIso l F W
  have hmap : WeilConjectures.integralCompletedScalarMap l E F i W =
      WeilConjectures.completedCoefficientMap l E F i W := by
    apply (WeilConjectures.completedCoefficientMap_existsUnique l E F i W).unique
    · exact (WeilConjectures.integralCompletedScalarMap_existsUnique l E F i W).exists.choose_spec
    · exact (WeilConjectures.completedCoefficientMap_existsUnique l E F i W).exists.choose_spec
  have hsq := scalarComplete_coefficientScalar_square l E F i W
  rw [hmap] at hsq
  change eR.hom ≫ _ = pbcScalarCoefficientMap l E F i W ≫ eS.hom at hsq
  apply (Iso.comp_inv_eq eS).mpr
  rw [Category.assoc]
  exact ((Iso.inv_comp_eq eR).mpr hsq.symm).symm

-- Restriction along a composite is the composite of restrictions (identity on sections).
private def scalarRestrictionCompose {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (f : R ⟶ S) (g : S ⟶ T) :
    SheafOfModules.restrictScalars.{u + 1} g ⋙ SheafOfModules.restrictScalars f ≅
      SheafOfModules.restrictScalars (f ≫ g) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (f.hom.app U).hom (g.hom.app U).hom
        ((f ≫ g).hom.app U).hom rfl (M.val.obj U)).symm)
      (by intro U V h; ext x; rfl)))
    (by intro M N h; ext U x; rfl)

-- Restriction along the two composites of the coefficient square agree.
private def pbcScalarModelRestrictionIso :
    pbcRestrict (pbcScalarCoefficientMap l E F i W) ⋙
        pbcRestrict (WeilConjectures.purCoefficientIso l E W).inv ≅
      pbcRestrict (WeilConjectures.purCoefficientIso l F W).inv ⋙
        pbcRestrict (WeilConjectures.completedCoefficientMap l E F i W) := by
  let FC := adicLisseForget W
  have h : FC.map (WeilConjectures.purCoefficientIso l E W).inv ≫
      FC.map (pbcScalarCoefficientMap l E F i W) =
      FC.map (WeilConjectures.completedCoefficientMap l E F i W) ≫
        FC.map (WeilConjectures.purCoefficientIso l F W).inv := by
    rw [← FC.map_comp, ← FC.map_comp, pbcScalarModelCoefficientSquare]
  exact scalarRestrictionCompose _ _ ≪≫
    eqToIso (congrArg SheafOfModules.restrictScalars.{u + 1} h) ≪≫
    (scalarRestrictionCompose _ _).symm

/-- Derived restriction in the published model commutes with the scalar restriction.
Source: Stacks Tag 03DA (blueprint: lem-pbc-scalar-restriction-complete). -/
private def pbcScalarModelDerivedRestrictionIso (K : PbcCompletedDerived W (pbcIntegralDatum l F)) :
    (pbcDerivedRestrict (WeilConjectures.purCoefficientIso l E W).inv).obj
        ((pbcDerivedRestrict (pbcScalarCoefficientMap l E F i W)).obj K) ≅
      (pbcDerivedRestrict (WeilConjectures.completedCoefficientMap l E F i W)).obj
        ((pbcDerivedRestrict (WeilConjectures.purCoefficientIso l F W).inv).obj K) :=
  (Functor.mapDerivedCategoryCompIso (pbcRestrict (pbcScalarCoefficientMap l E F i W))
      (pbcRestrict (WeilConjectures.purCoefficientIso l E W).inv)).symm.app K ≪≫
    (Functor.mapDerivedCategoryNatIso (pbcScalarModelRestrictionIso l E F i W)).app K ≪≫
    (Functor.mapDerivedCategoryCompIso
      (pbcRestrict (WeilConjectures.purCoefficientIso l F W).inv)
      (pbcRestrict (WeilConjectures.completedCoefficientMap l E F i W))).app K

/-- Restriction along the completed scalar inclusion preserves derived completeness in
the published coefficient model.
Source: Stacks Tags 0999, 099B and 0A0E (blueprint: lem-pbc-scalar-restriction-complete).
Proof: the source uniformizer maps to a unit times a positive power of the target
uniformizer, so their powers are cofinal and completeness for the target uniformizer is
completeness for the image of the source uniformizer. Restriction is exact, preserves
products, and detects acyclicity; it carries the local Koszul completion criterion for
that image to the source ring (`restrictScalars_locallyDerivedComplete_iff`).
Not yet formalized: that lemma is stated for a `SmallCategory` site with coefficients in
the same universe, whereas `W.ProEt` has `Category.{u}` on `Type (u + 1)`, and it is
phrased with `IsLocallyDerivedRingedIdealComplete`, not with the Roos predicate
`IsSfDerivedComplete` used here. A proof needs (a) a small-model transfer of that lemma to
`W.ProEt`, (b) the comparison of `IsSfDerivedComplete` with the local ideal criterion for
the principal ideals of the two uniformizers, and (c) the unit-power cofinality step. -/
private theorem pbcScalarModelRestrictionComplete
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l F W))
    (hM : WeilConjectures.IsSfDerivedComplete l F W M) :
    WeilConjectures.IsSfDerivedComplete l E W
      ((pbcDerivedRestrict (WeilConjectures.completedCoefficientMap l E F i W)).obj M) := by
  sorry

/-- Exact coefficient restriction preserves intrinsic completeness.
Source: Stacks Project, Tags 099B and 0A0E; the restriction and unit-power argument
of lem-weil-pbc-finite-free-completion-transport, step 2.
(blueprint: lem-pbc-scalar-restriction-complete).

Proof: identify the actual completed coefficient rings with their published
presentations by pbcCompletedComparison, retaining each finite quotient map.
The source uniformizer maps to a unit times a positive power of the target
uniformizer. Their powers are cofinal, so target-uniformizer completeness implies
completeness for the image of the source uniformizer, by the unit-power Cech/Koszul
criterion. Exact restriction carries this augmented Koszul computation to the
source ring: scalar restriction preserves the products and cones in the local
completion complex, and its scalar action on each differential is multiplication
by that image. It also detects the acyclicity of the corresponding Cech Hom
complexes. Consequently the restricted object is complete for the source
uniformizer. The comparison of intrinsic completeness with this local criterion
and transport back along pbcCompletedComparison give the stated predicate. This
argument uses no scalar/completion isomorphism and no constructibility assumption. -/
theorem pbcScalarRestrictionComplete (K : PbcCompletedDerived W (pbcIntegralDatum l F))
    (hK : PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F) K) :
    PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E)
      ((pbcDerivedRestrict (pbcScalarCoefficientMap l E F i W)).obj K) := by
  have hc := (WeilConjectures.purCoefficientModel_predicates l F W K).2.mp hK
  have hB := pbcScalarModelRestrictionComplete l E F i W _ hc
  apply (WeilConjectures.purCoefficientModel_predicates l E W _).2.mpr
  exact WeilConjectures.complete_of_iso l E W
    (pbcScalarModelDerivedRestrictionIso l E F i W K).symm hB

end AlgebraicGeometry.Scheme
