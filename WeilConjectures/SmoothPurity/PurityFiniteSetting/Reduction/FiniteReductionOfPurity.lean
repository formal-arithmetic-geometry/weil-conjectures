/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionAffineOrientation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescent
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionReassociation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorPurity
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalOrientationReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCoherence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionBaseChangeSource
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityNaturality

/-! # Reduction of the canonical finite-coefficient purity maps

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
thm-pur-finite-reduction-of-purity (blueprint: thm-pur-finite-reduction-of-purity).

## Main statements

- `finiteReductionOfPurity`: reduction of the canonical purity morphism.
- `finiteReductionOfSmoothTrace`: reduction of coefficient-valued smooth traces.
- `finiteReductionOfCompositionCoherence`: reduction of the full purity composite.
- `finiteReductionOfBaseChange`: reduction of the specified smooth exchange square.
- `finiteReductionOfAffineOrientation`: reduction of the supported-Kummer orientation.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Finite reduction takes the specified purity morphism to the specified purity
morphism over the smaller quotient, through the canonical six-operation comparisons.
There is no ramification-index divisibility or quotient-flatness hypothesis.
Source: blueprint thm-pur-finite-reduction-of-purity, displayed square
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: use bounded flat representatives to obtain the tensor, pullback, support,
shift and rank-one twist comparisons. The supported Cartier class reduces because
the finite Kummer sequences commute and the supported boundary is natural; its
adjoint gives the affine orientation at the smaller level. The deformation
localization triangles and their specialization maps commute with reduction, as
do zero-section duality and vector-bundle trace, so normalized diagonal orientation
reduces. The tensor transformation is the counit mate of the projection-formula
inverse; finite adjoint-mate compatibility makes it commute with reduction.
Substitute these identities into tau, tensor with the inverse diagonal orientation,
and theta defining gamma. This gives precisely the displayed equality. -/
theorem finiteReductionOfPurity (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (P.finiteReduction m hm hmn X).map (P.smoothPurityMap f d K hK) ≫
        P.finiteReductionExceptionalComparison m hm hmn f d K hK =
      (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).smoothPurityMap f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK) := by
  unfold smoothPurityMap
  rw [Functor.map_comp, Category.assoc,
    P.finiteReduction_tensorPurity m hm hmn f d K hK, ← Category.assoc,
    P.finiteReduction_reassociation m hm hmn f d K hK, Category.assoc]

set_option linter.unusedSectionVars false in
private theorem finiteReductionSupport_naturality
    {K L : Scheme.proEtaleDerivedCategory X P.Ring} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn Y).map ((P.smoothCompactSupport f).map a) ≫
        P.finiteReductionCompactSupportComparison m hm hmn f L =
      P.finiteReductionCompactSupportComparison m hm hmn f K ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReduction m hm hmn X).map a) := by
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  unfold finiteReductionCompactSupportComparison
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hu := (P.finiteReductionAdjunction m hm hmn X).unit.naturality a
  have hc := (Scheme.sfCompactSupportRestriction
    (HasCompactification.compactification f)
      (P.finiteReductionRingHom m hm hmn)).hom.naturality
        ((P.finiteReduction m hm hmn X).map a)
  simp only [Functor.comp_map, Functor.id_map] at hu hc
  change (P.smoothCompactSupport f).map
      ((X.proEtaleCoefficientRestrictScalars
        (P.finiteReductionRingHom m hm hmn)).mapDerivedCategory.map
          ((P.finiteReduction m hm hmn X).map a)) ≫ _ =
    _ ≫ (Y.proEtaleCoefficientRestrictScalars
      (P.finiteReductionRingHom m hm hmn)).mapDerivedCategory.map
        (((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReduction m hm hmn X).map a)) at hc
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc, hc]
  simp only [Category.assoc]

/-- Reduction preserves every coefficient-valued smooth trace, with the actual
compact-support and source comparisons on its domain.
Source: blueprint Step 6, trace paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: the trace is compact support of gamma followed by the exceptional counit.
Use naturality of the compact-support coefficient map to move reduced gamma
through it, apply finiteReductionOfPurity, and then apply the defining counit
identity of the exceptional coefficient comparison. The resulting composite is
the smaller-coefficient trace with exactly the source comparison displayed here. -/
theorem finiteReductionOfSmoothTrace (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (P.finiteReduction m hm hmn Y).map (P.coefficientValuedSmoothTrace f d K hK) =
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionShiftedPullback f d).obj K) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).coefficientValuedSmoothTrace f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK) := by
  have hb := (P.existsUnique_finiteReductionExceptionalComparison
    m hm hmn f d K hK).choose_spec.1
  change P.finiteReductionCompactSupportComparison m hm hmn f
      ((P.compositionExceptional f).obj K) ≫
    ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
      (P.finiteReductionExceptionalComparison m hm hmn f d K hK) ≫ _ = _ at hb
  have hn := finiteReductionSupport_naturality P m hm hmn f
    (K := (P.compositionShiftedPullback f d).obj K)
    (L := (P.compositionExceptional f).obj K) (P.smoothPurityMap f d K hK)
  change (P.finiteReduction m hm hmn Y).map
      ((P.smoothCompactSupport f).map (P.smoothPurityMap f d K hK) ≫
        P.smoothExceptionalCounit f K) = _
  rw [Functor.map_comp, ← hb, ← Category.assoc,
    hn]
  have hg := congrArg (((P.finiteReductionSetting m hm).smoothCompactSupport f).map)
    (P.finiteReductionOfPurity m hm hmn f d K hK)
  simp only [Functor.map_comp] at hg
  simpa only [Category.assoc, coefficientValuedSmoothTrace] using
    congrArg (fun z ↦
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionShiftedPullback f d).obj K) ≫ z ≫
        (P.finiteReductionSetting m hm).smoothExceptionalCounit f
          ((P.finiteReduction m hm hmn Y).obj K)) hg


/-- Transport the intrinsic finite-Tor predicate along an actual isomorphism.
Source: the definitions of constructibility and Tor amplitude. -/
private theorem finiteTor_of_iso
    {T : Scheme.{u}} {K L : Scheme.proEtaleDerivedCategory T P.Ring}
    (e : K ≅ L)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T L := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (Scheme.intrinsicFiniteTorsionConstructible
        P.coefficients.l P.extension P.level P.level_pos T) :=
    (Scheme.proEtale_bounded_constructible_isTriangulated T P.Ring).1
  refine ⟨ObjectProperty.prop_of_iso _ e hK.1, ?_⟩
  obtain ⟨a, b, ht⟩ := hK.2
  refine ⟨a, b, ht.1, ?_⟩
  intro M N hM g hg hN V i hi
  exact ht.2 M N (hM.map (fun j ↦ j ≪≫ e.symm)) g hg hN V i hi

attribute [-instance] WeilConjectures.finiteHomEtaleCategory in
set_option linter.unusedSectionVars false in
/-- The coefficient unit is the comparison image of the ordinary finite-Tor unit.
Source: finite coefficient Hom site descent, preservation of the finite-Tor domain. -/
private theorem coefficientUnit_ctf :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      (P.coefficientUnit Y) := by
  let F (r : {r : ℕ // 1 ≤ r}) : Prop :=
    let _ := Padic.finite_coefficientExtensionRing P.coefficients.l P.extension r r.property
    finiteTorConstructible P.coefficients.l P.extension r r.property Y
      ((ProEtale.finiteCoefficientIntrinsicComparison Y
        (Padic.coefficientExtensionRing P.coefficients.l P.extension r)).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit
            (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension r)) Y))
  have hAll (r : ℕ) (hr : 1 ≤ r) : F ⟨r, hr⟩ := by
    cases r with
    | zero => omega
    | succ n =>
        let A :=
          ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        let : Finite (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) :=
          Padic.finite_coefficientExtensionRing _ _ _ (Nat.succ_pos n)
        let U := Etale.ordinaryFiniteUnit A Y
        have hU : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y U := by
          exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y).prop_of_iso
            (((_root_.DerivedCategory.singleFunctor _ 0).mapIso
              (Functor.Monoidal.εIso
                (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))).symm) ≪≫
              _root_.DerivedCategory.singleFunctorObjUnitIso _).symm
            (Etale.constructibleFiniteTor_unit A)
        have hEt : finiteTorConstructibleEtale
            P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y U := by
          obtain ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩, c, d, ht⟩ := hU
          refine ⟨⟨fun i ↦
            (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
            min a b, b, min_le_right _ _, ?_⟩, min c d, d, min_le_right _ _, ?_⟩
          · intro i hi
            rcases hi with hi | hi
            · exact (_root_.DerivedCategory.isGE_iff U a).1 ha i
                (hi.trans_le (min_le_left _ _))
            · exact (_root_.DerivedCategory.isLE_iff U b).1 hb i hi
          · exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
              (ht.mono (min_le_left _ _) le_rfl)
        exact ((coefFiniteHomSiteDescent P.field P.coefficients.l
          P.coefficients.different P.extension Y).1 n).2.2.2.2 U hEt |>.1
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let E := ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring
  let : E.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  let : PreservesFiniteLimits E :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteLimits Y P.Ring
  let : PreservesFiniteColimits E :=
    ProEtale.finiteCoefficientIntrinsicRealization_preservesFiniteColimits Y P.Ring
  have hD' : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((ν ⋙ E).mapDerivedCategory.obj (Etale.ordinaryFiniteUnit P.Coefficient Y)) :=
    hAll P.level P.level_pos
  exact finiteTor_of_iso P (Functor.mapDerivedCategoryCompIso ν E |>.app
    (Etale.ordinaryFiniteUnit P.Coefficient Y)) hD'

set_option linter.unusedSectionVars false in
/-- The explicit unit trace is its coefficient-valued specialization.
Source: the universal presentation equation of the tensor purity map. -/
private theorem smoothTrace_eq_coefficientTrace (d : ℕ) [SmoothOfRelativeDimension d f]
    (hU : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      (P.coefficientUnit Y)) :
    P.smoothTrace f d = P.coefficientValuedSmoothTrace f d (P.coefficientUnit Y) hU := by
  unfold smoothTrace coefficientValuedSmoothTrace smoothPurityMap smoothPurityTensorMap
  rw [(P.existsUnique_smoothPurityTensorMap f d (P.coefficientUnit Y) hU).exists.choose_spec
    (Etale.ordinaryFiniteUnit P.Coefficient Y)
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y)))]

set_option linter.unusedSectionVars false in
/-- Naturality survives both the support and intrinsic realization comparisons.
Source: rightDerivedUpperShriekCounit_naturality and the realization triangle. -/
private theorem smoothCounit_naturality
    {K L : Scheme.proEtaleDerivedCategory Y P.Ring}
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (hL : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y L)
    (a : K ⟶ L) :
    (P.smoothCompactSupport f).map ((P.compositionExceptional f).map a) ≫
        P.smoothExceptionalCounit f L = P.smoothExceptionalCounit f K ≫ a := by
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  let E := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let H := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  have hK' := (P.compositionInput_bounded K hK).plusEtaleOrigin.plus
  have hL' := (P.compositionInput_bounded L hL).plusEtaleOrigin.plus
  have hn := ProEtale.rightDerivedUpperShriekCounit_naturality f hK' hL'
    (H.inverse.map a)
  have hs := (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
    (HasCompactification.compactification f)).hom.naturality
      ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (H.inverse.map a))
  change (P.smoothCompactSupport f).map
      (E.functor.map ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (H.inverse.map a))) ≫ _ = _ at hs
  have hc := H.counitIso.hom.naturality a
  simp only [Functor.comp_map, Functor.id_map] at hc
  simp only [smoothExceptionalCounit, dif_pos hK', dif_pos hL']
  change (P.smoothCompactSupport f).map
      (E.functor.map ((P.smoothPurityExceptionalOver f (Y ↘ Spec (.of P.field.k))).map
        (H.inverse.map a))) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, hs, Category.assoc, Category.assoc]
  simp only [Functor.comp_map]
  erw [← H.functor.map_comp_assoc, hn]
  rw [H.functor.map_comp, Category.assoc, Category.assoc, hc]
  simp only [Category.assoc]
  rfl

set_option linter.unusedSectionVars false in
/-- The coefficient-valued smooth trace is natural in the coefficient input.
Source: purity naturality and naturality of the exceptional counit. -/
private theorem smoothTrace_naturality (d : ℕ) [SmoothOfRelativeDimension d f]
    {K L : Scheme.proEtaleDerivedCategory Y P.Ring}
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (hL : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y L)
    (a : K ⟶ L) :
    P.coefficientValuedSmoothTrace f d K hK ≫ a =
      (P.smoothCompactSupport f).map ((P.compositionShiftedPullback f d).map a) ≫
        P.coefficientValuedSmoothTrace f d L hL := by
  have hn := (P.smoothPurityMap_naturality_choice_independence f d K L hK hL a).1
  change P.smoothPurityMap f d K hK ≫ (P.compositionExceptional f).map a =
    (P.compositionShiftedPullback f d).map a ≫ P.smoothPurityMap f d L hL at hn
  unfold coefficientValuedSmoothTrace
  rw [Category.assoc, ← smoothCounit_naturality P f hK hL a, ← Category.assoc,
    ← Functor.map_comp, hn, Functor.map_comp, Category.assoc]

/-- The coefficient-unit smooth trace reduces to the specified unit trace.
Source: blueprint Step 6, trace paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: specialize coefficient-valued trace compatibility to the coefficient unit.
Its finite-Tor amplitude is [0,0] and it is constructible. The explicit unit
presentation of smoothTrace agrees with that specialization by the uniqueness
of smoothPurityTensorMap. The scalar-unit map is the normalized rank-one tensor
comparison. Naturality in the coefficient input then gives the displayed formula. -/
theorem finiteReductionOfUnitSmoothTrace (d : ℕ) [SmoothOfRelativeDimension d f] :
    (P.finiteReduction m hm hmn Y).map (P.smoothTrace f d) ≫
        P.finiteReductionUnitComparison m hm hmn Y =
      P.finiteReductionCompactSupportComparison m hm hmn f
          ((P.compositionShiftedPullback f d).obj (P.coefficientUnit Y)) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
          ((P.finiteReductionSourceComparison m hm hmn f d (P.coefficientUnit Y)).hom ≫
            ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
              (P.finiteReductionUnitComparison m hm hmn Y)) ≫
        (P.finiteReductionSetting m hm).smoothTrace f d := by
  let Q := P.finiteReductionSetting m hm
  have hU := coefficientUnit_ctf P (Y := Y)
  have hV := coefficientUnit_ctf Q (Y := Y)
  have hRU := P.finiteReduction_preserves_ctf m hm hmn Y (P.coefficientUnit Y) hU
  rw [smoothTrace_eq_coefficientTrace P f d hU,
    P.finiteReductionOfSmoothTrace m hm hmn f d (P.coefficientUnit Y) hU,
    Category.assoc, Category.assoc,
    smoothTrace_naturality Q f d hRU hV (P.finiteReductionUnitComparison m hm hmn Y),
    ← smoothTrace_eq_coefficientTrace Q f d hV,
    Functor.map_comp, Category.assoc]

end Morphism
section Composition
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y Z : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [Z.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Z ↘ Spec (.of P.field.k))]
variable [IsSeparated (Z ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
variable (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]

set_option linter.unusedSectionVars false in
/-- The entire three-arrow composition formula reduces to the formula with the
specified smaller-coefficient source and exceptional composition arrows.
Source: blueprint Step 6, composition paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: apply the purity reduction square to the composite f followed by g.
Rewrite both purity maps using composition coherence. This gives precisely the
three-arrow paths with the specified source and exceptional composition arrows,
without separate reduction identities for the two outer comparison arrows. -/
theorem finiteReductionOfCompositionCoherence
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    (P.finiteReduction m hm hmn X).map
        ((P.compositionSourceIdentification f g d e K).hom ≫
          (P.compositionShiftedPullback f d).map (P.smoothPurityMap g e K hK) ≫
          P.smoothPurityMap f d ((P.compositionExceptional g).obj K)
            (P.compositionExceptional_ctf g e K hK) ≫
          (P.compositionExceptionalIso f g K hK).inv) ≫
        P.finiteReductionExceptionalComparison m hm hmn (f ≫ g) (d + e) K hK =
      (P.finiteReductionSourceComparison m hm hmn (f ≫ g) (d + e) K).hom ≫
        ((P.finiteReductionSetting m hm).compositionSourceIdentification f g d e
          ((P.finiteReduction m hm hmn Z).obj K)).hom ≫
        ((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
          ((P.finiteReductionSetting m hm).smoothPurityMap g e
            ((P.finiteReduction m hm hmn Z).obj K)
            (P.finiteReduction_preserves_ctf m hm hmn Z K hK)) ≫
        (P.finiteReductionSetting m hm).smoothPurityMap f d
          (((P.finiteReductionSetting m hm).compositionExceptional g).obj
            ((P.finiteReduction m hm hmn Z).obj K))
          ((P.finiteReductionSetting m hm).compositionExceptional_ctf g e
            ((P.finiteReduction m hm hmn Z).obj K)
            (P.finiteReduction_preserves_ctf m hm hmn Z K hK)) ≫
        ((P.finiteReductionSetting m hm).compositionExceptionalIso f g
          ((P.finiteReduction m hm hmn Z).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Z K hK)).inv := by
  have h := P.finiteReductionOfPurity m hm hmn (f ≫ g) (d + e) K hK
  rw [P.smoothPurityCompositionCoherence f g d e K hK,
    (P.finiteReductionSetting m hm).smoothPurityCompositionCoherence f g d e] at h
  exact h
end Composition
section BaseChange
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X X' Y Y' : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
variable [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X' ↘ Spec (.of P.field.k))]
variable [IsSeparated (X' ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y' ↘ Spec (.of P.field.k))]
variable (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
variable [u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
variable [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
variable (sq : IsPullback u f' f v) (d : ℕ)
variable [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']

private theorem reduction_inverse_pasting
    {C : Type v} [Category.{w} C] {D : Type v} [Category.{w} D] (Q : C ⥤ D)
    {A B C₀ D₀ : C} {A' B' C' D' : D}
    (a : A ≅ B) (b : A ≅ C₀) (c : C₀ ≅ D₀)
    (a' : A' ≅ B') (b' : A' ≅ C') (c' : C' ≅ D')
    (sA : Q.obj A ⟶ A') (sB : Q.obj B ⟶ B')
    (sC : Q.obj C₀ ⟶ C') (sD : Q.obj D₀ ⟶ D')
    (ha : Q.map a.hom ≫ sB = sA ≫ a'.hom)
    (hb : Q.map b.hom ≫ sC = sA ≫ b'.hom)
    (hc : Q.map c.hom ≫ sD = sC ≫ c'.hom) :
    Q.map (a.inv ≫ b.hom ≫ c.hom) ≫ sD =
      sB ≫ a'.inv ≫ b'.hom ≫ c'.hom := by
  apply (cancel_epi (Q.map a.hom)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← Q.map_comp_assoc, Iso.hom_inv_id, Q.map_id, Category.id_comp,
    hc, ← Category.assoc, hb]
  rw [← Category.assoc (Q.map a.hom), ha]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

set_option linter.unusedSectionVars false in
private theorem finiteReductionPullback_naturality
    {S T : Scheme.{u}} (v : S ⟶ T)
    {K L : Scheme.proEtaleDerivedCategory T P.Ring} (a : K ⟶ L) :
    (P.finiteReduction m hm hmn S).map ((P.finiteReductionPullback v).map a) ≫
        (P.finiteReductionPullbackComparison m hm hmn v L).hom =
      (P.finiteReductionPullbackComparison m hm hmn v K).hom ≫
        ((P.finiteReductionSetting m hm).finiteReductionPullback v).map
          ((P.finiteReduction m hm hmn T).map a) := by
  let e := Functor.isoWhiskerRight (P.finiteReductionRawPullbackModel v).symm
      (P.finiteReduction m hm hmn S) ≪≫
    (Scheme.proEtaleReductionPullbackIso v
      (Scheme.proEtaleConstantRing T P.Ring)
      (Scheme.proEtaleConstantRing T (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRing S P.Ring)
      (Scheme.proEtaleConstantRing S (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingMap (T := S) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingComparison v P.Ring)
      (Scheme.proEtaleConstantRingComparison v (P.finiteReductionSetting m hm).Ring)
      (P.finiteReductionCoefficientSquare m hm hmn v)).symm ≪≫
    Functor.isoWhiskerLeft (P.finiteReduction m hm hmn T)
      ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel v)
  simpa only [e, finiteReductionPullbackComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.app_hom, Iso.app_inv,
    Functor.comp_map, Functor.mapIso_hom, Functor.mapIso_inv] using e.hom.naturality a


/-- Reduction preserves both specified vertical arrows in the smooth base-change square.
The base morphism v is arbitrary; all extra displayed properties of f' are its
Cartesian pullback properties, not restrictions on v.
Source: blueprint Step 6, base-change paragraph
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: for the first equality use the independent root charts. Their coefficient
normalization, exact shift comparison and ordinary pullback compositors commute
with coefficient extension on K-flat representatives, so the middle source arrow
is precisely the one at the smaller coefficient level. For the second equality,
substitute the literal purity composite defining both exchanges. Apply the purity
reduction square to f and f', naturality of the pullback coefficient comparison,
and the first equality. The inverse of an isomorphism reduces to the inverse
under these comparisons. This identifies the actual exchange arrow at level m,
and hence every edge of the smooth base-change square, without a condition on v. -/
theorem finiteReductionOfBaseChange (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    ((P.finiteReduction m hm hmn X').map
        (P.finiteReductionBaseChangeSource u f' f v sq d K).hom ≫
      (P.finiteReductionSourceComparison m hm hmn f' d
        ((P.finiteReductionPullback v).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).compositionShiftedPullback f' d).map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom =
    (P.finiteReductionPullbackComparison m hm hmn u
        ((P.compositionShiftedPullback f d).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionBaseChangeSource
        u f' f v sq d ((P.finiteReduction m hm hmn Y).obj K)).hom) ∧
    ((P.finiteReduction m hm hmn X').map
        (P.finiteReductionSmoothExchange u f' f v sq d K hK).hom ≫
      P.finiteReductionExceptionalComparison m hm hmn f' d
        ((P.finiteReductionPullback v).obj K) (P.finiteReductionBaseChangeInput v K hK) ≫
      ((P.finiteReductionSetting m hm).compositionExceptional f').map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom =
    (P.finiteReductionPullbackComparison m hm hmn u
        ((P.compositionExceptional f).obj K)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback u).map
        (P.finiteReductionExceptionalComparison m hm hmn f d K hK) ≫
      ((P.finiteReductionSetting m hm).finiteReductionSmoothExchange u f' f v sq d
        ((P.finiteReduction m hm hmn Y).obj K)
        (P.finiteReduction_preserves_ctf m hm hmn Y K hK)).hom) := by
  let Q := P.finiteReductionSetting m hm
  let R := P.finiteReduction m hm hmn
  let L := (P.finiteReductionPullback v).obj K
  have hL := P.finiteReductionBaseChangeInput v K hK
  have hRK := P.finiteReduction_preserves_ctf m hm hmn Y K hK
  have hRL := P.finiteReduction_preserves_ctf m hm hmn Y' L hL
  let := P.finiteReductionPurityIsIso f d K hK
  let := P.finiteReductionPurityIsIso f' d L hL
  let := Q.finiteReductionPurityIsIso f d ((R Y).obj K) hRK
  let := Q.finiteReductionPurityIsIso f' d
    ((Q.finiteReductionPullback v).obj ((R Y).obj K))
    (Q.finiteReductionBaseChangeInput v ((R Y).obj K) hRK)
  have hs := P.finiteReduction_baseChangeSource m hm hmn u f' f v sq d K
  refine ⟨hs, ?_⟩
  have hn := (Q.smoothPurityMap_naturality_choice_independence f' d
    ((R Y').obj L) ((Q.finiteReductionPullback v).obj ((R Y).obj K)) hRL
    (Q.finiteReductionBaseChangeInput v ((R Y).obj K) hRK)
    (P.finiteReductionPullbackComparison m hm hmn v K).hom).1
  change Q.smoothPurityMap f' d ((R Y').obj L) hRL ≫
      (Q.compositionExceptional f').map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom =
    (Q.compositionShiftedPullback f' d).map
        (P.finiteReductionPullbackComparison m hm hmn v K).hom ≫
      Q.smoothPurityMap f' d ((Q.finiteReductionPullback v).obj ((R Y).obj K))
        (Q.finiteReductionBaseChangeInput v ((R Y).obj K) hRK) at hn
  have hc := P.finiteReductionOfPurity m hm hmn f' d L hL
  have ha := P.finiteReductionOfPurity m hm hmn f d K hK
  have hp := finiteReductionPullback_naturality P m hm hmn u
    (P.smoothPurityMap f d K hK)
  change (R X').map
      ((P.finiteReductionPullback u).map (P.smoothPurityMap f d K hK)) ≫
        (P.finiteReductionPullbackComparison m hm hmn u
          ((P.compositionExceptional f).obj K)).hom =
    (P.finiteReductionPullbackComparison m hm hmn u
        ((P.compositionShiftedPullback f d).obj K)).hom ≫
      (Q.finiteReductionPullback u).map ((R X).map (P.smoothPurityMap f d K hK)) at hp
  have hleft :
      (R X').map ((P.finiteReductionPullback u).map (P.smoothPurityMap f d K hK)) ≫
          ((P.finiteReductionPullbackComparison m hm hmn u
            ((P.compositionExceptional f).obj K)).hom ≫
          (Q.finiteReductionPullback u).map
            (P.finiteReductionExceptionalComparison m hm hmn f d K hK)) =
        ((P.finiteReductionPullbackComparison m hm hmn u
          ((P.compositionShiftedPullback f d).obj K)).hom ≫
          (Q.finiteReductionPullback u).map
            (P.finiteReductionSourceComparison m hm hmn f d K).hom) ≫
        (Q.finiteReductionPullback u).map (Q.smoothPurityMap f d ((R Y).obj K) hRK) := by
    rw [← Category.assoc, hp, Category.assoc, ← Functor.map_comp, ha,
      Functor.map_comp, ← Category.assoc]
  have hright :
      (R X').map (P.smoothPurityMap f' d L hL) ≫
          (P.finiteReductionExceptionalComparison m hm hmn f' d L hL ≫
            (Q.compositionExceptional f').map
              (P.finiteReductionPullbackComparison m hm hmn v K).hom) =
        ((P.finiteReductionSourceComparison m hm hmn f' d L).hom ≫
          (Q.compositionShiftedPullback f' d).map
            (P.finiteReductionPullbackComparison m hm hmn v K).hom) ≫
        Q.smoothPurityMap f' d ((Q.finiteReductionPullback v).obj ((R Y).obj K))
          (Q.finiteReductionBaseChangeInput v ((R Y).obj K) hRK) := by
    rw [← Category.assoc, hc, Category.assoc, hn, ← Category.assoc]
  have h := reduction_inverse_pasting (R X')
    ((P.finiteReductionPullback u).mapIso (asIso (P.smoothPurityMap f d K hK)))
    (P.finiteReductionBaseChangeSource u f' f v sq d K)
    (asIso (P.smoothPurityMap f' d L hL))
    ((Q.finiteReductionPullback u).mapIso
      (asIso (Q.smoothPurityMap f d ((R Y).obj K) hRK)))
    (Q.finiteReductionBaseChangeSource u f' f v sq d ((R Y).obj K))
    (asIso (Q.smoothPurityMap f' d
      ((Q.finiteReductionPullback v).obj ((R Y).obj K))
      (Q.finiteReductionBaseChangeInput v ((R Y).obj K) hRK)))
    _ _ _ _ hleft (by simpa only [Category.assoc] using hs) hright
  simpa only [finiteReductionSmoothExchange, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, Category.assoc, R, Q, L] using h

end BaseChange

/-- Finite reduction preserves the Kummer-normalized affine orientation itself.
The two comparisons are fixed independently by primitive-root and counit equations.
Source: blueprint finite-reduction statement, affine-orientation clause
(blueprint: thm-pur-finite-reduction-of-purity).
Proof: realize the supported coordinate Kummer boundary in the ordinary derived
category. The scalar quotient sends its relative Kummer extension to the extension
at the smaller coefficient level, independently of the annihilating exponent.
Supported-boundary uniqueness identifies the reduced supported class. The standing
exceptional adjunction and the counit-normalized exceptional comparison identify
its reduced adjoint with the adjoint at the smaller level. Comparison pullback and
intrinsic realization preserve these composites, proving the displayed equation.
This covers every positive level, including ramified levels and equal indices. -/
theorem finiteReductionOfAffineOrientation
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))] :
    (P.finiteReduction m hm hmn Y).map (P.finiteReductionOrientation Y) ≫
      P.finiteReductionOrientationExceptionalComparison m hm hmn Y ≫
      ((P.finiteReductionSetting m hm).compositionExceptional
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).map
          (P.finiteReductionOrientationInputComparison m hm hmn Y).hom =
    P.finiteReductionUnitComparison m hm hmn Y ≫
      (P.finiteReductionSetting m hm).finiteReductionOrientation Y := by
  exact FiniteDiagonalReduction.affineOrientationReduction P m hm hmn Y

end WeilConjectures.PurityFiniteSetting
