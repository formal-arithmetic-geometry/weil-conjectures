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

set_option linter.unusedSectionVars false in
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

attribute [-instance] WeilConjectures.finiteHomEtaleCategory in
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
set_option linter.unusedSectionVars false in
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

set_option linter.unusedSectionVars false in
end BaseChange

end WeilConjectures.PurityFiniteSetting
