/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.CompactSupportCoefficientChange
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleEssentiallySmall
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.FixSiteOpenExchange
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SecSmoothPurity.DirectImageScalarExchange
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.SecSmoothPurity.OpenScalarExchange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj

/-! # Ordinary-etale coefficient comparison for compact support

Source: Stacks Project, Tags 0GL5, 0GL6 and 07A6
(blueprint: lem-fix-compact-support-coefficient-change).
These are universal tensor presentations on the ordinary-etale site. The existing
pro-etale presentations and their normalized comparisons are imported unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The inverse mate of the canonical restriction/inverse-image identification on
sheaves. Source: Stacks Tags 03S2 and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change). -/
def coefficientRestrictionOpenMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars Z.smallEtaleTopology φ :=
  (mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).symm
      (asIso (upperStarRestrictScalars φ j).natTrans).inv

/-- The open coefficient mate is invertible. Source: Stacks Tags 03S2 and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: on the open both composites are the same module with restricted scalars;
off the open both are zero. The identity comparison has inverse the same identity.
Its transpose is the restriction/inverse-image identification, since both transposes
are the open unit. Thus it is the displayed mate, not an arbitrary isomorphism. -/
theorem coefficientRestrictionOpenMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (coefficientRestrictionOpenMap φ j) := by
  have hopen (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      IsIso ((j)^*[ModuleCat.{u + 1} A].map
        ((coefficientRestrictionOpenMap φ j).app F)) := by
    have h := unit_mateEquiv_symm
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      (asIso (upperStarRestrictScalars φ j).natTrans).inv F
    change _ = _ ≫ (j)^*[ModuleCat.{u + 1} A].map
      ((coefficientRestrictionOpenMap φ j).app F) at h
    dsimp only [Functor.id_obj] at h
    have hi : IsIso ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F) ≫
        (j)^*[ModuleCat.{u + 1} A].map
          ((coefficientRestrictionOpenMap φ j).app F)) := by
      rw [← h]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hi
  have happ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      IsIso ((coefficientRestrictionOpenMap φ j).app F) := by
    refine Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
    let t := Z.algClosurePoint x
    by_cases ht : t.base (IsLocalRing.closedPoint _) ∈ Set.range j.base
    · have h := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map
        (ModuleCat.{u + 1} A) j _ (hopen F)
        (IsOpenImmersion.lift j t (Scheme.range_base_subset_of_closedPoint_mem t ht))
      rw [IsOpenImmersion.lift_fac] at h
      exact h
    · have hd : Disjoint (Set.range j.base) (Set.range t.base) := by
        rw [Set.disjoint_right]
        rintro _ ⟨p, rfl⟩
        simpa only [Subsingleton.elim p (IsLocalRing.closedPoint _)] using ht
      have h₁ := isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
        (ModuleCat.{u + 1} A) j t hd
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F)
      have h₂ := ((Sheaf.restrictScalars _ φ).map_isZero
        (isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
          (ModuleCat.{u + 1} B) j t hd F)).of_iso
        ((asIso (upperStarRestrictScalars φ t).natTrans).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj F))
      have hi : IsIso ((t)^*[ModuleCat.{u + 1} A].map
          ((coefficientRestrictionOpenMap φ j).app F)) :=
        ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
      have h := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map
        (ModuleCat.{u + 1} A) t _ hi (𝟙 _)
      rw [Category.id_comp] at h
      exact h
  exact NatIso.isIso_of_isIso_app _

/-- The open restriction comparison descends termwise to bounded-below complexes.
Source: Stacks Tag 0GL6 (blueprint: lem-fix-compact-support-coefficient-change). -/
def coefficientRestrictionOpenPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  letI := coefficientRestrictionOpenMap_isIso φ j
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (asIso (coefficientRestrictionOpenMap φ j)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical proper/open scalar restriction comparison, with its direction
fixed by the open unit and the direct-image resolution map.
Source: Stacks Tag 0GL6 (blueprint: lem-fix-compact-support-coefficient-change). -/
def compactSupportCoefficientRestrictionPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c ⋙
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientRestrictionOpenPlus φ c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (rightDerivedLowerStarRestrictScalars φ c.g)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- A bounded-below presentation of the actual derived tensor, retaining its universal
arrow in the ambient derived category. Source: Stacks Tags 06YY and 07A6
(blueprint: lem-fix-compact-support-coefficient-change). -/
structure CoefficientTensorModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) where
  obj : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
  unit : K ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj obj
  universal : Sheaf.IsDerivedBaseChange unit.hom

/-- Scalar extension of a morphism, uniquely specified by the universal arrows.
Source: Stacks Tag 07A6 (blueprint: lem-fix-compact-support-coefficient-change). -/
def CoefficientTensorModel.map
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B} {T : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) (N : CoefficientTensorModel φ T L) (f : K ⟶ L) :
    M.obj ⟶ N.obj :=
  ObjectProperty.homMk ((Equiv.ofBijective _ (M.universal N.obj.obj)).symm
    (f.hom ≫ N.unit.hom))

/-- The canonical B-linear comparison is the unique arrow with the proper/open
restriction adjunct. Source: Stacks Tags 0GL5, 0GL6 and 07A6
(blueprint: lem-fix-compact-support-coefficient-change). -/
def compactSupportCoefficientComparisonPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K)) :
    N.obj ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c).obj M.obj :=
  ObjectProperty.homMk ((Equiv.ofBijective _ (N.universal _)).symm
    (((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map M.unit ≫
      (compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj).hom))

/-- The canonical ordinary-etale coefficient comparison is invertible for finite rings.
Source: Stacks Tags 0GL5 and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: write compact support as the proper direct image after open extension. The
open coefficient mate is an isomorphism by its unit normalization. For the proper
factor use the torsion-ring unbounded proper projection formula, applied to the
constant B-module; the canonical direct-image coefficient arrow is its counit mate.
The universal tensor bijections identify this B-linear composite with the displayed
comparison. Restricting back to the bounded-below full subcategory reflects its
invertibility. This is the ordinary-etale part of the coefficient-change argument. -/
theorem compactSupportCoefficientComparisonPlus_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {φ : A →+* B} {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    {f : X ⟶ Y} (c : Compactification f)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K)) :
    IsIso (compactSupportCoefficientComparisonPlus c M N) := by
  sorry

/-- Finite Tor amplitude ensures that reduction has a bounded tensor presentation;
no flatness of the coefficient map is assumed. Source: Stacks Tags 06YY and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: use lem-sf-flat-model on the bounded constructible finite-Tor input and tensor
its bounded flat representative termwise. The result stays bounded, even for a
nonflat quotient. K-flat localization gives the unit, which satisfies the ambient
universal property by lem-pur-derived-change-of-rings and its tensor adjunction. -/
theorem nonempty_coefficientTensorModel_of_finiteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hn : 1 ≤ n) (hmn : n ≤ m)
    (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
    (_hK : WeilConjectures.finiteTorConstructibleEtale l E m (hn.trans hmn) T K.obj) :
    Nonempty (CoefficientTensorModel
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E m)
        (T := Padic.coefficientExtensionIdeal l E n) (Ideal.pow_le_pow_right hmn))) T K) := by
  sorry

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- A universal tensor of a finite-Tor ordinary-etale realization remains bounded
below of etale origin, including for nonflat finite reduction.
Source: Stacks Tags 06YY and 0GL6
(blueprint: lem-fix-compact-support-coefficient-change).
Proof: choose a bounded flat representative of K₀ by lem-sf-flat-model. Its termwise
coefficient reduction stays bounded and flat (lem-sf-reduction-flat-model). Exact
comparison inverse image commutes with this tensor, by the representative-normalized
ringed-topos tensor comparison. Thus its comparison pullback presents the derived
scalar extension of K. The universal-arrow bijection identifies every presentation
M with that bounded-below etale realization. This is the domain calculation of
lem-sf-compact-coefficient-composition, proof step 2, without exceptional adjunctions. -/
theorem CoefficientTensorModel.origin_of_etale_finiteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m n : ℕ) (hn : 1 ≤ n) (hmn : n ≤ m)
    {T : Scheme.{u}}
    (K₀ : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m)))))
    (_hK₀ : WeilConjectures.finiteTorConstructibleEtale l E m (hn.trans hmn) T K₀.obj)
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))))}
    (_e : (comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E m))) T).mapDerivedCategory.obj K₀.obj ≅ K)
    (M : CoefficientTensorModel
      (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
        (S := Padic.coefficientExtensionIdeal l E m)
        (T := Padic.coefficientExtensionIdeal l E n) (Ideal.pow_le_pow_right hmn))) T K) :
    DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) T M.obj := by
  sorry

end AlgebraicGeometry.ProEtale
