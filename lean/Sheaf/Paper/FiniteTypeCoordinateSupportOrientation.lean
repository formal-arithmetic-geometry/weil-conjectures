/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Sheaf.AlgebraicGeometry.EtaleCoordinateSupport
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.Paper.SupportedCup
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.Paper.SupportedCupFunctoriality
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence
import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
import Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
import Sheaf.AlgebraicGeometry.SupportLongExact
import Sheaf.Paper.FiniteTateSiteDescent
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Finite-type coordinate support orientations

Source: Stacks Project, Tags 09XP and 09XQ; blueprint main-20261015,
cor-pur-affine-space-zero-section-purity, proof
(blueprint: lem-pur-finite-type-coordinate-support-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The signed ordinary finite twist, at the universal annihilator ell^n.
Source: blueprint zero-section calculation, finite etale witness
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
abbrev coordinateTwist (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℤ) :=
  P.functorialCupTwist false X r

/-- Degree-zero placement in the existing bounded-below category.
Source: Stacks 09XP (blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
abbrev coordinateSingle (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0

/-- The actual bounded-below derived kernel inclusion, followed by R(id)=id.
Source: Stacks 09XP, kernel inclusion
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateDerivedInclusion (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (Etale.coordinateSupportSheaf P.Coefficient i).rightDerivedFunctorPlus ⟶ 𝟭 _ :=
  Functor.rightDerivedFunctorPlusNatTrans (Etale.coordinateSupportInclusion P.Coefficient i) ≫
    (Functor.rightDerivedFunctorPlusIdIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))).hom

/-- The family of orientations, written in the equivalent forward, shifted direction.
Source: blueprint zero-section calculation
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def CoordinateOrientationFamily (P : PurityFiniteSetting.{u}) (b : ℕ) :=
  ∀ (B : Scheme.{u}) [IsAffine B] (a : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] (r : ℤ),
    (P.coordinateSingle (AffineSpace (ULift.{u} (Fin b)) B)).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).obj
            (P.coordinateTwist B (r - (b : ℤ)))) ≅
      ((Etale.coordinateSupportSheaf P.Coefficient
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).rightDerivedFunctorPlus.obj
          ((P.coordinateSingle (AffineSpace (ULift.{u} (Fin b)) B)).obj
            (P.coordinateTwist (AffineSpace (ULift.{u} (Fin b)) B) r)))⟦2 * (b : ℤ)⟧

/-- The actual counit representative of an orientation in the unbounded category.
Source: Stacks 09XP, closed-support counit
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateOrientationCounit (P : PurityFiniteSetting.{u}) (b : ℕ)
    (θ : P.CoordinateOrientationFamily b) (B : Scheme.{u}) [IsAffine B]
    (a : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType a] [QuasiCompact a] (r : ℤ) :
    (DerivedCategory.singleFunctor
      (Sheaf (AffineSpace (ULift.{u} (Fin b)) B).smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).obj
            (P.coordinateTwist B (r - (b : ℤ)))) ⟶
      ((DerivedCategory.singleFunctor
      (Sheaf (AffineSpace (ULift.{u} (Fin b)) B).smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (P.coordinateTwist (AffineSpace (ULift.{u} (Fin b)) B) r))⟦2 * (b : ℤ)⟧ :=
  DerivedCategory.Plus.ι.map ((θ B a r).hom ≫
    ((P.coordinateDerivedInclusion (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).app
      ((P.coordinateSingle (AffineSpace (ULift.{u} (Fin b)) B)).obj
        (P.coordinateTwist (AffineSpace (ULift.{u} (Fin b)) B) r)))⟦2 * (b : ℤ)⟧') ≫
    (DerivedCategory.Plus.ι.commShiftIso (2 * (b : ℤ))).hom.app
      ((P.coordinateSingle (AffineSpace (ULift.{u} (Fin b)) B)).obj
        (P.coordinateTwist (AffineSpace (ULift.{u} (Fin b)) B) r))

/-- The unshifted generator representative at r=b, with b-b identified with zero.
Source: blueprint ordered coordinate orientation
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateOrientationClass (P : PurityFiniteSetting.{u}) (b : ℕ)
    (θ : P.CoordinateOrientationFamily b) (B : Scheme.{u}) [IsAffine B]
    (a : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType a] [QuasiCompact a] :
    P.FunctorialCupH false (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
      (2 * (b : ℤ)) (b : ℤ) :=
  (DerivedCategory.singleFunctor _ 0).map
    ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).map
        (eqToHom (congrArg (P.coordinateTwist B) (sub_self (b : ℤ)).symm))) ≫
    P.coordinateOrientationCounit b θ B a (b : ℤ)

/-- Pull a basis of the constant field line to an arbitrary k-scheme using the
constant and root-normalized inverse-image comparisons. No basis is fixed.
Source: blueprint constant-line tensor argument
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateBasis (P : PurityFiniteSetting.{u}) (s : ℤ)
    (ε : P.constantEtale (Spec (.of P.field.k)) ≅
      P.coordinateTwist (Spec (.of P.field.k)) s)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) :
    P.constantEtale X ≅ P.coordinateTwist X s :=
  ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) a).app
    (ModuleCat.of P.Coefficient P.Coefficient)).symm ≪≫
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).mapIso ε ≪≫
    P.functorialCupEtaleTwistPullback a (𝟙 _) s

/-- Tensoring with a field-line generator and the signed Tate multiplication.
Source: blueprint tensor extension from r=b; negative powers use evaluation
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateBasisTwist (P : PurityFiniteSetting.{u}) (b : ℕ) (r : ℤ)
    (ε : P.constantEtale (Spec (.of P.field.k)) ≅
      P.coordinateTwist (Spec (.of P.field.k)) (r - (b : ℤ)))
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) :
    P.coordinateTwist X (b : ℤ) ⟶ P.coordinateTwist X r :=
  (ρ_ (P.coordinateTwist X (b : ℤ))).inv ≫
    P.coordinateTwist X (b : ℤ) ◁ (P.coordinateBasis (r - (b : ℤ)) ε X a).hom ≫
    (P.functorialCupTwistProduct false X a (b : ℤ) (r - (b : ℤ))).hom ≫
    eqToHom (congrArg (P.coordinateTwist X) (add_sub_cancel (b : ℤ) r))

/-- The product-normalized family. Support is identified scheme-theoretically,
and comparison is on supported Hom, so the normalization does not forget support.
Source: blueprint zero-section proof, ordered iteration and empty product
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def CoordinateOrientationNormalization (P : PurityFiniteSetting.{u}) (b : ℕ)
    (θ : P.CoordinateOrientationFamily b) : Prop :=
  ∀ (B : Scheme.{u}) [IsAffine B] (a : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a],
    ∃ e : (AffineSpace (ULift.{u} (Fin b)) B).zeroLocusSubscheme
        (Set.range (fun j : Fin b ↦ AffineSpace.coord B (ULift.up j))) ≅ B,
      ∃ he : e.hom ≫ AffineSpace.zeroSection (ULift.{u} (Fin b)) B =
          (AffineSpace (ULift.{u} (Fin b)) B).zeroLocusSubschemeι
            (Set.range (fun j : Fin b ↦ AffineSpace.coord B (ULift.up j))),
        (P.functorialCupSingle true (AffineSpace (ULift.{u} (Fin b)) B)).map
            (P.functorialCupSupportMap true
              (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
              ((AffineSpace (ULift.{u} (Fin b)) B).zeroLocusSubschemeι
                (Set.range (fun j : Fin b ↦ AffineSpace.coord B (ULift.up j))))
              e.hom he) ≫
          P.frameBoundaryProduct (AffineSpace (ULift.{u} (Fin b)) B)
            ((AffineSpace (ULift.{u} (Fin b)) B) ↘ B ≫ a) b
            (fun j : Fin b ↦ AffineSpace.coord B (ULift.up j)) =
          P.functorialCupCompare (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
            (2 * (b : ℤ)) (b : ℤ) (P.coordinateOrientationClass b θ B a)

/-- All signed orientations are obtained by tensoring the normalized orientation
with the constant line. Quantification over every generator asserts basis independence.
Source: blueprint zero-section proof, constant-line tensor argument
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def CoordinateOrientationTensor (P : PurityFiniteSetting.{u}) (b : ℕ)
    (θ : P.CoordinateOrientationFamily b) : Prop :=
  (∀ s : ℤ, Nonempty (P.constantEtale (Spec (.of P.field.k)) ≅
    P.coordinateTwist (Spec (.of P.field.k)) s)) ∧
  ∀ (B : Scheme.{u}) [IsAffine B] (a : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] (r : ℤ)
    (ε : P.constantEtale (Spec (.of P.field.k)) ≅
      P.coordinateTwist (Spec (.of P.field.k)) (r - (b : ℤ))),
    (DerivedCategory.singleFunctor _ 0).map
        ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).map
            (P.coordinateBasis (r - (b : ℤ)) ε B a).hom) ≫
      P.coordinateOrientationCounit b θ B a r =
    P.coordinateOrientationClass b θ B a ≫
      ((DerivedCategory.singleFunctor _ 0).map
        (P.coordinateBasisTwist b r ε (AffineSpace (ULift.{u} (Fin b)) B)
          ((AffineSpace (ULift.{u} (Fin b)) B) ↘ B ≫ a)))⟦2 * (b : ℤ)⟧'

/-- The canonical closed base-change map with the root-normalized twist comparison.
Source: blueprint final base-change paragraph, Stacks 03Q1
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateTwistedExchange (P : PurityFiniteSetting.{u}) (b : ℕ)
    {B B' : Scheme.{u}} (g : B' ⟶ B) (a : B ⟶ Spec (.of P.field.k))
    (sq : IsPullback g (AffineSpace.zeroSection (ULift.{u} (Fin b)) B')
      (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
      (AffineSpace.map (ULift.{u} (Fin b)) g)) (s : ℤ) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.map (ULift.{u} (Fin b)) g)).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).obj (P.coordinateTwist B s)) ⟶
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin b)) B')).obj (P.coordinateTwist B' s) :=
  (Etale.baseChangeMap (ModuleCat.{u + 1} P.Coefficient) sq.toCommSq).app
      (P.coordinateTwist B s) ≫
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin b)) B')).map
        (P.functorialCupEtaleTwistPullback g a s).hom

/-- Naturality is stated for the actual counit representatives. By closed adjunction
this is precisely the square for the canonical supported inverse-image map.
Source: blueprint final base-change paragraph, Stacks 09XP
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def CoordinateOrientationBaseChange (P : PurityFiniteSetting.{u}) (b : ℕ)
    (θ : P.CoordinateOrientationFamily b) : Prop :=
  ∀ (B B' : Scheme.{u}) [IsAffine B] [IsAffine B']
    (a : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType a] [QuasiCompact a]
    (g : B' ⟶ B) [LocallyOfFiniteType (g ≫ a)] [QuasiCompact (g ≫ a)],
    ∃ sq : IsPullback g (AffineSpace.zeroSection (ULift.{u} (Fin b)) B')
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
        (AffineSpace.map (ULift.{u} (Fin b)) g),
      ∀ r : ℤ,
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            (AffineSpace.map (ULift.{u} (Fin b)) g)).mapDerivedCategory.map
              (P.coordinateOrientationCounit b θ B a r) ≫
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            (AffineSpace.map (ULift.{u} (Fin b)) g)).mapDerivedCategory.commShiftIso
              (2 * (b : ℤ))).hom.app
                ((DerivedCategory.singleFunctor _ 0).obj
                  (P.coordinateTwist (AffineSpace (ULift.{u} (Fin b)) B) r)) ≫
          (((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
              (AffineSpace.map (ULift.{u} (Fin b)) g)).mapDerivedCategorySingleFunctor 0).hom.app
                (P.coordinateTwist (AffineSpace (ULift.{u} (Fin b)) B) r) ≫
            (DerivedCategory.singleFunctor _ 0).map
              (P.functorialCupEtaleTwistPullback (AffineSpace.map (ULift.{u} (Fin b)) g)
                ((AffineSpace (ULift.{u} (Fin b)) B) ↘ B ≫ a) r).hom)⟦2 * (b : ℤ)⟧' =
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            (AffineSpace.map (ULift.{u} (Fin b)) g)).mapDerivedCategorySingleFunctor 0).hom.app
              ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
                (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).obj
                  (P.coordinateTwist B (r - (b : ℤ)))) ≫
          (DerivedCategory.singleFunctor _ 0).map
            (P.coordinateTwistedExchange b g a sq (r - (b : ℤ))) ≫
          P.coordinateOrientationCounit b θ B' (g ≫ a) r

/-- The existing small derived localization of abelian groups, shared explicitly.
Source: Stacks 09XP (blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
instance coordinateAbHasDerivedCategory : HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1} :=
  HasDerivedCategory.ofIsGrothendieckAbelian AddCommGrpCat.{u + 1}

/-- The existing small derived localization of coefficient modules.
Source: Stacks 09XP (blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
instance coordinateModuleHasDerivedCategory (P : PurityFiniteSetting.{u}) :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} P.Coefficient) :=
  HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient)

/-- Global sections in abelian sheaves, evaluated at the terminal etale object.
Source: Stacks 09XP (blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
abbrev coordinateAbelianGlobalSections (B : Scheme.{u}) :=
  Sheaf.Γ B.smallEtaleTopology AddCommGrpCat.{u + 1}

/-- Derived global sections in the same small localization as supported sections.
Source: Stacks 09XP (blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateDerivedAbelianGlobalSections (B : Scheme.{u}) :
    DerivedCategory.Plus.{u + 1} (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus.{u + 1} AddCommGrpCat.{u + 1} :=
  (coordinateAbelianGlobalSections B).rightDerivedFunctorPlus

/-- The actual fibre line L_s=A_k(s)(k), with its A-module structure retained.
Source: blueprint field specialization
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateFieldLine (P : PurityFiniteSetting.{u}) (s : ℤ) :
    ModuleCat.{u + 1} P.Coefficient :=
  (P.coordinateTwist (Spec (.of P.field.k)) s).obj.obj
    (op (Scheme.Etale.mk (𝟙 (Spec (.of P.field.k)))))

/-- Ordinary closed-support comparisons, including the module-to-abelian bridge.
The derived counit is fixed, rather than an arbitrary isomorphism of support objects.
Source: Stacks 09XP and 09XQ
(blueprint: lem-pur-finite-type-coordinate-support-orientation).
Proof: identify the two kernels sectionwise. The unit F→z_*z^*F is invertible
on a supported sheaf, and composing its inverse with the kernel inclusion is the
closed adjunction counit. Exact z_* and its exact left adjoint preserve injectives;
z^!_0 preserves injectives by z_* ⊣ z^!_0. Apply this identification to injective
resolutions to obtain RQ=z_*Rz^!_0, with the same inclusion and counit. Global
sections of the kernel are sections on B of z^!_0. Underlying injective module
sheaves are acyclic for abelian cohomology on X, its complement and B. The
support exact sequence is onto on sections on injectives, so its abelian long
exact sequence makes these resolutions support-acyclic too. Thus they compute
the abelian derived functor specified in def-pur-support-cohomology. -/
theorem coordinateSupport_closedComparison (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (a : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] (b : ℕ) :
    (∃ e : Etale.coordinateSupportSheaf P.Coefficient
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B) ≅
      Etale.closedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B).openComplement.ι ⋙
      Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B),
      e.hom ≫ (Etale.lowerStarClosedUpperShriekAdjunction
        (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B).openComplement.ι
        (Scheme.Hom.range_eq_compl_range_openComplement_ι _)).counit =
      Etale.coordinateSupportInclusion P.Coefficient
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)) ∧
    (∃ ρ : (Etale.coordinateSupportSheaf P.Coefficient
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).rightDerivedFunctorPlus ≅
      (Etale.closedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B).openComplement.ι).rightDerivedFunctorPlus ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)).mapDerivedCategoryPlus,
      ρ.hom ≫ (Etale.lowerStarClosedUpperShriekAdjunction
        (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B).openComplement.ι
        (Scheme.Hom.range_eq_compl_range_openComplement_ι _)).derivedPlus.counit =
      P.coordinateDerivedInclusion (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)) ∧
    Nonempty ((P.forgetEtale (AffineSpace (ULift.{u} (Fin b)) B)).mapDerivedCategoryPlus ⋙
        Etale.derivedSupportSections (AffineSpace.zeroSection (ULift.{u} (Fin b)) B) ≅
      (Etale.closedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B)
        (AffineSpace.zeroSection (ULift.{u} (Fin b)) B).openComplement.ι).rightDerivedFunctorPlus ⋙
      (P.forgetEtale B).mapDerivedCategoryPlus ⋙
      coordinateDerivedAbelianGlobalSections B) := by
  sorry

/-- Sections of the already recorded sheaf support kernel, not a new support functor.
Source: Stacks 09XP (blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
abbrev coordinateModuleGlobalSections (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)

/-- The actual derived evaluation functor, with the shared small localization.
Source: Stacks 09XP (blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
abbrev coordinateDerivedModuleGlobalSections (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    DerivedCategory.Plus.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) ⥤
    DerivedCategory.Plus.{u + 1} (ModuleCat.{u + 1} P.Coefficient) :=
  (P.coordinateModuleGlobalSections X).rightDerivedFunctorPlus

/-- The unique restriction-kernel identification, including its inclusion equation.
Source: Stacks 09XP (blueprint: lem-pur-finite-type-coordinate-support-orientation).
Proof: evaluate the sheaf kernel on the terminal etale object. The complement
adjunction unit there is restriction to the open complement, by the canonical
pullback of the terminal object. Kernels with their inclusions are unique. -/
theorem coordinateGlobalSupport_existsUnique (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃! e : Etale.coordinateGlobalSupport P.Coefficient i ≅
        Etale.coordinateSupportSheaf P.Coefficient i ⋙ P.coordinateModuleGlobalSections X,
      ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient),
        e.hom.app F ≫ (P.coordinateModuleGlobalSections X).map
            ((Etale.coordinateSupportInclusion P.Coefficient i).app F) =
          kernel.ι (F.obj.map (Etale.supportRestrictionArrow i).op) ≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
              (ModuleCat.{u + 1} P.Coefficient)
                (Scheme.Etale.isTerminalMkId X)).inv.app F := by
  sorry

/-- The derived support/global-sections comparison is obtained from that unique
kernel identification and the canonical composition theorem on injectives.
Source: Stacks 09XP and 09XQ
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateDerivedGlobalSupportIso (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (Etale.coordinateGlobalSupport P.Coefficient i).rightDerivedFunctorPlus ≅
      (Etale.coordinateSupportSheaf P.Coefficient i).rightDerivedFunctorPlus ⋙
        P.coordinateDerivedModuleGlobalSections X :=
  Functor.rightDerivedFunctorPlusNatIso
      (P.coordinateGlobalSupport_existsUnique i).exists.choose ≪≫
    Functor.rightDerivedFunctorPlusCompIso
      (Etale.coordinateSupportSheaf P.Coefficient i) (P.coordinateModuleGlobalSections X)

/-- Evaluate the actual closed pushforward of the field line. The map is the
pushforward/global-sections comparison followed by evaluation at the terminal object.
Source: blueprint field specialization
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateFieldSourceIso (P : PurityFiniteSetting.{u}) (b : ℕ) (s : ℤ) :
    (P.coordinateModuleGlobalSections
      (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.zeroSection (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).obj
            (P.coordinateTwist (Spec (.of P.field.k)) s)) ≅ P.coordinateFieldLine s :=
  (Etale.lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} P.Coefficient)
    (AffineSpace.zeroSection (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).app
      (P.coordinateTwist (Spec (.of P.field.k)) s) ≪≫
    (Sheaf.ΓNatIsoSheafSections (Spec (.of P.field.k)).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)
        (Scheme.Etale.isTerminalMkId (Spec (.of P.field.k)))).app
          (P.coordinateTwist (Spec (.of P.field.k)) s)

/-- The field comparison obtained from precisely the same orientation family,
through the original support kernel and its canonical derived/global comparison.
Source: blueprint zero-section proof, field calculation
(blueprint: lem-pur-finite-type-coordinate-support-orientation). -/
def coordinateFieldOrientation (P : PurityFiniteSetting.{u}) (b : ℕ)
    (θ : P.CoordinateOrientationFamily b) (r : ℤ) :
    (DerivedCategory.Plus.singleFunctor (ModuleCat.{u + 1} P.Coefficient) 0).obj
        (P.coordinateFieldLine (r - (b : ℤ))) ⟶
      ((Etale.coordinateGlobalSupport P.Coefficient
        (AffineSpace.zeroSection (ULift.{u} (Fin b))
          (Spec (.of P.field.k)))).rightDerivedFunctorPlus.obj
          ((P.coordinateSingle (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).obj
            (P.coordinateTwist (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k))) r)))⟦
              2 * (b : ℤ)⟧ :=
  (DerivedCategory.Plus.singleFunctor (ModuleCat.{u + 1} P.Coefficient) 0).map
      (P.coordinateFieldSourceIso b (r - (b : ℤ))).inv ≫
    (P.coordinateModuleGlobalSections
      (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).rightDerivedPlusSingleUnit
        ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.zeroSection (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).obj
            (P.coordinateTwist (Spec (.of P.field.k)) (r - (b : ℤ)))) ≫
    (P.coordinateDerivedModuleGlobalSections
      (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).map
        (θ (Spec (.of P.field.k)) (𝟙 _) r).hom ≫
    ((P.coordinateDerivedModuleGlobalSections
      (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).commShiftIso
        (2 * (b : ℤ))).hom.app
          ((Etale.coordinateSupportSheaf P.Coefficient
            (AffineSpace.zeroSection (ULift.{u} (Fin b))
              (Spec (.of P.field.k)))).rightDerivedFunctorPlus.obj
                ((P.coordinateSingle
                  (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).obj
                    (P.coordinateTwist
                      (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k))) r))) ≫
    ((P.coordinateDerivedGlobalSupportIso
      (AffineSpace.zeroSection (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).inv.app
        ((P.coordinateSingle (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k)))).obj
          (P.coordinateTwist (AffineSpace (ULift.{u} (Fin b)) (Spec (.of P.field.k))) r)))⟦
            2 * (b : ℤ)⟧'

/-- The ordinary finite-type coordinate support orientation, with its ordered
Cartier-Kummer normalization, all signed twists, every affine finite-type base
change, and the field comparison induced by this very orientation.
Source: Stacks 09XP--09XQ, and blueprint main-20261015,
cor-pur-affine-space-zero-section-purity, proof
(blueprint: lem-pur-finite-type-coordinate-support-orientation).

Proof:
1. On an affine base the zero section is the polynomial quotient by the coordinates.
   Its complement is the finite union of their basic opens. The two schemes are
   separated and finite type, including rank zero and empty bases.
2. Use etale_injective_support_sequence and the closed support adjunction to
   identify Q=z_*z^!_0 and its derived functor, retaining the kernel inclusion as
   counit. Underlying injective module sheaves are abelian-cohomology-acyclic on
   the scheme, complement and support. The support exact sequence is onto on
   sections, so these resolutions compute the prescribed abelian support functor.
3. Finite Tate-site descent and the counit-preserving closed-adjoint comparison
   identify the pro-etale inverse image of Rz^!_0(A(b))[2b]. Apply the normalized
   affine-space zero-section theorem. Bounded-below full faithfulness descends its
   isomorphism and inverse, and faithfulness makes their composites identities.
4. The counit transpose is the ordered Cartier-Kummer product: each factor is its
   ordinary etale witness, and supported-cup site comparison preserves the product.
   Faithfulness identifies the actual etale arrows. The empty product is the unit.
   cartier_kummer_map identifies the boundary at every annihilating ell-power
   with the same specified twist, independently of the exponent, even at ramified n.
5. The signed twist is pulled back from the algebraically closed field. Its fibre
   is a free rank-one A-module. Tensor the normalized b-twist orientation with this
   constant line. Tensor is exact and commutes with kernels and closed pushforward.
   Every generator gives the displayed tensor equation, so no basis is selected.
   Signed Tate multiplication and evaluation give the negative-power clauses.
6. Under an arbitrary base change the coordinates remain nonzerodivisors. Cartier
   boundaries and ordered cups pull back to the primed ones. Supported-Hom naturality
   and the closed adjunction identify this with the canonical supported pullback.
   Tensor with the same field line gives the square for every integer twist.
7. For Spec k the etale Galois group is trivial, hence evaluation is exact. Apply
   derived global sections to the same family, use the support/global comparison,
   and evaluate A(r-b) to its actual fibre L_(r-b). This is exactly the displayed
   coordinateFieldOrientation map, and it is invertible with the same normalization.
-/
theorem finiteTypeCoordinateSupportOrientation (P : PurityFiniteSetting.{u}) (b : ℕ) :
    ∃ θ : P.CoordinateOrientationFamily b,
      P.CoordinateOrientationNormalization b θ ∧
      P.CoordinateOrientationTensor b θ ∧
      P.CoordinateOrientationBaseChange b θ ∧
      ∀ r : ℤ, IsIso (P.coordinateFieldOrientation b θ r) := by
  sorry

end WeilConjectures.PurityFiniteSetting
