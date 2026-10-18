/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.CompletedDerivedInverseLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.CategoryTheory.KInjectiveBridge
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.Triangulated.DerivedLimitTower
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.KInjectiveBridge
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTower

/-!
# The derived inverse-limit functor on strict completed-coefficient towers

Source: blueprint, proper base change, proposition Rlim functoriality;
Stacks Tags 079P and 08TC (blueprint: prop-weil-pbc-rlim-functoriality).

## Main statements

- `AlgebraicGeometry.Scheme.completedRlim_computation`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [instance] reductionTower_isGrothendieckAbelian

/-- The ordinary inverse limit of strict towers, with its canonical limit maps.
Source: blueprint Rlim functoriality; Stacks Tag 079P
(blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedTowerLimit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    reductionTowerCategory T (reductionModuleRing T R) ⥤ reductionModules T R :=
  lim

/-- Inverse limit is additive because it is a right adjoint and preserves binary products.
Source: blueprint Rlim functoriality (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance coherenceTowerLimit_additive (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (completedTowerLimit T R).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Rlim is the total right derived functor of the actual strict inverse-limit functor.
Its universal unit, not a choice of triangulated cones, determines its action on maps.
Source: blueprint Rlim functoriality; Stacks Tag 079P
(blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedRlim (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    DerivedCategory (reductionTowerCategory T (reductionModuleRing T R)) ⥤
      reductionDerivedCategory T R :=
  (completedTowerLimit T R).rightDerivedFunctor

/-- The universal comparison to the K-injective computation of Rlim.
Source: blueprint Rlim functoriality; Stacks Tag 079P
(blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedRlimUnit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  (completedTowerLimit T R).rightDerivedFunctorUnit

/-- Rlim is computed by inverse limits of K-injective tower resolutions. It is
triangulated, and its universal derived pair identifies all resolution choices.
Source: blueprint proposition Rlim functoriality; Stacks Tags 079P and 08TC.
Proof: strict towers are Grothendieck abelian by the adic coefficient datum, hence have
functorial K-injective resolutions. The K-injective derivability structure constructs
the total right derived functor of inverse limit. Its unit is invertible on K-injectives,
and the derived functor is triangulated. The universal property gives a unique compatible
isomorphism between any two derived pairs; these are the resolution-choice comparisons.
(blueprint: prop-weil-pbc-rlim-functoriality). -/
theorem completedRlim_computation (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (J : CochainComplex (reductionTowerCategory T (reductionModuleRing T R)) ℤ)
    [J.IsKInjective] :
    IsIso ((completedRlimUnit T R).app ((HomotopyCategory.quotient _ _).obj J)) := by
  sorry

/-- The canonical derived projection is obtained by deriving the actual limit projection.
Source: blueprint Rlim functoriality and its K-injective construction; Stacks 079P
(blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedRlimProjection (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) (n : ℕ) :
    completedRlim T R ⟶
      reductionTowerDerivedEvaluation T (reductionModuleRing T R) n :=
  Functor.rightDerivedFunctorNatTrans (lim.π (op n)) ≫
    (Functor.rightDerivedFunctorIsoMapDerivedCategory
      (reductionTowerEvaluation T (reductionModuleRing T R) n)).hom

/-- The actual derived inverse-limit functor is triangulated and independent of the
K-injective resolution choice through its universal derived pair.
Source: blueprint Rlim functoriality, all clauses; Stacks Tags 079P and 08TC
(blueprint: prop-weil-pbc-rlim-functoriality).
Proof: the category of strict towers is Grothendieck abelian and has functorial
K-injective resolutions. Applying inverse limit to them defines the stated universal
right-derived pair and its shift and triangle structure. For any other resolution
choice its universal pair is right derived for the same functor. Uniqueness of right
derived pairs gives a natural isomorphism, compatible with both units. -/
theorem completedRlim_properties (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    (∃ (_ : (completedRlim T R).CommShift ℤ), (completedRlim T R).IsTriangulated) ∧
      ∀ (RF : DerivedCategory (reductionTowerCategory T (reductionModuleRing T R)) ⥤
          reductionDerivedCategory T R)
        (η : (completedTowerLimit T R).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF),
        RF.IsRightDerivedFunctor η
            (HomotopyCategory.quasiIso
              (reductionTowerCategory T (reductionModuleRing T R)) (.up ℤ)) →
          Nonempty (completedRlim T R ≅ RF) := by
  sorry

/-- The first Roos arrow is the product of the actual derived limit projections.
Source: blueprint Rlim functoriality and derived inverse limit; Stacks 07KC and 08TC
(blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedRlimRoosProjection (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T d))))
    [HasProduct (completedTowerDerivedSequence T d M)] :
    (completedRlim T (completedReductionCoefficient T d)).obj M ⟶
      ∏ᶜ (completedTowerDerivedSequence T d M) :=
  Pi.lift (fun n ↦ (completedRlimProjection T (completedReductionCoefficient T d) n).app M)

/-- The K-injective computation of Rlim gives the distinguished Roos triangle with
its specified projections, rather than a cone map chosen in a triangulated category.
Source: blueprint Rlim functoriality and derived inverse limit; Stacks 07KC and 08TC
(blueprint: prop-weil-pbc-rlim-functoriality).
Proof: represent the strict tower by a K-injective tower complex. The standard Roos
sequence computes its inverse limit; the first map is its family of actual projections.
Countable products of these module sheaves are exact, so termwise products compute
products in the derived category. Localization of the Roos sequence gives the
asserted triangle. The universal right-derived unit identifies its first object and
projections with completedRlim and completedRlimProjection. -/
theorem completedRlim_roos (T : Scheme.{t})
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T d))))
    [HasProduct (completedTowerDerivedSequence T d M)] :
    ∃ δ : ∏ᶜ (completedTowerDerivedSequence T d M) ⟶
        ((completedRlim T (completedReductionCoefficient T d)).obj M)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (completedTowerDerivedStep T d M)
        ((completedRlim T (completedReductionCoefficient T d)).obj M)
        (completedRlimRoosProjection T d M) δ := by
  sorry

end AlgebraicGeometry.Scheme
