/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenComparison
import WeilConjectures.AlgebraicGeometry.PointScalarSectionsExact
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.CondensedFibresExact

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.QuasiFinite.Basic
import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed

/-! # Condensed finite-fibre evaluation and Frobenius orbits

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/
lem-zl-finite-pushforward.proof.md, Exactness and stalks and the Frobenius-orbit sentences
(blueprint: lem-zl-condensed-finite-fibre-evaluation).

The derived comparison is characterized on H⁰ by the actual restriction of sections.
The geometric cycle and the local return use the semilinear point convention, even
when the module is zero. No reducedness, purity or semisimplicity is imposed.

## Main definitions

`Evaluation` records the canonical finite sum and derived comparison.
`Frobenius` records the geometric cycles and their specified local returns.
`Naturality` records functoriality for module maps and semilinear diagrams.

## Main statements

`condensed_finite_fibre_evaluation` asserts these comparisons and compatibilities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum

namespace WeilConjectures.CondensedFiniteEvaluation

attribute [local irreducible] CondensedModule.transport CondensedModule.operator

/-- Restrict a section by pulling back its map from the regular coefficient module.
Source: latest blueprint, natural evaluation
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def restrict (l : ℕ) [Fact l.Prime] {U V : Scheme.{u}} (f : U ⟶ V)
    (M : CondensedModule.Modules l V)
    (v : (CondensedRing.condensedCoefficientSections l V).obj M) :
    (CondensedRing.condensedCoefficientSections l U).obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M) :=
  (Functor.Monoidal.εIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)).hom ≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).map v

/-- Expose the existing additive instance of the represented section functor.
Source: latest blueprint, ordinary module sections
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
instance sectionsAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (CondensedRing.condensedCoefficientSections l T).Additive := by
  dsimp [CondensedRing.condensedCoefficientSections, coyonedaSections]
  infer_instance

/-- Expose left exactness of the existing represented section functor.
Source: latest blueprint, degree-zero normalization of RΓ
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
instance sectionsFiniteLimits (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    PreservesFiniteLimits (CondensedRing.condensedCoefficientSections l T) := by
  refine ⟨fun J _ _ => ?_⟩
  have : PreservesLimitsOfShape J
      ((CondensedRing.condensedCoefficientSections l T) ⋙
        forget₂ (ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l)) Ab.{u + 1}) :=
    inferInstanceAs (PreservesLimitsOfShape J
      (preadditiveCoyonedaObj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T)) ⋙
          forget₂ _ Ab.{u + 1}))
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l)) Ab.{u + 1})

variable (D : FiniteFieldDatum.{u}) (T₀ : Over (Spec (.of D.k₀))) [IsFinite T₀.hom]
  (l : ℕ) [Fact l.Prime]

/-- The k-points of the specified geometric base change.
Source: latest blueprint, finite geometric fibre
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
abbrev Points := (D.geometricFiber T₀).hom.GeometricFiber (𝟙 (Spec (.of D.k)))

/-- Points above the given closed point of the arithmetic model.
Source: latest blueprint, Frobenius orbit block P_x
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
abbrev Block (x : closedPoints T₀.left) :=
  {z : Points D T₀ //
    (z.val ≫ pullback.fst T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        (IsLocalRing.closedPoint D.k) = x.val}

/-- The existing point fibre with its recorded scalar category exposed.
Source: latest blueprint, the vector space F_z
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
abbrev Fibre (M : CondensedModule.Modules l (D.geometricFiber T₀).left)
    (z : Points D T₀) : ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l) :=
  CondensedModule.fibre l D M z.val

/-- The direct sum in one closed-point block.
Source: latest blueprint, the summands indexed by P_x
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def BlockSum (M : CondensedModule.Modules l (D.geometricFiber T₀).left)
    (x : closedPoints T₀.left) : ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l) :=
  ModuleCat.of _ (⨁ z : Block D T₀ x, Fibre D T₀ l M z.val)

/-- The finite double direct sum of the actual point-pullback sections.
Source: latest blueprint, evaluation display
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def Sum (M : CondensedModule.Modules l (D.geometricFiber T₀).left) :
    ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l) :=
  ModuleCat.of _ (⨁ x : closedPoints T₀.left, BlockSum D T₀ l M x)

/-- The canonical coordinate projection from the double direct sum.
Source: latest blueprint, the evaluation component e_z
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def project (M : CondensedModule.Modules l (D.geometricFiber T₀).left)
    (x : closedPoints T₀.left) (z : Block D T₀ x) :
    Sum D T₀ l M ⟶ Fibre D T₀ l M z.val :=
  ModuleCat.ofHom (X := Sum D T₀ l M) (Y := Fibre D T₀ l M z.val)
    ((DirectSum.component (CondensedRing.CohomologyScalar.{u} l) (Block D T₀ x)
      (fun w => Fibre D T₀ l M w.val) z).comp
      (DirectSum.component (CondensedRing.CohomologyScalar.{u} l) (closedPoints T₀.left)
        (fun y => BlockSum D T₀ l M y) x))

/-- RΓ is total right derivation of the existing global-section functor.
Source: latest blueprint, derived evaluation; det-def-sfb-derived-categories
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
abbrev sectionsComplex :=
  (CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left).rightDerivedFunctor

/-- The canonical H⁰(RΓ(M[0])) = Γ(M) comparison for the left exact section functor.
Source: latest blueprint, exactness and stalks
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def h0 (M : CondensedModule.Modules l (D.geometricFiber T₀).left) :=
  (Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso
    (CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left)).app M

/-- The standard degree-zero embedding of ordinary coefficient modules.
Source: latest blueprint, the notation F_z[0] in D(Omega)
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def coefficientSingle :=
  DerivedCategory.singleFunctor (ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l)) 0

/-- Derived sections applied to degree-zero native modules.
Source: latest blueprint, RΓ(T,F) for a degree-zero coefficient module
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def derivedOnModules :=
  DerivedCategory.singleFunctor (CondensedModule.Modules l (D.geometricFiber T₀).left) 0 ⋙
    sectionsComplex D T₀ l

/-- Ordinary sections placed in degree zero, using the existing single functor.
Source: latest blueprint, exact finite-scheme evaluation
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def sectionsInDegreeZero :=
  CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left ⋙
    coefficientSingle l

/-- The complete geometric and derived evaluation assertion, including its canonical maps.
Source: latest blueprint, Exactness and stalks and natural Frobenius return
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
structure Evaluation where
  finite_closed : Finite (closedPoints T₀.left)
  finite_points (x : closedPoints T₀.left) : Finite (Block D T₀ x)
  cardinality (x : closedPoints T₀.left) :
    Nat.card (Block D T₀ x) = T₀.hom.degreeOver x.val
  finite_fibre
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (z : Points D T₀) :
    FiniteDimensional (CondensedRing.CohomologyScalar.{u} l) (Fibre D T₀ l M.obj z)
  evaluation
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left) :
    (CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left).obj M.obj ≃ₗ[
      CondensedRing.CohomologyScalar.{u} l] Sum D T₀ l M.obj
  evaluation_component
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (v : (CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left).obj M.obj)
      (x : closedPoints T₀.left) (z : Block D T₀ x) :
    project D T₀ l M.obj x z ((evaluation M) v) =
      restrict l z.val.val M.obj v
  derived
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left) :
    (derivedOnModules D T₀ l).obj M.obj ≅
      (coefficientSingle l).obj (Sum D T₀ l M.obj)
  derived_component
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (v : (DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l)) 0).obj
        ((derivedOnModules D T₀ l).obj M.obj))
      (x : closedPoints T₀.left) (z : Block D T₀ x) :
    project D T₀ l M.obj x z
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l)) 0).hom.app
          (Sum D T₀ l M.obj)
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l)) 0).map
          (derived M).hom v)) =
      restrict l z.val.val M.obj ((h0 D T₀ l M.obj).hom v)
  naturality
      (M N : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (f : M ⟶ N)
      (v : (CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left).obj M.obj)
      (x : closedPoints T₀.left) (z : Block D T₀ x) :
    project D T₀ l N.obj x z ((evaluation N)
      ((CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left).map f.hom v)) =
      (CondensedRing.pointSections l D.k).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z.val.val).map f.hom)
          (project D T₀ l M.obj x z ((evaluation M) v))

/-- The evaluation component as a linear map, with the actual restriction formula supplied
by Evaluation.evaluation_component. Source: latest blueprint, e_z
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
@[irreducible] def Evaluation.component (E : Evaluation D T₀ l)
    (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
    (x : closedPoints T₀.left) (z : Block D T₀ x) :
    (CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left).obj M.obj ⟶
      Fibre D T₀ l M.obj z.val :=
  (E.evaluation M).toModuleIso.hom ≫ project D T₀ l M.obj x z

/-- Cancel the evaluated direct sum to obtain the canonical degree-zero normalization.
Source: latest blueprint, exact derived evaluation
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
@[irreducible] def Evaluation.normalization (E : Evaluation D T₀ l)
    (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left) :
    (derivedOnModules D T₀ l).obj M.obj ≅
      (sectionsInDegreeZero D T₀ l).obj M.obj :=
  E.derived M ≪≫
    (coefficientSingle l).mapIso (E.evaluation M).toModuleIso.symm

/-- The Frobenius action, with its geometric point cycle and its specified local return.
The derived action is uniquely characterized by its canonical H⁰ normalization: the
finite evaluation isomorphism places the entire derived object in degree zero.
Source: latest blueprint, Frobenius-orbit and return-operator sentences
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
structure Frobenius (E : Evaluation D T₀ l) where
  cycle (x : closedPoints T₀.left) : Equiv.Perm (Block D T₀ x)
  cycle_transitive (x : closedPoints T₀.left) (z z' : Block D T₀ x) :
    ∃! j : Fin (T₀.hom.degreeOver x.val), (cycle x ^ j.val) z = z'
  cycle_step (x : closedPoints T₀.left) (z : Block D T₀ x) :
    z.val.val ≫ (D.geometricFrobenius T₀).hom =
      (frobeniusPointIso D).hom ≫ (cycle x z).val.val
  local_return (x : closedPoints T₀.left) (z : Block D T₀ x) :
    z.val.val ≫ localPositivePower (D.geometricFrobenius T₀).hom
        (T₀.hom.degreeOver x.val - 1) =
      localPositivePower (frobeniusPointIso D).hom (T₀.hom.degreeOver x.val - 1) ≫ z.val.val
  global
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius T₀).hom).obj M.obj ≅ M.obj) :
    Aut ((CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left).obj M.obj)
  global_formula
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius T₀).hom).obj M.obj ≅ M.obj)
      (v : (CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left).obj M.obj) :
    (global M θ).hom v = restrict l (D.geometricFrobenius T₀).hom M.obj v ≫ θ.hom
  cycle_action
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius T₀).hom).obj M.obj ≅ M.obj)
      (x : closedPoints T₀.left) (z : Block D T₀ x) :
    CommSq (global M θ).hom (E.component D T₀ l M x (cycle x z))
      (E.component D T₀ l M x z)
      (CondensedModule.transport l D (D.geometricFrobenius T₀).hom M.obj θ
        z.val.val (cycle x z).val.val 0 (cycle_step x z)).hom
  power_return
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius T₀).hom).obj M.obj ≅ M.obj)
      (x : closedPoints T₀.left) (z : Block D T₀ x) :
    CommSq ((global M θ) ^ (T₀.hom.degreeOver x.val)).hom
      (E.component D T₀ l M x z) (E.component D T₀ l M x z)
      (CondensedModule.operator l D (D.geometricFrobenius T₀).hom M.obj θ z.val.val
        (T₀.hom.degreeOver x.val - 1) (local_return x z))
  derivedAction
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius T₀).hom).obj M.obj ≅ M.obj) :
    Aut ((derivedOnModules D T₀ l).obj M.obj)
  derivedFormula
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius T₀).hom).obj M.obj ≅ M.obj) :
    CommSq
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (CondensedRing.CohomologyScalar.{u} l)) 0).map
          (derivedAction M θ).hom)
      (h0 D T₀ l M.obj).hom (h0 D T₀ l M.obj).hom (global M θ).hom

/-- Canonical comparison for point pullbacks around a commuting scheme square.
Source: latest blueprint, naturality for semilinear finite-scheme diagrams
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def diagramComparison (l : ℕ) [Fact l.Prime] {S' S T' T : Scheme.{u}}
    (a : T' ⟶ T) (b : S' ⟶ S) (z' : S' ⟶ T') (z : S ⟶ T)
    (h : z' ≫ a = b ≫ z) (M : CondensedModule.Modules l T) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z').obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M) ≅
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b).obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M) :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z' a).symm.app M ≪≫
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h).app M ≪≫
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) b z).app M

/-- Evaluation commutes with the canonical comparison around a scheme square.
Source: latest blueprint, component form of naturality under field reparametrization
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def diagramEvaluation (l : ℕ) [Fact l.Prime] {S' S T' T : Scheme.{u}}
    (a : T' ⟶ T) (b : S' ⟶ S) (z' : S' ⟶ T') (z : S ⟶ T)
    (h : z' ≫ a = b ≫ z) (M : CondensedModule.Modules l T)
    (v : (CondensedRing.condensedCoefficientSections l T).obj M) : Prop :=
  CommSq (𝟙 _)
    (restrict l z' ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M)
      (restrict l a M v))
    (restrict l b ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)
      (restrict l z M v))
    (diagramComparison l a b z' z h M).hom

set_option maxHeartbeats 600000 in
-- The coherent pullback comparison has large concrete module-object types.
/-- Naturality of the canonical evaluation, at both the derived and diagram levels.
The component equation uses actual inverse-image composition and unit comparisons;
a field isomorphism is allowed in the lower horizontal side of the diagram.
Source: latest blueprint, natural evaluation and point-transport coherence
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
structure Naturality (E : Evaluation D T₀ l) : Prop where
  derived
      (M N : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (f : M ⟶ N) :
    CommSq
      ((derivedOnModules D T₀ l).map f.hom)
      (E.normalization D T₀ l M).hom (E.normalization D T₀ l N).hom
      ((sectionsInDegreeZero D T₀ l).map f.hom)
  diagram (D' : FiniteFieldDatum.{u})
      (T₀' : Over (Spec (.of D'.k₀))) [IsFinite T₀'.hom]
      (a : (D'.geometricFiber T₀').left ≅ (D.geometricFiber T₀).left)
      (b : Spec (.of D'.k) ≅ Spec (.of D.k))
      (_sq : CommSq a.hom (D'.geometricFiber T₀').hom (D.geometricFiber T₀).hom b.hom)
      (z' : Points D' T₀') (z : Points D T₀)
      (h : z'.val ≫ a.hom = b.hom ≫ z.val)
      (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left)
      (v : (CondensedRing.condensedCoefficientSections l (D.geometricFiber T₀).left).obj M.obj) :
    diagramEvaluation l a.hom b.hom z'.val z.val h M.obj v

/-- Canonical derived evaluation on a finite geometric scheme, with Frobenius cycles.
Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/
lem-zl-finite-pushforward.proof.md, Exactness and stalks, Frobenius orbits and return maps
(blueprint: lem-zl-condensed-finite-fibre-evaluation).

Proof in words:
1. Finite over a field is affine with finite-dimensional coordinate algebra. Its spectrum
is finite with all points closed, and its residue fields are finite extensions.
2. Base change gives B₀ tensor k. Its reduction is a finite product of k: residue fields
are k by algebraic closedness, and the Chinese remainder theorem applies to its finitely
many pairwise comaximal maximal ideals. Thus the reduction is a disjoint union of points.
3. Its reduction immersion is a surjective closed immersion, hence a universal
homeomorphism. Pro-etale topological invariance and cartesian coefficients identify module
sections with sections on this reduction, through the canonical adjunction restriction.
4. The finite disjoint-cover sheaf axiom identifies these sections with the product of
point restrictions. Module pullback composition identifies each with the stated z^*M.
This is the actual evaluation map and respects the constant Omega action; the empty cover
has zero module sections. Finite products identify canonically with finite direct sums.
5. Point pullback and point sections are exact. Hence finite evaluation makes sections
on T exact. Total right derivation is termwise sections, so the same evaluation is an
isomorphism in D(Omega), normalized on H⁰ by the displayed restriction maps.
6. Constructibility makes each point fibre finite dimensional. The geometric points over
x are the embeddings of its finite residue field into k. Finite-field Galois theory makes
these a torsor for the d distinct q-power automorphisms. Consequently their number is d.
7. Put h=Spec(gamma), g=id times h. The permutation tau(z)=h⁻¹ z g changes the embedding
by q-power Frobenius, so every block is one d-cycle and z g^d=h^d z.
8. Restriction naturality and the coherent pullback comparisons give
 e_z F=A_z e_tau(z), where A_z is precisely CondensedModule.transport with one iterate.
The global operator is restriction along g followed by theta. It is invertible.
The degree-zero derived comparison gives its unique lift to an automorphism of RΓ;
its H⁰ normalization is exactly derivedFormula.
9. Iterate that equation d times. The point returns to z, and the coherent product of
the d transports is exactly CondensedModule.operator, defined by d Weil iterates and the
single point reparametrization h^d. This gives e_z F^d=F_x,z e_z, without semisimplicity.
10. For module maps, evaluation commutes with pullback and sections. For a diagram with
a field isomorphism, both composites restrict along the same scheme map. The inverse-image
unit and composition coherences give the stated diagram equation, preserving scalars.
The H⁰-normalized derived comparison inherits these equations, since both complexes lie
in degree zero. This proves naturality and includes semilinear diagrams. -/
theorem condensed_finite_fibre_evaluation (hl : l ≠ D.p) :
    ∃ E : Evaluation D T₀ l, Nonempty (Frobenius D T₀ l E) ∧ Naturality D T₀ l E := by
  sorry

end WeilConjectures.CondensedFiniteEvaluation
