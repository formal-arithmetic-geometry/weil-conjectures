/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.PbcQbarCompletedPullback
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.FiniteStagePairCategory
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.Algebra.Homology.LocallyFreeDerivedHom
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.FiniteMittagLeffler
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.CategoryTheory.SiteCohomologyPullback
public import Sheaf.Paper.PbcScalarExtension
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Sheaf.AlgebraicGeometry.ContinuousEtaleCohomology
import Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.CartesianCoefficientsFiniteFree
import Sheaf.Paper.IntrinsicQbarCategory

/-!
# Finite-level comparison for constant algebraically closed l-adic coefficients

Source: current blueprint, Fourier transform, affine-line constant cohomology proof;
Milne, Lectures on Etale Cohomology, Section 19, pp. 123--126; Bhatt--Scholze,
Proposition 3.1.10 and Section 6.8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).

## Main definitions

* `finiteSheaf`, `tower`, `integralLimit`: the usual finite-coefficient inverse system.
* `integralUnit`, `unit`, `cohomology`: the completed regular unit and shifted pair Hom.
* `cohomologyPull`, `limitPull`: the actual pullback maps in the naturality square.
* `comparison`: the linear finite-level comparison, with naturality and constants.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.QbarFiniteLevel

variable (l : ℕ) [Fact l.Prime]

/-- The l-adic integers at the common site coefficient size. Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
abbrev Integral := ULift.{u + 1} ℤ_[l]

/-- The actual finite quotient ring map, with only universe lifts on its carriers.
Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def quotient (n : ℕ) : Integral.{u} l →+* ULift.{u + 1} (ZMod (l ^ (n + 1))) :=
  RingHom.ulift (PadicInt.toZModPow (n + 1))

/-- The regular finite coefficient module, restricted along the actual l-adic quotient.
Level n denotes exponent n+1. Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def coefficient (n : ℕ) : ModuleCat.{u + 1} (Integral.{u} l) :=
  (ModuleCat.restrictScalars (quotient.{u} l n)).obj
    (ModuleCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))
      (ULift.{u + 1} (ZMod (l ^ (n + 1)))))

/-- The usual quotient between consecutive finite coefficients, with l-adic scalars.
Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def coefficientStep (n : ℕ) : coefficient.{u} l (n + 1) ⟶ coefficient.{u} l n :=
  ConcreteCategory.ofHom (C := ModuleCat (Integral.{u} l))
    { toFun := fun x ↦ ULift.up (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
        (ZMod (l ^ (n + 1))) x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add _ x.down y.down)
      map_smul' := fun a x ↦ by
        apply congrArg ULift.up
        change (ZMod.castHom _ _)
          (PadicInt.toZModPow (n + 2) a.down * x.down) =
            PadicInt.toZModPow (n + 1) a.down * (ZMod.castHom _ _) x.down
        rw [map_mul]
        congr 1
        exact PadicInt.cast_toZModPow (n + 1) (n + 2) (Nat.le_succ _) a.down }

variable (X : Scheme.{u})

/-- Constant sheafification of the finite regular module on the small etale site.
Forgetting its scalar action gives the constant abelian sheaf Z/l^(n+1).
Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def finiteSheaf (n : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Integral.{u} l)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Integral.{u} l))).obj
    (coefficient.{u} l n)

/-- Ordinary right-derived etale cohomology of the actual finite constant sheaf.
Keeping its l-adic module structure makes all quotient transitions linear.
Source: Milne Section 19; def-weil-pbc-etale-cohomology
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def finiteCohomology (q n : ℕ) : ModuleCat.{u + 1} (Integral.{u} l) :=
  (Etale.cohomology (ModuleCat.{u + 1} (Integral.{u} l)) X (q : ℤ)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (finiteSheaf l X n))

/-- The inverse system uses the maps induced by F_(n+1) to F_n, not assumed surjective
on cohomology. Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def tower (q : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u + 1} (Integral.{u} l) :=
  Functor.ofOpSequence (X := finiteCohomology l X q) (fun n ↦
    (Etale.cohomology (ModuleCat.{u + 1} (Integral.{u} l)) X (q : ℤ)).map
      ((DerivedCategory.singleFunctor _ 0).map
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Integral.{u} l))).map
          (coefficientStep.{u} l n))))

/-- The ordinary inverse limit of finite-level etale cohomology, in l-adic modules.
Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def integralLimit (q : ℕ) : ModuleCat.{u + 1} (Integral.{u} l) := limit (tower l X q)

/-- H⁰ is identified with sections by the resolution augmentation.
Source: Milne Section 19; Stacks Tag 0156
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def h0Sections (n : ℕ) :
    finiteCohomology l X 0 n ≅
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} (Integral.{u} l))).obj
        (finiteSheaf l X n) :=
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso
    (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} (Integral.{u} l)))
    (finiteSheaf l X n) 0 ≪≫
    (Functor.rightDerivedZeroIsoSelf
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} (Integral.{u} l)))).app
        (finiteSheaf l X n)

/-- The actual finite constant-section map, using the unit of constant sheafification
and global sections and the degree-zero resolution augmentation.
Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def constantSection (n : ℕ) : coefficient.{u} l n ⟶ finiteCohomology l X 0 n :=
  (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} (Integral.{u} l))).unit.app
    (coefficient.{u} l n) ≫ (h0Sections l X n).inv

/-- Quotient of the integral regular coefficient into the finite regular module.
Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def scalarQuotient (n : ℕ) : ModuleCat.of (Integral.{u} l) (Integral.{u} l) ⟶
    coefficient.{u} l n :=
  ConcreteCategory.ofHom (C := ModuleCat (Integral.{u} l))
    { toFun := quotient.{u} l n
      map_add' := map_add _
      map_smul' := fun a b ↦ map_mul (quotient.{u} l n) a b }

/-- The finite constant-section maps commute with quotient transitions.
Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof: naturality of the constant/global-sections adjunction unit and of the
resolution-augmentation H⁰ comparison gives the square. The coefficient quotient
composites agree by PadicInt.zmod_cast_comp_toZModPow, including exponent one. -/
theorem constantSection_compatible (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (ModuleCat.of (Integral.{u} l) (Integral.{u} l))).map
        (homOfLE (Nat.le_succ n)).op ≫
      (scalarQuotient.{u} l n ≫ constantSection l X n) =
    (scalarQuotient.{u} l (n + 1) ≫ constantSection l X (n + 1)) ≫
      (tower l X 0).map (homOfLE (Nat.le_succ n)).op := by
  sorry

/-- The inverse limit of the actual finite constant-section maps.
Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def integralConstantSection : ModuleCat.of (Integral.{u} l) (Integral.{u} l) ⟶
    integralLimit l X 0 :=
  limit.lift (tower l X 0)
    { pt := ModuleCat.of (Integral.{u} l) (Integral.{u} l)
      π := NatTrans.ofOpSequence
        (fun n ↦ scalarQuotient.{u} l n ≫ constantSection l X n)
        (constantSection_compatible l X) }

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Integral scalars act on the fixed closure through Z_l into Q_l into the closure.
The only lift is removed by its canonical ring equivalence. Source: Milne Section 19
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
instance integralAlgebra : Algebra (Integral.{u} l) Ω :=
  ((algebraMap ℚ_[l] Ω).comp
    ((algebraMap ℤ_[l] ℚ_[l]).comp
      (ULift.ringEquiv : Integral.{u} l ≃+* ℤ_[l]).toRingHom)).toAlgebra

/-- The completed regular module, explicitly in degree zero, at a finite coefficient stage.
Source: Bhatt--Scholze Section 6.8; blueprint finite-level passage
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
abbrev regular (E : Padic.FiniteCoefficientFields l Ω) : pbcAmbientStage l Ω X E :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit ((adicLisseForget X).obj
      (pbcAdicCompletion X (pbcStageDatum.{u} l Ω E))))

variable [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The regular completed unit belongs to the integral full category.
Source: Bhatt--Scholze Lemma 6.8.2(1); blueprint finite-level passage, Step 1
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof: take the single stratum X and the perfect rank-one scalar complex O_E[0].
Its completed realization is the displayed regular module. Multiplication identifies
its normalized reduction with the finite constant regular module, all in degree zero.
The quotient transitions are surjective and their ordinary limit is the completed
ring itself, so the surjective-tower derived-limit calculation gives completeness.
The finite constant complexes on the etale site give compatible origin witnesses;
tensor multiplication gives their normalization and quotient cocycle. These are the
three clauses of PbcIsBoundedConstructibleComplete. Empty X is allowed. -/
theorem regular_mem (E : Padic.FiniteCoefficientFields l Ω) :
    PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E) (regular l X Ω E) := by
  sorry

/-- The integral full-subcategory unit has the explicitly constructed regular underlying
object; only its membership proof is postponed. Source: Bhatt--Scholze Lemma 6.8.2(1)
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def integralUnit (E : Padic.FiniteCoefficientFields l Ω) : pbcIntegralStage l Ω X E :=
  ⟨regular l X Ω E, regular_mem l X Ω E⟩

/-- The literal pair (Q_l, image of the completed regular unit), with no envelope.
Source: blueprint finite-level passage; def-weil-pbc-qbar-category
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def unit : pbcQbarCategory l Ω X :=
  ⟨Padic.finiteCoefficientBase l Ω,
    (pbcStageLocalization l Ω X (Padic.finiteCoefficientBase l Ω)).obj
      (integralUnit l X Ω (Padic.finiteCoefficientBase l Ω))⟩

/-- Ordinary adic cohomology is shifted Hom from the actual unit in the pair category.
Source: blueprint finite-level passage; Bhatt--Scholze Section 6.8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
abbrev cohomology (q : ℕ) := unit l X Ω ⟶ (unit l X Ω)⟦(q : ℤ)⟧

end AlgebraicGeometry.Scheme.QbarFiniteLevel

namespace AlgebraicGeometry.Scheme.QbarFiniteLevel

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]
  [IsAlgClosure ℚ_[l] Ω] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The regular coefficient module before placing it in degree zero.
Source: blueprint finite-level passage, Step 1
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
abbrev regularModule (T : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :=
  SheafOfModules.unit ((adicLisseForget T).obj
    (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E)))

/-- The coefficient-unit map R_Y to g_*R_X is the section 1, with the actual
completed coefficient structure map giving its scalar action.
Source: blueprint finite-level passage, Step 8; Stacks 03D2
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def regularToPush (E : Padic.FiniteCoefficientFields l Ω) :
    regularModule l Ω Y E ⟶
      (pbcActualModulePush g (pbcStageDatum.{u} l Ω E)).obj (regularModule l Ω X E) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : ((pbcActualCompletedRing (pbcStageDatum.{u} l Ω E) X).obj.obj
        ((proEtaleBaseChange g).op.obj U))))
      (fun {_ _} f ↦ by
        change ((pbcActualCompletedRing (pbcStageDatum.{u} l Ω E) X).obj.map
          ((proEtaleBaseChange g).op.map f)) 1 = 1
        exact map_one _))

/-- The canonical ordinary tensor-pullback unit map, adjoint to the constant section 1.
Source: blueprint finite-level passage, Step 8; Stacks 03D2
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def modulePullUnit (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcActualModulePull g (pbcStageDatum.{u} l Ω E)).obj (regularModule l Ω Y E) ⟶
      regularModule l Ω X E :=
  ((pbcActualModuleAdjunction g (pbcStageDatum.{u} l Ω E)).homEquiv _ _).symm
    (regularToPush l Ω g E)

/-- The ordinary derived pullback unit map, retaining the universal K-flat counit.
Source: blueprint finite-level passage, Step 8; Stacks 06YY
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def derivedPullUnit (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcActualDerivedPull g (pbcStageDatum.{u} l Ω E)).obj (regular l Y Ω E) ⟶
      regular l X Ω E :=
  pbcActualPullComplexCounit g (pbcStageDatum.{u} l Ω E)
      ((CochainComplex.singleFunctor _ 0).obj (regularModule l Ω Y E)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (pbcActualModulePull g (pbcStageDatum.{u} l Ω E)) (.up ℤ) 0).hom.app
          (regularModule l Ω Y E)) ≫
    (DerivedCategory.singleFunctor _ 0).map (modulePullUnit l Ω g E)

variable [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The completed-pullback unit is uniquely fixed by the ordinary tensor unit and
completion augmentation. No unspecified isomorphism of coefficient objects is chosen.
Source: blueprint finite-level passage, Steps 1 and 8; Bhatt--Scholze 6.8.2
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof: the regular module is K-flat and its ordinary pullback is the target regular
module by tensor multiplication. The displayed derived counit computes this map.
The target regular complex is intrinsically complete by regular_mem. The completion
reflection therefore extends the ordinary map uniquely across its augmentation.
Both complexes already identify with the completed regular target, so the extended
map is invertible. The reflection's bijection on Homs proves uniqueness. -/
theorem completedPullUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj
        (regular l Y Ω E) ≅ regular l X Ω E,
      (pbcActualCompletedPullUnit g (pbcStageDatum.{u} l Ω E)).app
          (regular l Y Ω E) ≫ e.hom = derivedPullUnit l Ω g E := by
  sorry

/-- The unique augmentation-normalized completed unit comparison.
Source: blueprint finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def completedPullUnit (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj (regular l Y Ω E) ≅
      regular l X Ω E :=
  (completedPullUnit_exists l Ω g E).exists.choose

/-- The canonical integral unit arrow in the full subcategory.
Source: blueprint finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def integralPullUnit (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E))
      (pbcQbarIntegralPull_mem l Ω g E)).obj (integralUnit l Y Ω E) ⟶
        integralUnit l X Ω E :=
  ObjectProperty.homMk (completedPullUnit l Ω g E).hom

/-- Pair-category unit comparison is the actual localized integral unit at the base
field. The heterogeneous equality only transports the functor-object equalities of
pbcQbarPullFamily_existsUnique; it fixes the arrow itself.
Source: blueprint finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof: localize integralPullUnit and its inverse and apply the stage inclusion at Q_l.
The pullback-family specification identifies the source object with the actual
common-stage pullback. Both equalities are the identities of raw localization on
objects, so this gives an isomorphism with exactly the displayed arrow. The arrow
is fixed, and an isomorphism is determined by its forward arrow, proving uniqueness. -/
theorem pairPullUnit_exists :
    ∃! e : (pbcQbarCompletedPull l Ω g).obj (unit l Y Ω) ≅ unit l X Ω,
      HEq e.hom
        ((pbcScalarSystem l Ω X dX.out iX.out).ι (Padic.finiteCoefficientBase l Ω) |>.map
          ((pbcStageLocalization l Ω X (Padic.finiteCoefficientBase l Ω)).map
            (integralPullUnit l Ω g (Padic.finiteCoefficientBase l Ω)))) := by
  sorry

/-- The canonical completed unit comparison in the actual Qbar pair category.
Source: blueprint finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def pairPullUnit : (pbcQbarCompletedPull l Ω g).obj (unit l Y Ω) ≅ unit l X Ω :=
  (pairPullUnit_exists l Ω g).exists.choose

/-- Shift on the integral pullback of the unit is the ambient completed-pullback shift.
Source: blueprint finite-level passage, Steps 6 and 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def integralPullShiftUnit (E : Padic.FiniteCoefficientFields l Ω) (q : ℕ) :
    (pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E))
      (pbcQbarIntegralPull_mem l Ω g E)).obj ((integralUnit l Y Ω E)⟦(q : ℤ)⟧) ⟶
    ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
      (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E))
      (pbcQbarIntegralPull_mem l Ω g E)).obj (integralUnit l Y Ω E))⟦(q : ℤ)⟧ :=
  letI := pbcIntegralTriangulated l (pbcFiniteField.{u} l Ω E) X dX.out iX.out
  letI := pbcIntegralTriangulated l (pbcFiniteField.{u} l Ω E) Y dY.out iY.out
  ObjectProperty.homMk
    ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).map
      (((pbcStageInclusion l Ω Y E).commShiftIso (q : ℤ)).hom.app
        (integralUnit l Y Ω E)) ≫
      ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).commShiftIso (q : ℤ)).hom.app
        (regular l Y Ω E) ≫
      ((pbcStageInclusion l Ω X E).commShiftIso (q : ℤ)).inv.app
        ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
          (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E))
          (pbcQbarIntegralPull_mem l Ω g E)).obj (integralUnit l Y Ω E)))

/-- The pair pullback shift on the unit is fixed by its actual integral representative.
Source: blueprint finite-level passage, Steps 6--8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof: the ambient completed pullback commutes with shifts. Its component and inverse
restrict to the full integral category, and localization and stage inclusion take them
to inverse arrows. The object equalities in the pullback-family specification identify
these arrows with the two displayed endpoints. The forward arrow determines the
isomorphism, so the prescribed representative also proves uniqueness. -/
theorem pairPullShiftUnit_exists (q : ℕ) :
    ∃! e : (pbcQbarCompletedPull l Ω g).obj ((unit l Y Ω)⟦(q : ℤ)⟧) ≅
        ((pbcQbarCompletedPull l Ω g).obj (unit l Y Ω))⟦(q : ℤ)⟧,
      HEq e.hom
        ((pbcScalarSystem l Ω X dX.out iX.out).ι (Padic.finiteCoefficientBase l Ω) |>.map
          ((pbcStageLocalization l Ω X (Padic.finiteCoefficientBase l Ω)).map
            (integralPullShiftUnit l Ω g (Padic.finiteCoefficientBase l Ω) q))) := by
  sorry

/-- The shift comparison determined by the localized ambient comparison.
Source: blueprint finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def pairPullShiftUnit (q : ℕ) :
    (pbcQbarCompletedPull l Ω g).obj ((unit l Y Ω)⟦(q : ℤ)⟧) ≅
      ((pbcQbarCompletedPull l Ω g).obj (unit l Y Ω))⟦(q : ℤ)⟧ :=
  (pairPullShiftUnit_exists l Ω g q).exists.choose

/-- Pull back a shifted unit Hom using the canonical completed pullback and its
specified unit and shift comparisons. Source: blueprint finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def cohomologyPull (q : ℕ) (h : cohomology l Y Ω q) : cohomology l X Ω q :=
  (pairPullUnit l Ω g).inv ≫ (pbcQbarCompletedPull l Ω g).map h ≫
    (pairPullShiftUnit l Ω g q).hom ≫
    (shiftFunctor _ (q : ℤ)).map (pairPullUnit l Ω g).hom

end AlgebraicGeometry.Scheme.QbarFiniteLevel

namespace AlgebraicGeometry.Scheme.QbarFiniteLevel
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The constant sheaf map to direct image is induced by the sheafification unit on
base-changed objects. Source: blueprint finite-level passage, Step 8; Stacks 03D2
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def finiteToPush (n : ℕ) : finiteSheaf l Y n ⟶
    (Etale.lowerStar (ModuleCat.{u + 1} (Integral.{u} l)) g).obj (finiteSheaf l X n) :=
  ((sheafificationAdjunction Y.smallEtaleTopology
    (ModuleCat.{u + 1} (Integral.{u} l))).homEquiv _ _).symm
    (Functor.whiskerLeft (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale
      (⊤ : MorphismProperty Scheme.{u}) g).op
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (coefficient.{u} l n))))

/-- The ordinary-to-derived direct-image augmentation on a finite sheaf, computed on
its degree-zero complex. Source: blueprint finite-level passage, Step 8; Stacks 03P2
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def finiteDerivedToPush (n : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (Integral.{u} l)) g).obj (finiteSheaf l X n)) ⟶
      (Etale.lowerStar (ModuleCat.{u + 1} (Integral.{u} l)) g).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (finiteSheaf l X n)) :=
  DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex
      (Etale.lowerStar (ModuleCat.{u + 1} (Integral.{u} l)) g) (.up ℤ) 0).inv.app
        (finiteSheaf l X n)) ≫
    (Etale.lowerStar (ModuleCat.{u + 1} (Integral.{u} l)) g).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj
        ((CochainComplex.singleFunctor _ 0).obj (finiteSheaf l X n)))

/-- The usual finite-level cohomology pullback: coefficient unit into derived direct
image, followed by Leray and degree-q homology. Source: Stacks 03P2;
blueprint finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def finitePull (q n : ℕ) : finiteCohomology l Y q n ⟶ finiteCohomology l X q n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Integral.{u} l)) (q : ℤ)).map
    ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} (Integral.{u} l)) Y).map
      ((DerivedCategory.singleFunctor _ 0).map (finiteToPush l g n) ≫
        finiteDerivedToPush l g n) ≫
      (Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} (Integral.{u} l)) g).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj (finiteSheaf l X n)))

/-- Finite coefficient reduction commutes with the canonical pullback.
Source: blueprint finite-level passage, Step 8; Stacks 03P2
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof: the sheafification unit is natural in its scalar module. Right-derived
augmentation and the Leray comparison are natural transformations. Apply this
naturality to the constant sheaf quotient and then degree-q homology. -/
theorem finitePull_compatible (q n : ℕ) :
    (tower l Y q).map (homOfLE (Nat.le_succ n)).op ≫ finitePull l g q n =
      finitePull l g q (n + 1) ≫
        (tower l X q).map (homOfLE (Nat.le_succ n)).op := by
  sorry

/-- The canonical morphism of finite-level cohomology towers.
Source: blueprint finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def towerPull (q : ℕ) : tower l Y q ⟶ tower l X q :=
  NatTrans.ofOpSequence (finitePull l g q) (finitePull_compatible l g q)

/-- Pullback on the inverse limit, induced by its actual finite-level maps.
Source: blueprint finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def limitPull (q : ℕ) : integralLimit l Y q ⟶ integralLimit l X q :=
  lim.map (towerPull l g q)

end AlgebraicGeometry.Scheme.QbarFiniteLevel

namespace AlgebraicGeometry.Scheme.QbarFiniteLevel

variable (K : Type u) [Field K]

/-- The separated finite-type K-schemes, with their usual K-morphisms. This merely
packages the schemes quantified over in the naturality clause, without choosing a
structure map or restricting to connected or nonempty schemes.
Source: blueprint finite-level passage
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def spacesProperty : ObjectProperty (Over (Spec (.of K))) := fun T ↦
  LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom ∧ IsSeparated T.hom

/-- The full category of separated finite-type K-schemes.
Source: blueprint finite-level passage
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
abbrev Space := (spacesProperty K).FullSubcategory

/-- Finite-type schemes over a field are noetherian.
Source: finite-level passage, Step 1; lem-cbc-compactification-geometry-fibre-bound
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof: Spec K is noetherian since K is a field. A finite-type morphism is
quasi-compact and locally noetherian over a noetherian base, so its source is
noetherian. These are precisely the first two defining properties of Space K. -/
theorem space_noetherian (T : Space K) : IsNoetherian T.obj.left := by
  sorry

/-- The noetherian structure follows from finite type and is not a new hypothesis.
Source: finite-level passage, Step 1
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
instance spaceNoetherian (T : Space K) : IsNoetherian T.obj.left := space_noetherian K T

/-- Finite type over Spec K bounds the dimension of the source.
Source: finite-level passage, Step 1; lem-cbc-compactification-geometry-fibre-bound
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof: a field has only the ideals zero and top, so its spectrum has dimension zero
and a one-member affine noetherian cover. Apply the recorded finite-type geometry
and fibre-bound theorem to the structure morphism T.hom. Its dimension clause is
exactly the asserted bound, also for the empty scheme. -/
theorem space_finiteDimension (T : Space K) :
    ∃ n : ℕ, topologicalKrullDim T.obj.left ≤ (n : WithBot ℕ∞) := by
  sorry

/-- The dimension bound is derived from finite type, not imposed separately.
Source: finite-level passage, Step 1
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
instance spaceDimension (T : Space K) :
    Fact (∃ n : ℕ, topologicalKrullDim T.obj.left ≤ (n : WithBot ℕ∞)) :=
  ⟨space_finiteDimension K T⟩

variable (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : K))]

/-- An invertible scalar in K remains invertible in every local ring over K.
Source: finite-level passage, Step 1; lem-cbc-compactification-geometry-fibre-bound
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof: pull the unit l in K along the structure morphism and then to each local
ring of T. Ring homomorphisms preserve units and natural-number casts. Equivalently
apply the scalar-invertibility clause of the finite-type geometry theorem. -/
theorem space_invertible (T : Space K) :
    ∀ x : T.obj.left, IsUnit (l : T.obj.left.presheaf.stalk x) := by
  sorry

/-- The required stalkwise invertibility is inherited from the given base field.
Source: finite-level passage, Step 1
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
instance spaceInvertible (T : Space K) :
    Fact (∀ x : T.obj.left, IsUnit (l : T.obj.left.presheaf.stalk x)) :=
  ⟨space_invertible K l T⟩

variable (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The identity regarded as a degree-zero shifted Hom, through the specified zero
shift comparison of the actual pair category. Source: finite-level passage, Step 8
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison). -/
def identitySection (T : Space K) : cohomology l T.obj.left Ω 0 :=
  (shiftFunctorZero (pbcQbarCategory l Ω T.obj.left) ℤ).inv.app (unit l T.obj.left Ω)

/-- Ordinary adic constant-coefficient cohomology is the finite-level inverse limit
extended to the fixed algebraic closure, naturally in the separated finite-type
K-scheme and compatibly with every constant section.
Source: Milne, Lectures on Etale Cohomology, Section 19, pp. 123--126;
Bhatt--Scholze Proposition 3.1.10 and Section 6.8; Stacks Tag 07KY;
current blueprint Fourier transform, affine-line constant cohomology proof
(blueprint: lem-fd-qbar-cohomology-finite-level-comparison).
Proof:
1. Finite type over a field gives noetherianity, finite dimension and stalkwise
invertibility. The sheafified continuous functions with finite discrete values equal
the constant finite sheaf: locally on a quasi-compact affine, its finitely many open
fibres form a cover on which it is constant. The finite-level maps respect scalars
and quotients. The integral coefficient limit is consequently the stated A_X. The
regular complex belongs to the integral category by the single-stratum perfect
rank-one realization (integralStratifiedPerfectCharacterization).
2. Pull back the finite sheaves through the etale/pro-etale comparison. Their quotient
maps are epimorphic locally by lifting a scalar. The continuous-cohomology derived
limit theorem identifies RΓ(A_X) with the derived limit of their RΓ. The finite-ring
comparison identifies this with the actual etale tower. The Milnor sequence gives
zero to R¹lim H^(q-1) to H^q RΓ(A_X) to lim H^q to zero.
3. Finite groups satisfy Mittag--Leffler: the descending images in any fixed finite
group stabilize. Thus R¹lim vanishes. For q=0 the preceding groups are H^(-1) of a
right-derived functor on a degree-zero object, hence zero. The projection-induced
comparison is an integral-linear isomorphism in every stated degree.
4. The module/abelian evaluation comparison and locally-free derived Hom identify
Hom from the regular rank-one unit to its q-shift with H^q RΓ(A_X). Fullness of the
integral category preserves this Hom. Evaluation at 1 sends the identity to 1.
5. Choose a finite integral basis of O_E. Its basis-induced coefficient-sheaf map
identifies S_E with a finite direct sum of copies of A_X. Sections, injective
resolutions and cohomology commute with this finite sum, so the canonical bilinear
map M_q tensor O_E to H^q RΓ(S_E) is an isomorphism. Its formula h tensor b maps to
the class induced by a maps to ab, independent of the basis and compatible with
all inclusions E into F (cartesian-coefficients-finite-free and integral-basis nodes).
6. Raw rationalization is localization of the integral Hom modules. Tensor balancing
therefore identifies the rational unit Hom at E with M_q tensor E. Scalar extension
sends the regular unit to the regular unit by tensor multiplication and respects
shifts. The finite-stage transition maps are the evident coefficient inclusions.
7. The pair-category Hom is the directed colimit of these finite-stage Homs. Each
tensor uses finitely many algebraic scalars, hence lies in one finite field; each
tensor equality involves finitely many balancing relations and holds in a finite
overfield. Thus this colimit is M_q tensor Ω, with precisely its specified Ω-action.
Compose with Step 3 and tensor symmetry to obtain the displayed Ω-linear equivalence.
8. Project a constant section to each finite quotient. Each comparison sends it to
the same scalar section, and Step 4 sends the regular identity to 1. Tensor balancing
then gives the constant-section equation for every integral a and algebraic b.
For a K-morphism, the coefficient maps and site-comparison pullbacks commute with
finite reduction. The derived units, Leray and limit projections are natural; the
basis-free maps a maps to ab also commute with pullback. Localization, its specified
shift maps and the pair-category transition coherences preserve these squares.
This yields the displayed naturality equation for the actual canonical maps. -/
theorem comparison [IsAlgClosed K] :
    ∃ e : ∀ (T : Space K)
      (_ : ∀ j n : ℕ, Finite (finiteCohomology l T.obj.left j n)) (q : ℕ),
        cohomology l T.obj.left Ω q ≃ₗ[Ω]
          Ω ⊗[Integral.{u} l] integralLimit l T.obj.left q,
      (∀ (T : Space K)
        (hfin : ∀ j n : ℕ, Finite (finiteCohomology l T.obj.left j n))
        (a : Integral.{u} l) (b : Ω),
        e T hfin 0 ((algebraMap (Integral.{u} l) Ω a * b) • identitySection K l Ω T) =
          b ⊗ₜ[Integral.{u} l] (integralConstantSection l T.obj.left).hom a) ∧
      (∀ (T S : Space K)
        (hT : ∀ j n : ℕ, Finite (finiteCohomology l T.obj.left j n))
        (hS : ∀ j n : ℕ, Finite (finiteCohomology l S.obj.left j n))
        (g : T ⟶ S) (q : ℕ) (h : cohomology l S.obj.left Ω q),
        e T hT q (cohomologyPull l Ω g.hom.left q h) =
          TensorProduct.map (LinearMap.id : Ω →ₗ[Integral.{u} l] Ω)
            (limitPull l g.hom.left q).hom (e S hS q h)) := by
  sorry

end AlgebraicGeometry.Scheme.QbarFiniteLevel
