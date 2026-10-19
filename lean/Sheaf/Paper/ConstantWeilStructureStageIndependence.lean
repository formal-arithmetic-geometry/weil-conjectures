/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.ConstantCoefficientScalarNormalization
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.PurInverseImageTensorHom
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Stage independence of the canonical constant Weil structure

Source: blueprint, ordinary compact cohomology, order 1869, coefficient-object paragraph
(blueprint: lem-weil-constant-weil-structure-stage-independence).
The finite-stage comparison is the rationalized, strict-cone-normalized coefficient-unit
map. At algebraically closed coefficients its class is taken at the larger finite stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Endofunctor
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The pullback/scalar comparison for the actual geometric Frobenius.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence). -/
def constantWeilScalarPullbackComparison :=
  @rationalPullbackScalarComparison l _ E _ _ _ L _ _ _ ι _ _
    (D.geometricFrobenius Y₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)

/-- Scalar extension of the specified constant Weil pair. Its structure is scalar theta_E
composed with the inverse pullback/scalar comparison, as in the node's source convention.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence). -/
def constantWeilScalarComplex : sfWeilComplex D l hl Y₀ L :=
  IsoAlgebra.mk
    ((sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
        (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left))
    ((constantWeilScalarPullbackComparison D l hl Y₀ E L ι).symm.app
        (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left) ≪≫
      (sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).mapIso
          (constantWeilRationalTheta l E D hl Y₀))

/-- The scalar constant carrier is in the constructible heart.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence).
Proof: the normalized alpha identifies this carrier with L_Y, which is in the heart by
constantWeilRationalObject_mem_heart. Both standard classes are closed under isomorphisms
by their definitions, so their intersection is too. -/
theorem constantWeilScalar_mem_heart :
    sfRationalHeartProperty l L (D.geometricFiber Y₀).left
      (constantWeilScalarComplex D l hl Y₀ E L ι).carrier := by
  sorry

/-- The extended canonical constant as a constructible L-Weil sheaf.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence). -/
def constantWeilScalarSheaf : sfWeilSheaf D l hl Y₀ L :=
  ⟨constantWeilScalarComplex D l hl Y₀ E L ι,
    constantWeilScalar_mem_heart D l hl Y₀ E L ι⟩

/-- Clause 1: the normalized alpha intertwines the canonical Weil structures and is the
underlying arrow of an isomorphism of Weil pairs.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence).
Proof: write R and S for the two completed coefficient rings and F for g inverse image.
1. Exact inverse image along the scheme isomorphism preserves limits; its constant-ring
comparisons commute with all quotient projections (proetale-isomorphism-inverse-image).
2. Naturality for each coefficient inclusion gives rho_m c_R=c_B F(rho_m). Joint monicity
of the limit projections gives c_S F(j)=j c_R, also for ramified coefficient extensions.
3. The regular module itself is K-flat. Multiplication R tensor_R S -> S and its inverse
s -> 1 tensor s identify the canonical scalar comparison; the strict cone inverse has
coordinates pi_m(s) and zero shifted component (finite-free-completed-scalar-comparison).
4. At finite level the pullback unit is multiplication after the constant-ring comparison.
The integral pullback unit has those same quotient coordinates and zero shifted component;
the surjective-tower theorem identifies it with the specified theta, without a cone choice.
5. The tensor comparison sends pure tensors to pure tensors. The square is the equality
c_S(Fj(x)y)=j(c_R(x))c_S(y). It descends through sheafification and commutes with reductions.
6. The normalized integral pullback/scalar comparison is the same square on the strict
products and both cone components (integral-operations-scalar-extension). Thus beta is
integrally equivariant. This uses actual cone maps, not detection of arbitrary derived
arrows by finite reductions.
7. Rationalization sends beta to alpha and integral theta to rational theta, proving the
displayed square. The inverse square follows by cancellation. Hence alpha lifts to an
isomorphism of fixed pairs. Their carriers lie in the heart by the constant-object lemma,
so this is also an isomorphism of constructible Weil sheaves. -/
theorem constantWeilRationalScalar_equivariant
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (A B : AlgebraicallyClosedCoefficients.Index l Ω) (h : A ≤ B) :
    (sfWeilFrobeniusPullback D l hl Y₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)).map
        (constantCoefficientRationalScalarIso l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω A B h)
          (D.geometricFiber Y₀).left D hl).hom ≫
        (constantWeilRationalTheta l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B) D hl Y₀).hom =
      (constantWeilScalarComplex D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω A B h)).str.hom ≫
        (constantCoefficientRationalScalarIso l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω A B h)
          (D.geometricFiber Y₀).left D hl).hom ∧
    ∃ φ : constantWeilScalarSheaf D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω A B h) ≅
          constantWeilRationalSheaf l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B) D hl Y₀,
      (sfWeilForget D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)).map φ.hom.hom =
          (constantCoefficientRationalScalarIso l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω A B h)
            (D.geometricFiber Y₀).left D hl).hom := by
  sorry

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Every finite-stage constant pair belongs to the common-stage constructible heart.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence).
Proof: use its own stage and its rational constant carrier in both common-stage standard
classes. The carrier is the stage inclusion of that object, and its rational heart
membership supplies both required finite-stage classes. -/
theorem constantWeilStage_mem_heart (A : AlgebraicallyClosedCoefficients.Index l Ω) :
    sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω
      (sfWeilStageObject D l hl Y₀ Ω A
        (constantWeilRationalComplex l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
          D hl Y₀)).carrier := by
  sorry

/-- The literal E-stage canonical constant as an algebraically closed Weil sheaf.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence). -/
def constantWeilStageSheaf (A : AlgebraicallyClosedCoefficients.Index l Ω) :
    sfCommonStageWeilSheaf D l hl Y₀ Ω :=
  ⟨sfWeilStageObject D l hl Y₀ Ω A
    (constantWeilRationalComplex l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
      D hl Y₀), constantWeilStage_mem_heart D l hl Y₀ Ω A⟩

/-- The same normalized alpha, with its source identified by the recorded stage-system
transition equality. No independent scalar-extension isomorphism is selected.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence). -/
def constantWeilStageScalarIso (A B : AlgebraicallyClosedCoefficients.Index l Ω) (h : A ≤ B) :
    (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω
      (D.geometricFiber Y₀).left A B h).obj
        (constantWeilRationalObject l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
          D hl (D.geometricFiber Y₀).left) ≅
      constantWeilRationalObject l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)
        D hl (D.geometricFiber Y₀).left :=
  (eqToIso (congrArg (fun F ↦ F.obj
    (constantWeilRationalObject l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
      D hl (D.geometricFiber Y₀).left))
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω
          (D.geometricFiber Y₀).left).exists.choose_spec.1 A B h))) ≪≫
    constantCoefficientRationalScalarIso l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω A B h)
      (D.geometricFiber Y₀).left D hl

/-- The canonical underlying class from the least-stage constant to the E-stage constant.
The target self-transition and the associator are exactly the common-stage normalization.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence). -/
def constantWeilStageComparison (A : AlgebraicallyClosedCoefficients.Index l Ω) :=
  GeneralAlgebraicallyClosedCoefficients.ofHom
    (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).carrier
    (sfWeilStageObject D l hl Y₀ Ω A
      (constantWeilRationalComplex l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
        D hl Y₀)).carrier A (bot_le : (⊥ : IntermediateField (Padic l) Ω) ≤ A.val) le_rfl
    (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
      (D.geometricFiber Y₀).left).assoc
        (bot_le : (⊥ : IntermediateField (Padic l) Ω) ≤ A.val) le_rfl).inv.app
          (constantWeilRationalObject l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
            D hl (D.geometricFiber Y₀).left) ≫
      (GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω
        (D.geometricFiber Y₀).left A A le_rfl).map
          (constantWeilStageScalarIso D l hl Y₀ Ω (Padic.finiteCoefficientBase l Ω) A
            (bot_le : (⊥ : IntermediateField (Padic l) Ω) ≤ A.val)).hom)

/-- Clause 2: the E-stage canonical constant is canonically isomorphic to the least-stage
constant, and its inverse forgets to the normalized coefficient comparison class.
Source: blueprint coefficient-object paragraph, order 1869
(blueprint: lem-weil-constant-weil-structure-stage-independence).
Proof: apply clause 1 to Q_l subset E. Represent alpha at the stage E, inserting the
self-transition and associator used in constantWeilStageComparison. Represent its inverse
at the same stage. Composition gives the two identity classes. Clause 1 and the defining
common-stage pullback comparisons give Frobenius equivariance, so these classes lift to
inverse arrows of Weil pairs. Their carriers are exactly (E,E_Y) and (Q_l,(Q_l)_Y).
The forgetful functor keeps the representatives and thus has the displayed value. The
unit normalization is compatible with enlargement of the stage: both iterated and direct
unit maps send (r tensor s) tensor t to j(r)st, and the canonical scalar associators preserve
these formulas. Therefore the isomorphism is canonical in the common-stage category. -/
theorem constantWeilStructure_stageIndependent (A : AlgebraicallyClosedCoefficients.Index l Ω) :
    ∃ φ : constantWeilStageSheaf D l hl Y₀ Ω A ≅
        constantWeilAlgebraicallyClosedSheaf l D hl Y₀ Ω,
      (sfCommonStageWeilForget D l hl Y₀ Ω).map φ.inv.hom =
        constantWeilStageComparison D l hl Y₀ Ω A := by
  sorry

end WeilConjectures
