/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.Paper.SmoothTrace
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.FiniteTateSiteDescent
import Sheaf.Paper.ConstantCoefficientObjectsConstructible
import WeilConjectures.EtaleCohomology.Purity.Smooth.Adic
import WeilConjectures.EtaleCohomology.Purity.Smooth.Rational
import WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction
import WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization
import Sheaf.Paper.ConstantCoefficientScalarNormalization
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.PurAdicReconstruction

/-! # Adic and rational smooth dualizing complexes

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-cor-sp-all-coefficients/cor-pur-adic-and-rational-smooth-dualizing-complexes.md
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
universe u v₁ v₂ u₁ u₂ w₁ w₂
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures
namespace AdicSmoothDualizing

open AlgebraicGeometry.Scheme

/-- The positive completed coefficient line already used by the signed twists.
Source: the corollary proof, completed coefficient object and its Tate power
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev line (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  coefficientTwistPower T
    (R := completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension T)
    (purTwistIntegralModule T P.coefficients.l P.extension) d

/-- Pure completed-coefficient root tensors in that line, including its zero power.
Source: the corollary proof, the projection-normalized integral Tate line
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def generator (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (W : T.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted
      P.coefficients.l P.extension T).obj.obj W) :
    (d : ℕ) → (Fin d → (purTwistZlOne T P.coefficients.l).obj.obj W) →
      (line P T d).val.obj W
  | 0, _ => a
  | 1, x => @SMul.smul _ _ (purTwistIntegralAction T P.coefficients.l P.extension W).toSMul a
      (purTwistIntegralTensor T P.coefficients.l P.extension W 1 (x 0))
  | d + 2, x => SheafOfModules.siteSheafTensorTmul
      (line P T (d + 1)) (purTwistIntegralModule T P.coefficients.l P.extension) W
      (generator P T W a (d + 1) (fun i ↦ x i.castSucc))
      (purTwistIntegralTensor T P.coefficients.l P.extension W 1 (x (Fin.last (d + 1))))

/-- The finite projection of a completed Tate power is fixed on every local root
and completed scalar, rather than chosen as an unnormalized line isomorphism.
Source: corollary proof, reduction to the normalized finite coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: project completed scalars to the finite quotient. The integral root tensor
is defined over the discrete constants; its quotient is purTwistFiniteOne.
The tensor universal property gives the first-power map and its tensor powers.
At power zero use the coefficient projection. These generators generate locally,
so the displayed equations determine the morphism uniquely, including on the empty site. -/
theorem existsUnique_lineProjection (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n d : ℕ) :
    ∃! p : line P T d ⟶
        (scalarReductionRestriction P.coefficients.l P.extension T n).obj
          (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)),
      ∀ (W : T.ProEtᵒᵖ)
        (a : (completedIntegralCoefficientSheafUnrestricted
          P.coefficients.l P.extension T).obj.obj W)
        (x : Fin d → (purTwistZlOne T P.coefficients.l).obj.obj W),
        p.val.app W (generator P T W a d x) =
          @SMul.smul ((integralCoefficientSheaf
              P.coefficients.l P.extension T n).obj.obj W)
            ((finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)).val.obj W)
            (
              (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)).val.obj W
            ).isModule.toSMul
            ((completedIntegralCommRingProjectionUnrestricted
              P.coefficients.l P.extension T n).hom.app W a)
            (finiteTateProPowerGenerator P.coefficients.l P.extension n T W 1 d x) := by
  sorry

/-- The fixed positive finite level, with the original global conventions unchanged.
Source: corollary proof, reductions modulo every positive power
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def levelSetting (P : PurityFiniteSetting.{u}) (n : ℕ) : PurityFiniteSetting.{u} :=
  { P with level := n + 1, level_pos := Nat.succ_pos n }

/-- The projection selected by its unique root-tensor equations.
Source: corollary proof, integral reconstruction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def lineProjection (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (n d : ℕ) :=
  (existsUnique_lineProjection P T n d).exists.choose

/-- Reassociation of the nonnegative etale Tate powers, with the unit at degree zero.
Source: corollary proof and the detailed coefficient-twist conventions
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev etalePowerProduct (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
    P.diagonalExponent_annihilates d ⊗
      finiteEtaleTateLine T P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates

/-- The underlying sheaf tensor unitor, before endpoint presentation transport.
Source: corollary, zero-power tensor normalization
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def etalePowerUnitor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  λ_ (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
    P.diagonalExponent_annihilates)

/-- The zero power-step has the specified tensor-unitor data.
Source: corollary, coefficient unit at power zero
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the zero finite Tate power and the tensor unit are the same constant regular
module sheaf, obtained by sheafifying that constant presheaf. Thus the unitor has
exactly these endpoints. Heterogeneous equality fixes its data uniquely. -/
theorem existsUnique_etalePowerZero (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ∃! e : etalePowerProduct P T 0 ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates 1,
      HEq e (etalePowerUnitor P T) := by
  sorry

/-- A subsequent sheaf tensor power is literally the preceding power tensor the line.
Source: corollary, positive tensor powers
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: this is the successor clause of finiteEtaleTateTwist, with the same sheaf
monoidal structure. Its comparison is identity, so the prescribed data is unique. -/
theorem existsUnique_etalePowerPositive (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (d : ℕ) :
    ∃! e : etalePowerProduct P T (d + 1) ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates (d + 2),
      HEq e (Iso.refl (etalePowerProduct P T (d + 1))) := by
  sorry

/-- The power-step comparison is exactly the tensor unitor at zero and identity
thereafter. Its specified data is preserved by the endpoint transports.
Source: corollary proof, positive tensor powers
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def etalePowerStep (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (d : ℕ) → etalePowerProduct P T d ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates (d + 1)
  | 0 => (existsUnique_etalePowerZero P T).exists.choose
  | d + 1 => (existsUnique_etalePowerPositive P T d).exists.choose

/-- Every nonnegative finite Tate power is flat, including the coefficient unit.
Source: corollary proof and finite Tate descent
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the normalized root line is locally free of rank one because ell is invertible.
Its positive tensor powers remain locally free of rank one; power zero is the unit.
Tensoring with a locally free rank-one sheaf is locally the identity and hence exact. -/
theorem etalePowerFlat (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (d : ℕ) :
    ObjectProperty.flat (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates d) := by
  sorry

/-- The finite Tate sheaf placed in degree zero.
Source: the corollary's finite coefficient model
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev etaleSingle (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates d)

/-- The existing ordered derived tensor, with its site and coefficients explicit.
Source: the corollary's ordered tensor convention
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev etaleTensor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T

/-- The comparison family is fixed by the actual tensor map, shift comparison,
flat single-complex comparison, and sheaf-power step. HEq only transports their
endpoint presentations; it fixes the data of every factor.
Source: the corollary's normalized finite powers
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: at zero use the zero-shift unitor. At the successor tensor the preceding
comparison with the shifted root line. Move the two shifts outside tensor using
derivedTensorShiftIso, use singleFunctorObjTensorIso for the flat Tate power,
then etalePowerStep and PurityFiniteSetting.frameDegreeNext. These maps have the displayed
endpoints by unfolding the definitions. Induction constructs the family. HEq fixes each factor
uniquely; induction therefore also proves uniqueness of the whole family. -/
structure EtalePowerPresentation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) where
  comparison : (d : ℕ) → P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧
  normalized :
    letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    HEq (comparison 0) (((shiftFunctorZero _ ℤ).app (P.diagonalTwistEtale T 0)).symm) ∧
      ∀ d : ℕ,
        ∃ (e₁ : P.diagonalTwistEtale T (d + 1) ≅
              ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧))
          (e₂ : ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧) ≅
              (((etaleTensor P T).obj (etaleSingle P T d)).obj
                (etaleSingle P T 1))⟦2 * (d : ℤ) + 2⟧)
          (e₃ : ((etaleTensor P T).obj (etaleSingle P T d)).obj (etaleSingle P T 1) ≅
              (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d))
          (e₄ : (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d) ≅
              etaleSingle P T (d + 1)),
          HEq e₁ ((Etale.derivedTensorRight (ModuleCat.{u + 1} P.Coefficient) T
            ((etaleSingle P T 1)⟦(2 : ℤ)⟧)).mapIso (comparison d)) ∧
          HEq e₂ (Etale.derivedTensorShiftIso (ModuleCat.{u + 1} P.Coefficient) (X := T)
            (etaleSingle P T d) (etaleSingle P T 1) (2 * (d : ℤ)) 2) ∧
          HEq e₃ (Etale.singleFunctorObjTensorIso
            (A := ModuleCat.{u + 1} P.Coefficient) (X := T)
            (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates d)
            (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates) (etalePowerFlat P T hT d)) ∧
          HEq e₄ ((DerivedCategory.singleFunctor _ 0).mapIso (etalePowerStep P T d)) ∧
          comparison (d + 1) = e₁ ≪≫ e₂ ≪≫
            (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso (e₃ ≪≫ e₄) ≪≫
            eqToIso (congrArg (fun j : ℤ ↦ (etaleSingle P T (d + 1))⟦j⟧)
              (PurityFiniteSetting.frameDegreeNext d))

/-- The canonical finite tensor presentation, with its full normalization stored
in its type, is uniquely determined.
Source: the corollary's ordered Tate powers
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: construct the comparison by induction from the zero-shift unitor using
exactly the four normalized factors. HEq fixes each factor, so induction proves
uniqueness of the comparison. The normalization proof is unique by proof irrelevance. -/
theorem existsUnique_etalePowerPresentation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) :
    ∃! e : EtalePowerPresentation P T hT, True := by
  sorry

/-- The canonical ordered-tensor family selected by its uniquely determining recursion.
Source: the corollary's finite Tate presentation
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def etalePowerComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) :
    (d : ℕ) → P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧ :=
  ((existsUnique_etalePowerPresentation P T hT).exists.choose).comparison

set_option backward.isDefEq.respectTransparency false in
/-- The unique finite site comparison fixed by the root-limit projections.
Source: corollary proof, finite normalization; finite Tate site descent
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: finite Tate site descent gives the comparison for the annihilator ell^(n+1).
The displayed projection formula is its defining normalization. Local root lifts
and pure tensor generation make two such comparisons equal. -/
theorem existsUnique_rootComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (_aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    ∃! b : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T).obj
        (finiteEtaleTateTwist T (levelSetting P n).diagonalExponent
          (levelSetting P n).Coefficient (levelSetting P n).diagonalExponent_annihilates d) ≅
        finiteTateProSheaf P.coefficients.l P.extension n T d,
      IsFiniteTateSiteComparison P.coefficients.l P.extension n T n
        (levelSetting P n).diagonalExponent_annihilates d b := by
  sorry

/-- The finite comparison selected from its unique root-projection characterization.
Source: corollary proof, finite coefficient comparisons
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rootComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :=
  (existsUnique_rootComparison P T aT n d).exists.choose

/-- A realization comparison fixes each scalar-unit section of the original sheaf.
Source: the corollary's fixed-to-intrinsic finite coefficient transport
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def IsScalarUnitRealization (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (N : proEtaleRingModules T (proEtaleConstantRing T A))
    (e : (sfIntrinsicModuleEquivalence T A).functor.obj M ≅ N) : Prop :=
  ∀ (W : T.ProEtᵒᵖ) (y : M.obj.obj W),
    HEq (e.hom.val.app W (sfIntrinsicRealizationUnit T A M W y)) y

/-- The finite fixed-scalar realization is fixed on every scalar-unit section.
Source: corollary proof, canonical finite coefficient presentation
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: restriction to the constant scalar action is inverse to the canonical
finite coefficient realization. The realization unit sends a section to its
scalar-unit generator. Extend the identity on these sections by local scalar
linearity and sheafification. The two inverse composites are identities on those
generators, which also proves uniqueness. -/
theorem existsUnique_finiteRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n d : ℕ) :
    ∃! e : (sfIntrinsicModuleEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        (finiteTateProSheaf P.coefficients.l P.extension n T d) ≅
        finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ),
      IsScalarUnitRealization T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        (finiteTateProSheaf P.coefficients.l P.extension n T d)
        (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)) e := by
  sorry

/-- The preceding canonical realization, with no generator or orientation choice.
Source: corollary proof, finite comparison
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def finiteRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (n d : ℕ) :=
  (existsUnique_finiteRealization P T n d).exists.choose

/-- Exact functors carry shifted single complexes to the shifted single image.
The data is the standard shift comparison followed by the single-complex comparison.
Source: the corollary's exact coefficient and site transports
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def exactSingleShiftIso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    (M : C) (j : ℤ) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj M)⟦j⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj (F.obj M))⟦j⟧ :=
  (F.mapDerivedCategory.commShiftIso j).app _ ≪≫
    (shiftFunctor _ j).mapIso ((F.mapDerivedCategorySingleFunctor 0).app M)

/-- Canonical comparison from the finite purity orientation's ordered shifted tensor
model to the specified intrinsic finite Tate power placed in degree -2d.
Source: corollary proof, normalized finite purity at each reduction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def finitePowerComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    (sfIntrinsicDerivedEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        ((levelSetting P n).diagonalTwist T d) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)))⟦2 * (d : ℤ)⟧ :=
  Functor.mapIso (Functor.mapDerivedCategory (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor)
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T).mapDerivedCategory.mapIso
      (etalePowerComparison (levelSetting P n) T
        ((levelSetting P n).diagonalExponent_isUnit aT) d) ≪≫
      exactSingleShiftIso (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T) _ (2 * (d : ℤ)) ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso (rootComparison P T aT n d))) ≪≫
    exactSingleShiftIso (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor _
      (2 * (d : ℤ)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (finiteRealization P T n d))

/-- The source's completed coefficient unit with Tate twist and even shift.
Only its finite-Tor membership is asserted here; its data is the existing root
line tensor power in a genuine single complex.
Source: corollary proof, the completed unit and its twist
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the root line is locally free of rank one and derived complete. The signed
twist definition at nonnegative d is exactly line P T d. Its finite reductions
are flat lines in degree zero. The shift gives common Tor interval [-2d,-2d].
Thus this is in the recorded complete finite-Tor constructible subcategory. -/
theorem integralTwist_mem (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension T
      (((DerivedCategory.singleFunctor _ 0).obj (line P T d))⟦2 * (d : ℤ)⟧) := by
  sorry

/-- The full-subcategory restriction of the existing completed Tate coefficient object.
Source: corollary proof, Lambda_X(d)[2d]
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralTwist (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension T :=
  ⟨((DerivedCategory.singleFunctor _ 0).obj (line P T d))⟦2 * (d : ℤ)⟧,
    integralTwist_mem P T aT d⟩

/-- The actual quotient projection, transposed under the tensor-unit-normalized
coefficient adjunction and then shifted. Its target is identified with the finite
purity twist through the root-normalized finite comparison above.
Source: corollary proof, reduction-normalized integral reconstruction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def twistReduction (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) T)).obj (integralTwist P T aT d).obj ⟶
      (sfIntrinsicDerivedEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        ((levelSetting P n).diagonalTwist T d) :=
  let φ := PurCompactSupport.projection P.coefficients.l P.extension
    (n + 1) (Nat.succ_pos n) T
  letI := PurCompactSupport.scalarCommShift φ
  ((pbcDerivedExtend φ).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      (((pbcDerivedScalarAdjunction φ).homEquiv _ _).symm
        ((DerivedCategory.singleFunctor _ 0).map (lineProjection P T n d) ≫
          ((pbcRestrict φ).mapDerivedCategorySingleFunctor 0).inv.app _)) ≫
    (finitePowerComparison P T aT n d).inv

/-- The finite coefficient unit is bounded below after exact site comparison.
Source: corollary proof, finite counit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: exact comparison carries the degree-zero constant sheaf to its degree-zero
inverse image. All negative cohomology sheaves vanish, so zero is a lower bound. -/
theorem finiteUnitPlus (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit P.Coefficient T)) := by
  sorry

variable (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]

/-- The recorded Nagata compactification of the structure morphism.
Source: corollary proof, compact-support functor
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def compactification : Compactification (X ↘ Spec (.of P.field.k)) :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X
    (Spec (.of P.field.k)) (X ↘ Spec (.of P.field.k))
  HasCompactification.compactification (X ↘ Spec (.of P.field.k))

set_option backward.isDefEq.respectTransparency false in
/-- The normalized finite integration map. Its orientation is the published
coordinate-counit-normalized diagonal purity isomorphism. Every other factor is a
specified proper/open or coefficient-realization comparison and the actual counit.
Source: corollary proof, normalized finite trace at the coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def finiteIntegration (n d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) (compactification P X)).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((levelSetting P n).diagonalTwist X d)) ⟶
      (levelSetting P n).coefficientUnit (Spec (.of P.field.k)) :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X
    (Spec (.of P.field.k)) (X ↘ Spec (.of P.field.k))
  (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n
      (compactification P X)).hom.app _ ≫
    (ProEtale.sfIntrinsicCompactSupportComparison (levelSetting P n).Ring
      (compactification P X)).hom.app _ ≫
    (sfIntrinsicDerivedEquivalence (Spec (.of P.field.k)) (levelSetting P n).Ring).functor.map
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} (levelSetting P n).Coefficient)
        (X ↘ Spec (.of P.field.k))).map
        ((levelSetting P n).diagonalDualizingObject d (X ↘ Spec (.of P.field.k))
          (𝟙 (Spec (.of P.field.k)))).inv ≫
        ProEtale.rightDerivedUpperShriekCounit (X ↘ Spec (.of P.field.k)) _
          (finiteUnitPlus (levelSetting P n) (Spec (.of P.field.k))))

/-- An integral integration map is normalized precisely when its reductions are the
specified finite integration maps, through actual scalar-extension and root comparisons.
Source: corollary proof, adic reconstruction of the normalized counit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def IsNormalizedIntegralIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))]
    (t : (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) (compactification P X)).obj
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj) : Prop :=
  ∀ n : ℕ,
    (PurCompactSupport.comparison (PurCompactSupport.reduction P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) (compactification P X)).app
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ≫
      (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) (compactification P X)).map
          (twistReduction P X (X ↘ Spec (.of P.field.k)) n d) ≫
      finiteIntegration P X n d =
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n) (Spec (.of P.field.k)))).map t ≫
        twistReduction P (Spec (.of P.field.k)) (𝟙 _) n 0

/-- The selected finite extension in the coefficient-system coordinates.
Source: corollary coefficient conventions
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev fieldStage : ConstructibleExceptionalCoefficients.FieldStage.{u} P.coefficients.l where
  carrier := P.extension

/-- The structure morphism is a morphism over its base field.
Source: the structure-morphism convention of the corollary
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the structure morphism of Spec k over itself is Spec.map of the identity,
which is the identity by Spec.map_id, so the required triangle commutes by the
right identity law. -/
theorem structureIsOver : (X ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k)) := by
  sorry

attribute [instance] structureIsOver

variable (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
  P.field P.coefficients.different (f := X ↘ Spec (.of P.field.k)))

/-- The exceptional coefficient operation in any of the three stages of the corollary.
This is the recorded normalized constructible adjunction, not a new choice of adjoint.
Source: corollary, Ra_X! and Ra_X^!
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev operation (s : ConstructibleExceptionalCoefficients.Stage.{u} P.coefficients.l) :=
  S.ring.operation (compactification P X) s

/-- The integral counit read on the twisted coefficient object through an identification
of the dualizing complex. This expression retains the actual adjunction counit.
Source: corollary, integral counit clause
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralCounit (d : ℕ)
    (e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      integralTwist P X (X ↘ Spec (.of P.field.k)) d) :=
  (operation P X S (.integral (fieldStage P))).F.map e.inv ≫
    (operation P X S (.integral (fieldStage P))).adjunction.counit.app
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0)

/-- The same counit in ordinary completed-coefficient compact-support coordinates.
The left realization is normalized by the proper/open construction in the existing system.
Source: corollary, RΓ_c and the completed coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralCounitAmbient (d : ℕ)
    (e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      integralTwist P X (X ↘ Spec (.of P.field.k)) d) :=
  (S.ring.left (compactification P X)
      (.integral (fieldStage P))).inv.app
        (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension
      (Spec (.of P.field.k))).ι.map (integralCounit P X S d e)

/-- The integral clause of the corollary, including its canonical normalization.
The unit is the completed regular coefficient module (power zero), and its reduction
at every positive level is the free rank-one finite coefficient unit.

Source: current blueprint cor-pur-adic-and-rational-smooth-dualizing-complexes,
proof Step 1 and normalized-integration paragraph
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: apply thm-pur-adic-reconstruction to the completed coefficient unit.
Each finite reduction is the free coefficient module with Tor interval [0,0].
The finite purity maps are isomorphisms and their scalar-naturality makes them a
map of normalized systems. Reconstruction gives an isomorphism from the completed
twisted pullback of the unit to its exceptional pullback. Pullback of the completed
unit is the completed unit on X. Invert the reconstructed isomorphism to obtain e.
The reconstructed counit reduces to the finite normalized smooth trace: its factors
are finite purity followed by the exceptional counit. The root projections,
coefficient multiplication and even-shift comparisons are precisely twistReduction.
Thus its normalization is the displayed IsNormalizedIntegralIntegration predicate.
For uniqueness transpose under the exceptional adjunction and reduce to the same
finite purity morphism at every level. Use the already constructed isomorphism to
identify the dualizing object with the shifted line. Degree-zero full faithfulness
then identifies a difference with an ordinary endomorphism of that completed line.
The root projections and completed coefficient projections are jointly injective, so
an endomorphism vanishing at every finite quotient is zero. Thus the isomorphisms agree.
No uniqueness assertion about arbitrary triangulated homotopy-limit maps is used. -/
theorem existsUnique_integralIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    ∃! e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
        integralTwist P X (X ↘ Spec (.of P.field.k)) d,
      IsNormalizedIntegralIntegration P X d (integralCounitAmbient P X S d e) := by
  sorry

/-- The canonical integral identification is selected only after its normalized
integration property has determined it uniquely.
Source: corollary, omega_X = O_E,X(d)[2d]
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S (.integral (fieldStage P))).G.obj
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
        integralTwist P X (X ↘ Spec (.of P.field.k)) d :=
  (existsUnique_integralIdentification P X S d).exists.choose

/-- The rational coefficient unit and its shifted twist, using the literal
rationalization of the same completed integral representatives.
Source: corollary proof Step 2, rationalization
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rationalTwist (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
    (fieldStage P) T).obj (integralTwist P T aT d)

/-- The rational identification is exactly the transported inverse integral purity map.
Source: corollary proof Step 2, coefficient comparison for exceptional pullback
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rationalIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S (.rational (fieldStage P))).G.obj
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      rationalTwist P X (X ↘ Spec (.of P.field.k)) d :=
  ((S.fields.rationalizationComparison (compactification P X) (fieldStage P)).b.symm.app
    (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
  (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
    (fieldStage P) X).mapIso (integralIdentification P X S d)

/-- Rational integration is the specified scalar transport of normalized integral
integration, through the compact-support coefficient comparison.
Source: corollary proof Steps 2--3
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rationalIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :=
  (S.fields.rationalizationComparison (compactification P X) (fieldStage P)).q.inv.app
      (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (fieldStage P) (Spec (.of P.field.k))).map
        (integralCounit P X S d (integralIdentification P X S d))

/-- The selected field's index in the recorded common-stage category.
Source: corollary proof Step 2, descent of a finite coefficient stage
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def fieldIndex : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar :=
  ⟨P.extension, P.finiteExtension⟩

/-- The prescribed small-model transport, retaining its actual algebra equivalence.
Source: corollary proof Step 2, common-stage size convention
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def modelEmbedding : P.extension →ₐ[Padic P.coefficients.l]
    AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (fieldIndex P) :=
  (Shrink.algEquiv (Padic P.coefficients.l) P.extension).symm.toAlgHom

/-- Scalar transport to that small coefficient model uses the existing rational tensor
functor, with no equality imposed on coefficient and site universes.
Source: corollary proof Step 2, common-stage descent
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev modelScalar (T : Scheme.{u}) :=
  ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
    (fieldStage P)
    (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
      (fieldIndex P)) (modelEmbedding P) T

/-- The actual common-stage inclusion of the selected coefficient field.
Source: corollary proof Step 2, Qbar coefficients
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev commonInclusion (T : Scheme.{u}) :=
  ConstructibleExceptionalCoefficients.commonInclusion P.coefficients.l P.coefficients.Qbar
    T (fieldIndex P)

/-- The closed coefficient unit and its twist represented over the selected finite
stage. The representative uses the actual size transport and common-stage inclusion.
Source: corollary proof Step 2, Qbar_X(d)[2d]
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def closedTwist (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  (commonInclusion P T).obj ((modelScalar P T).obj (rationalTwist P T aT d))

/-- Transport the rational identification first through the specified small-model
coefficient change and then through the common-stage exceptional comparison.
Source: corollary proof Step 2, transported Qbar purity
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def closedIdentification (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S .closed).G.obj (closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      closedTwist P X (X ↘ Spec (.of P.field.k)) d :=
  ((S.common.commonComparison (compactification P X) (fieldIndex P)).b.symm.app
      ((modelScalar P (Spec (.of P.field.k))).obj
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0))) ≪≫
    (commonInclusion P X).mapIso
      (((S.fields.rationalComparison (compactification P X) (fieldStage P)
          (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
            (fieldIndex P)) (modelEmbedding P)).b.symm.app
              (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) ≪≫
        (modelScalar P X).mapIso (rationalIdentification P X S d))

/-- Qbar integration is common-stage descent of the same rationalized integral map.
The compact-support comparisons are the published normalized q maps.
Source: corollary proof Step 3, transported normalized integration
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def closedIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :=
  (S.common.commonComparison (compactification P X) (fieldIndex P)).q.inv.app
      ((modelScalar P X).obj (rationalTwist P X (X ↘ Spec (.of P.field.k)) d)) ≫
    (commonInclusion P (Spec (.of P.field.k))).map
      ((S.fields.rationalComparison (compactification P X) (fieldStage P)
          (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
            (fieldIndex P)) (modelEmbedding P)).q.inv.app
              (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
        (modelScalar P (Spec (.of P.field.k))).map (rationalIntegration P X S d))

/-- The rational and algebraically closed counit clauses of the smooth dualizing
corollary. Together with existsUnique_integralIdentification these cover exactly
O_E, E and Qbar_l; none of the three integration maps has an arbitrary scalar factor.
The functors on Spec k are the sheaf coordinates of the recorded ordinary compact
cohomology, so applying the recorded coefficient-point fibre gives RΓ_c -> Lambda.

Source: current blueprint cor-pur-adic-and-rational-smooth-dualizing-complexes
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: Step 1 is existsUnique_integralIdentification: reconstruct finite normalized
purity at the completed unit, identify its pullback with the completed unit on X,
and invert. Step 2 applies rationalization to that inverse, with the exceptional
coefficient comparison b. Size-transport the same rational representative and descend
it to the common-stage category to get the Qbar identification. These are exactly
rationalIdentification and closedIdentification, so they invert transported purity.
Step 3 applies the counit equation of each recorded coefficient comparison. It says
that q inverse followed by the scalar-extended old trace is the new counit after
compact-support image of the transported identification. First use rationalization,
then the small-model field change, then common-stage inclusion. Finite normalization
is inherited from the coordinate Kummer orientation in finiteIntegration; on affine
space its ordered product of normalized A1 classes integrates to one. No global
fundamental class or assertion that integration is invertible is made for arbitrary X.
Finally the coefficient-point fibre identifies the unit with the scalar coefficient
complex and the compact-support value with the recorded RΓ_c. -/
theorem adic_and_rational_smooth_dualizing_complexes (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    IsNormalizedIntegralIntegration P X d
      (integralCounitAmbient P X S d (integralIdentification P X S d)) ∧
    ((operation P X S (.rational (fieldStage P))).adjunction.counit.app
        (rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
      (operation P X S (.rational (fieldStage P))).F.map
          (rationalIdentification P X S d).hom ≫ rationalIntegration P X S d) ∧
    ((operation P X S .closed).adjunction.counit.app
        (closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0) =
      (operation P X S .closed).F.map
          (closedIdentification P X S d).hom ≫ closedIntegration P X S d) := by
  sorry

end AdicSmoothDualizing
end WeilConjectures
