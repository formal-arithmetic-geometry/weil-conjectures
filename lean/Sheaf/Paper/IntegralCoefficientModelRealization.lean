/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q152
-/
module

public import Sheaf.Paper.IntegralAmbientDirectImageEncoding
public import Sheaf.Paper.IntegralQuotientResolutionNormalization
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralAmbientCoefficientPresentation
import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
import Sheaf.Paper.IntegralCoefficientPresentationComparison
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral

/-! # Normalized integral coefficient models and ordinary direct image

Source: Bhatt--Scholze, Section 6.5; Stacks Tags 093J, 093M and 0D6E;
IntegralAmbientTowerComparison, coefficientModel_exists and encodings
(blueprint: lem-sfb-integral-coefficient-model-realization).

Positive exponent n + 1 is indexed by n. Constant quotient sheaves are kept separate
from the adic datum's continuous-function presentation. Naturality is written in
adjunct form on sections, using the actual coefficient morphisms, with no chosen
replacement action. All module derived categories are ordinary and unbounded.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.IntegralAmbientTower

attribute [-instance] ConstantScalarRestriction.fixedAbelian
attribute [-instance] ConstantScalarRestriction.fixedPreadditive
attribute [-instance] ConstantScalarRestriction.fixedZeroMorphisms

variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)

/-- The finite coefficient-model field in constant-sheaf coordinates. The comparison
is the existing constants-to-functions isomorphism, so no new scalar action is chosen.
Source: Bhatt--Scholze, Section 6.5; Stacks 093J
(blueprint: lem-sfb-integral-coefficient-model-realization). -/
def CoefficientModel.constantFinite {π : PadicAlgCl.integers l E.1}
    {hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)}
    {T : Scheme.{u}} (C : CoefficientModel l E π hπ T) (n : ℕ) :
    quotientRing l E π T n ≅
      adicLisseConstantRing T (integers.{u} l E ⧸ (datum.{u} l E π hπ).ideal ^ (n + 1)) :=
  C.finite n ≪≫ (pbcLevelConstantComparison T (datum.{u} l E π hπ) n).symm

/-- The completed field in the actual inverse limit of constant quotient sheaves.
Source: Bhatt--Scholze, Section 6.5; Stacks 093M
(blueprint: lem-sfb-integral-coefficient-model-realization). -/
def CoefficientModel.constantCompleted {π : PadicAlgCl.integers l E.1}
    {hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)}
    {T : Scheme.{u}} (C : CoefficientModel l E π hπ T) :
    integralRing l E T ≅ adicLisseCompletedRing T (datum.{u} l E π hπ).ideal :=
  C.completed ≪≫ (pbcCompletedComparison T (datum.{u} l E π hπ)).symm

/-- The actual quotient diagram, obtained by pulling back the continuous quotient maps
and reconstructing their section rings. Its maps include all positive quotient transitions.
Source: Bhatt--Scholze, Section 6.5
(blueprint: lem-sfb-integral-coefficient-model-realization). -/
def realizationQuotientSystem (π : PadicAlgCl.integers l E.1) (T : Scheme.{u}) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ quotientRing l E π T n)
    (fun n ↦ CondensedRing.sectionRingMap T
      (AlgebraicGeometry.ProEtale.completedCoefficientMap T
        (completedResidueTransition.{u} l E π n)).hom)

/-- Arithmetic, normalized coefficient realization, all coefficient squares and the
ordinary and derived direct-image encodings, for arbitrary schemes and morphisms.

Source: Bhatt--Scholze, Section 6.5 and Lemma 6.5.9(3); Stacks 093J, 093M, 0D6E
(blueprint: lem-sfb-integral-coefficient-model-realization).

Proof:
1. Apply lem-sfb-integral-quotient-resolution-normalization with pi the uniformizer.
   Its finite free two-term resolutions make the positive quotients perfect. The
   l-adic absolute value puts l in (pi); writing l = pi*a shows that l^(n+1) kills
   every positive quotient. In particular the residue ring is additive torsion.
   The uniformizer ideal is principal, and the valuation ring is Noetherian.
2. Lem-sf-finite-discrete-normalized-encoding identifies each finite coefficient with
   constants, preserving every scalar. Compose the normalized limit comparison of
   step 1 with the limit of these finite comparisons. The resulting projections
   are the actual pulled-back quotient maps. Use the quotient ULift isomorphisms
   and constants-to-functions comparisons of
   lem-weil-pbc-integral-coefficient-presentation-comparison to obtain CoefficientModel.
   The class of a is sent to the class of up a. Local constant generation proves
   uniqueness at finite level, and joint monicity of projections proves it at the limit.
3. The canonical coefficient inverse-image maps send every constant residue class
   to the same class after base change. Therefore the finite squares commute.
   Quotient transitions commute by the same calculation. The projection equation
   of lem-weil-pbc-profinite-coefficient-inverse-image reduces the integral square
   to these finite squares. This uses no preservation of arbitrary limits.
4. Lem-sfb-internal-module-operations-transport makes the fixed section encodings
   additive exact equivalences. Scalar restriction along the normalized ring
   isomorphisms and lem-sfb-constant-scalar-restriction-tensor give the ambient and
   finite encodings, retaining all underlying additive maps and section groups.
5. On V over Y, both ordinary ambient direct images have section group M(V times_Y X).
   The two scalar actions agree by the adjunct of the integral square in step 3.
   Thus the identity on these groups is an invertible natural linear comparison.
6. At a finite level both actions are multiplication by the same constant residue
   class. The finite square in step 3 makes identity on sections a natural linear
   comparison with the specified fixed-scalar direct image.
7. Apply lem-derived-exact-equivalence-squares to each ordinary square and the
   prescribed right-derived pairs. Supply its unused left half by zero functors,
   using lem-weil-pbc-exact-functor-derived-functor. The resulting comparison
   intertwines the universal right-derived units on every complex, exactly as in
   NormalizedSquare.normalization. No boundedness, completeness, properness or
   constructibility hypothesis is used.
-/
theorem integral_coefficient_model_realization (π : PadicAlgCl.integers l E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)) :
    IsNoetherianRing (integers.{u} l E) ∧
    (Ideal.span ({ULift.up π} : Set (integers.{u} l E))).FG ∧
    (∀ x : integers.{u} l E ⧸ Ideal.span {ULift.up π},
      ∃ m : ℕ, 0 < m ∧ m • x = 0) ∧
    (∀ n : ℕ, Finite (integers.{u} l E ⧸ (Ideal.span {ULift.up π}) ^ (n + 1))) ∧
    (∀ n : ℕ, 1 ≤ n → adicQuotientPerfect (integers.{u} l E)
      (Ideal.span {ULift.up π}) n) ∧
    (∀ (n : ℕ) (x : integers.{u} l E ⧸ (Ideal.span {ULift.up π}) ^ (n + 1)),
      l ^ (n + 1) • x = 0) ∧
    (∀ T : Scheme.{u}, Nonempty (CoefficientModel l E π hπ T) ∧
      ∀ C : CoefficientModel l E π hπ T,
        (∀ n : ℕ,
          (C.constantCompleted l E).hom ≫
              limit.π (adicLisseRingSystem T (datum.{u} l E π hπ).ideal) (op n) =
            quotientProjection l E π T n ≫ (C.constantFinite l E n).hom) ∧
        (∀ (a b : ℕᵒᵖ) (g : a ⟶ b),
          (realizationQuotientSystem l E π T).map g ≫
              (C.constantFinite l E b.unop).hom =
            (C.constantFinite l E a.unop).hom ≫
              (adicLisseRingSystem T (datum.{u} l E π hπ).ideal).map g)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        (CX : CoefficientModel l E π hπ X) (CY : CoefficientModel l E π hπ Y),
      (∀ (V : Y.ProEtᵒᵖ) (s : (integralRing l E Y).obj.obj V),
        (CX.completed.hom.hom.app ((proEtaleBaseChange f).op.obj V))
            (((condensedPushforwardHom (Profinite.padicIntegersRingObj.{u} l E.1) f).hom.app V)
              s) =
          (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
              ((datum.{u} l E π hπ).integralRingIso f).hom).hom.app V)
            (CY.completed.hom.hom.app V s)) ∧
      (∀ (n : ℕ) (V : Y.ProEtᵒᵖ) (s : (quotientRing l E π Y n).obj.obj V),
        ((CX.finite n).hom.hom.app ((proEtaleBaseChange f).op.obj V))
            (((condensedPushforwardHom
              (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) f).hom.app V) s) =
          (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
              ((datum.{u} l E π hπ).finiteRingIso f n).hom).hom.app V)
            ((CY.finite n).hom.hom.app V s)) ∧
      Nonempty (AmbientEncoding l E f CX CY) ∧
      ∀ n : ℕ, Nonempty (FinitePushEncoding l E (π := π) (hπ := hπ) f n)) := by
  sorry

end AlgebraicGeometry.Scheme.IntegralAmbientTower
