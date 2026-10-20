/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.Paper.TateInverseLimitBaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Paper.ConstantTwoTermResolution
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Paper.KFlatConeComparison
import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.CategoryTheory.Yoneda
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-! # Finite Kummer level of the Tate twist

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.md
(blueprint: lem-pur-finite-kummer-level).

The source is the published inverse-limit/scalar-extension Tate line, not the already
finite etale line of the purity conventions. The comparison is fixed on local tensors
by the N-th root projection. The base-change square uses the coordinatewise root map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The existing coefficient quotient at positive level n+1; this is only an index alias.
Source: finite Kummer level, coefficient notation (blueprint: lem-pur-finite-kummer-level). -/
abbrev kummerCoefficient (P : PurityFiniteSetting.{u}) (n : ℕ) :=
  Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)

/-- The existing coefficient ring sheaf at positive level n+1.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
abbrev kummerRingSheaf (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u}) :=
  integralCoefficientCommRingSheaf P.coefficients.l P.extension T n

/-- The existing finite twist O_E(1) tensor A, with the published constant-ring tensors.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
abbrev kummerLine (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u}) :=
  Scheme.purTwistFiniteOne T P.coefficients.l P.extension n

/-- The scalar map from Z/ell^(N+1) to A, applied to constant sheaves.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def kummerScalarMap (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u}) :
    Scheme.purTwistFiniteRing T P.coefficients.l N ⟶ P.kummerRingSheaf n T :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (a.comp ULift.ringEquiv.toRingHom)))

/-- Exactly mu_(ell^(N+1)) tensor_(Z/ell^(N+1)) A, with its A-action.
The roots module is the recorded kernel of the power map, transported only through
commutation of constant sheaves with forgetting commutativity.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def kummerRootsTensor (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u}) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (P.kummerScalarMap n N a T) (Scheme.purTwistRootsModule T P.coefficients.l N)

/-- The source's local tensor a tensor (b tensor x), using both published sheafifications.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def kummerSourceTensor (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u})
    (U : T.ProEt)
    (a : (P.kummerRingSheaf n T).obj.obj (op U))
    (b : (Scheme.purTwistIntegralConstant T P.coefficients.l P.extension).obj.obj (op U))
    (x : (Scheme.purTwistZlOne T P.coefficients.l).obj.obj (op U)) :
    (P.kummerLine n T).val.obj (op U) :=
  Scheme.purScalarSection
    (Scheme.purTwistIntegralConstant T P.coefficients.l P.extension)
    (P.kummerRingSheaf n T)
    (Scheme.purTwistIntegralQuotient T P.coefficients.l P.extension n)
    (Scheme.purTwistIntegralOne T P.coefficients.l P.extension) U a
    (Scheme.purTwistIntegralTensor T P.coefficients.l P.extension (op U) b x)

/-- Pure tensors in the explicit finite roots scalar extension.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def kummerTargetTensor (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (U : T.ProEt) (z : (P.kummerRingSheaf n T).obj.obj (op U))
    (y : (Scheme.proEtaleRootsOfUnitySheaf T (P.coefficients.l ^ (N + 1))).obj.obj
      (op U)) : (P.kummerRootsTensor n N a T).val.obj (op U) :=
  Scheme.purScalarSection (Scheme.purTwistFiniteRing T P.coefficients.l N)
    (P.kummerRingSheaf n T) (P.kummerScalarMap n N a T)
    (Scheme.purTwistRootsModule T P.coefficients.l N) U z y

/-- The canonical projection normalization, including the integral scalar in a tensor.
Source: finite Kummer level (blueprint: lem-pur-finite-kummer-level). -/
def IsKummerComparison (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (α : P.kummerLine n T ≅ P.kummerRootsTensor n N a T) : Prop :=
  ∀ (U : T.ProEt) (z : (P.kummerRingSheaf n T).obj.obj (op U))
    (b : (Scheme.purTwistIntegralConstant T P.coefficients.l P.extension).obj.obj (op U))
    (x : (Scheme.purTwistZlOne T P.coefficients.l).obj.obj (op U)),
    α.hom.val.app (op U) (P.kummerSourceTensor n T U z b x) =
      P.kummerTargetTensor n N a T U
        (z * (Scheme.purTwistIntegralQuotient T P.coefficients.l P.extension n).hom.app
          (op U) b)
        ((limit.π (Scheme.proEtaleRootsOfUnityTower T P.coefficients.l
          (Fact.out : P.coefficients.l.Prime)) (op N)).hom.app (op U) x)

/-- The ordinary tensor comparison induced by the finite Kummer map on the second factor.
Source: finite Kummer level, derived tensor clause (blueprint: lem-pur-finite-kummer-level). -/
def kummerTensorMap (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (α : P.kummerLine n T ≅ P.kummerRootsTensor n N a T) :=
  SheafOfModules.siteSheafTensorRightMap (A := P.kummerRingSheaf n T) α.hom

/-- Derived tensor compatibility on every K-flat representative. The ordinary natural
comparison is the second-factor map of the SAME normalized finite Kummer comparison.
Its termwise image on a K-flat complex is a quasi-isomorphism; this is precisely the
induced comparison K tensor^L A(1) to K tensor^L (mu tensor A).
Source: finite Kummer level, last sentence (blueprint: lem-pur-finite-kummer-level). -/
def KummerDerivedCompatible (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n) (T : Scheme.{u})
    (α : P.kummerLine n T ≅ P.kummerRootsTensor n N a T) : Prop :=
  ∀ K : CochainComplex (Scheme.tateModules T (P.kummerCoefficient n)) ℤ,
    CochainComplex.IsAcyclicTensorKFlat (R := P.kummerRingSheaf n T) K →
      QuasiIso (((P.kummerTensorMap n N a T α).mapHomologicalComplex
        (ComplexShape.up ℤ)).app K)

/-- The full base-change clause, on arbitrary scheme morphisms, with both vertical
comparisons fixed on inverse-image units. The root-limit map is fixed at EVERY level;
no assertion that inverse image commutes with infinite limits is assumed.
Source: finite Kummer level, final sentence (blueprint: lem-pur-finite-kummer-level). -/
def KummerBaseChangeCompatible (P : PurityFiniteSetting.{u}) (n N : ℕ)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n)
    (α : ∀ (T : Scheme.{u})
      (_hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
      P.kummerLine n T ≅ P.kummerRootsTensor n N a T) : Prop :=
  ∀ (T T' : Scheme.{u}) (f : T' ⟶ T)
    (hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x))
    (hT' : ∀ x : T', IsUnit (P.coefficients.l : T'.presheaf.stalk x)),
    ∃ c : Scheme.purTwistZlOne T P.coefficients.l ⟶
        (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
          (Scheme.purTwistZlOne T' P.coefficients.l),
      (∀ r : ℕ,
        c ≫ (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
            (limit.π (Scheme.proEtaleRootsOfUnityTower T' P.coefficients.l
              (Fact.out : P.coefficients.l.Prime)) (op r)) =
          limit.π (Scheme.proEtaleRootsOfUnityTower T P.coefficients.l
            (Fact.out : P.coefficients.l.Prime)) (op r) ≫
              Scheme.proEtaleRootsOfUnityDirectImageMap f (P.coefficients.l ^ (r + 1))) ∧
      ∃ β : (Scheme.tatePullback f (P.kummerCoefficient n)).obj (P.kummerLine n T) ≅
          P.kummerLine n T',
        ∃ δ : (Scheme.tatePullback f (P.kummerCoefficient n)).obj
            (P.kummerRootsTensor n N a T) ≅ P.kummerRootsTensor n N a T',
          (∀ (U : T.ProEt) (z : (P.kummerRingSheaf n T).obj.obj (op U))
            (b : (Scheme.purTwistIntegralConstant T P.coefficients.l P.extension).obj.obj
              (op U))
            (x : (Scheme.purTwistZlOne T P.coefficients.l).obj.obj (op U)),
            β.hom.val.app (op ((Scheme.proEtaleBaseChange f).obj U))
                (Scheme.tateUnit f (P.kummerCoefficient n) (P.kummerLine n T) U
                  (P.kummerSourceTensor n T U z b x)) =
              P.kummerSourceTensor n T' ((Scheme.proEtaleBaseChange f).obj U)
                (Scheme.tateRingUnit f (P.kummerCoefficient n) U z)
                (Scheme.tateRingUnit f
                  (Padic.coefficientExtensionIntegers P.coefficients.l P.extension) U b)
                (c.hom.app (op U) x)) ∧
          (∀ (U : T.ProEt) (z : (P.kummerRingSheaf n T).obj.obj (op U))
            (y : (Scheme.proEtaleRootsOfUnitySheaf T (P.coefficients.l ^ (N + 1))).obj.obj
              (op U)),
            δ.hom.val.app (op ((Scheme.proEtaleBaseChange f).obj U))
                (Scheme.tateUnit f (P.kummerCoefficient n) (P.kummerRootsTensor n N a T) U
                  (P.kummerTargetTensor n N a T U z y)) =
              P.kummerTargetTensor n N a T' ((Scheme.proEtaleBaseChange f).obj U)
                (Scheme.tateRingUnit f (P.kummerCoefficient n) U z)
                ((Scheme.proEtaleRootsOfUnityDirectImageMap f
                  (P.coefficients.l ^ (N + 1))).hom.app (op U) y)) ∧
          (Scheme.tatePullback f (P.kummerCoefficient n)).map (α T hT).hom ≫ δ.hom =
            β.hom ≫ (α T' hT').hom

/-- Finite Kummer level, with arithmetic, explicit roots tensor, and both compatibilities.
Source: the current blueprint finite Kummer level statement and Stacks Tag 03PK
(blueprint: lem-pur-finite-kummer-level).

Proof: (1) the DVR order writes ell as a unit times varpi^e; since e divides n,
N=n/e is positive and the two power ideals coincide. The normalized logarithmic
valuation is -log(abs(x))/log(ell). A smaller power has smaller uniformizer order,
so cannot annihilate A. (2) O_E is finite free over Z_ell. If its rank is d, its
reduction modulo ell has ell^d elements. Its uniformizer filtration has e quotients,
each of cardinal ell^f, so d=ef. Reduce that basis modulo ell^N to obtain the
displayed linear additive equivalence. (3) The root-limit projection has kernel
ell^N times the limit: when x_N=1, shifting coordinates by N gives its ell^N-th
root in the limit. Thus the induced reduction map is mono. Both its source and
target are locally free rank-one Z/ell^N-lines by the Tate-line lemma. Locally the
map is multiplication by a constant scalar; a nonunit kills the nonzero element
ell^(N-1), contradicting monicity on a nonempty cover member. On empty members both
sheaves are zero. Thus the reduction map is invertible. Tensor with the finite
free Z/ell^N-module A. The associator identifies the iterated integral tensor with
this tensor, and the displayed local formula gives uniqueness. (4) The constant
Z_ell two-term resolution of Z/ell^N, injectivity of ell^N on the root limit, and
the K-flat cone comparison identify derived and ordinary reduction. Tensoring a
K-flat representative with the same comparison gives the displayed quasi-isomorphism.
(5) Pull roots along each fibre-product projection. The root-limit universal property
gives c; tensor with the constant coefficient maps gives beta and delta. Root base
change is invertible by the representable etale root cover. Their tensor reductions
are therefore invertible. Both square composites project x to the same N-th root
and pull back the two scalars, so local tensor generation proves the square. This
includes identity maps and the empty scheme.

The detailed proof dependencies are: lem-weil-l-adic-extension-integers-dvr for (1),
lem-pur-twist-sheaf-locally-free for the finite free scalar module and the finite
root lines in (2)--(3), lem-pur-constant-two-term-resolution together with
lem-pc-kflat-bounded-flat-replacement, lem-pc-bounded-above-flat-kflat-site and
lem-pur-kflat-cone-comparison for (4). In (5), construct the affine root scheme with
lem-sbc-root-split-away-cover-etale and glue it by scheme-morphism-gluing; its
represented sheaf is subcanonical. The inverse-image adjunction, yoneda-hom-bijection
and coyoneda-iso-of-natural-hom-bijection identify the normalized root map with the
representable base-change isomorphism. Then lem-pur-tate-inverse-limit-base-change
and lem-pe-constant-left-module-inverse-image give the scalar-linear limit map and
tensor square. Finally proetale-constant-exact and
lem-weil-pbc-ringed-topoi-derived-tensor-pullback transport that same square to
derived tensor, naturally in every complex.
-/
theorem finiteKummerLevel (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    1 ≤ P.kummerLevel ∧
    P.level = P.ramificationIndex * P.kummerLevel ∧
    (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (P.coefficients.l : P.extension)) / Real.log P.coefficients.l = 1) ∧
    (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
        Real.log P.coefficients.l = (P.ramificationIndex : ℝ)⁻¹) ∧
    (P.level : ℝ) *
      (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
        (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
          Real.log P.coefficients.l) = P.kummerLevel ∧
    Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level =
      Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)) ∧
    (∃ r : P.Ring ≃+* (Padic.coefficientExtensionIntegers P.coefficients.l P.extension ⧸
        Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
            P.coefficients.l P.extension))),
      ∀ x : Padic.coefficientExtensionIntegers P.coefficients.l P.extension,
        r (Ideal.Quotient.mk
          (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level) x) =
        Ideal.Quotient.mk (Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
            P.coefficients.l P.extension))) x) ∧
    (P.exponent : P.Ring) = 0 ∧
    (∀ j : ℕ, ((P.coefficients.l ^ j : ℕ) : P.Ring) = 0 → P.kummerLevel ≤ j) ∧
    ∀ n : ℕ, P.level = n + 1 →
      ∃ N : ℕ, P.kummerLevel = N + 1 ∧
        ∃ a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n,
          ∃ f : ℕ,
            Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
              P.coefficients.l ^ f ∧
            (∃ b : P.kummerCoefficient n ≃+
                (Fin (P.ramificationIndex * f) → ZMod (P.coefficients.l ^ (N + 1))),
              ∀ (z : ZMod (P.coefficients.l ^ (N + 1))) (x : P.kummerCoefficient n),
                b (a z * x) = z • b x) ∧
            ∃ α : ∀ (T : Scheme.{u})
                (_hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
                P.kummerLine n T ≅ P.kummerRootsTensor n N a T,
              (∀ (T : Scheme.{u})
                (hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
                P.IsKummerComparison n N a T (α T hT) ∧
                (∀ γ : P.kummerLine n T ≅ P.kummerRootsTensor n N a T,
                  P.IsKummerComparison n N a T γ → γ = α T hT) ∧
                P.KummerDerivedCompatible n N a T (α T hT)) ∧
              P.KummerBaseChangeCompatible n N a α := by
  sorry

end WeilConjectures.PurityFiniteSetting
