/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.PurTwistSheaves
public import Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Paper.TateInverseLimitBaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import Sheaf.Paper.PurInverseImageTensorHomDefinitions

/-! # Definitions for the normalized finite Kummer comparison

The definitions formerly in `PurityFiniteKummerLevel` are unchanged. Their separate
module permits the arithmetic, projection comparison and base-change proofs to be used
independently without an import cycle.
Source: the finite Kummer-level blueprint, (blueprint: lem-pur-finite-kummer-level).
-/

/-! (blueprint: def-pur-kummer-comparison-data) -/

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

end WeilConjectures.PurityFiniteSetting
