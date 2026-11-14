/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHomDefinitions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootTowerFiniteTensor
import WeilConjectures.AlgebraicGeometry.SmoothPurity.AmbRootTowerPullbackCoherence
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore

/-! # Root-projection reduction of finite ramified Tate coefficients

Source: Stacks Project, Tags 0990, 090K, 03EK and 03EL.

All levels below are positive: index `r` means exponent `r + 1`, and coefficient
index `n` means quotient by the uniformizer to exponent `n + 1`. Pullback maps
are specified by their direct-image adjuncts. This retains the specified maps,
and expresses their coherence using the actual fibre-product comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ)

/-- The schemes allowed in the statement, including the empty scheme. -/
abbrev AmbTateBase := {T : Scheme.{u} // ∀ x : T, IsUnit (l : T.presheaf.stalk x)}

/-- Admissible positive root exponents, with only the annihilation condition on A. -/
abbrev AmbTateLevel :=
  {r : ℕ // ((l ^ (r + 1) : ℕ) : Padic.coefficientExtensionRing l E (n + 1)) = 0}

/-- Restrict the existing coordinatewise root action to the constant Z_l sheaf. -/
def ambTateConstantRootModule (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (purTwistRing T (purTwistZlConstant T l)) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (purTwistZlCompletionMap T l))).obj (purTwistZlModule T l)

/-- The composite constant scalar map Z_l to O_E to A. -/
def ambTateScalar (T : Scheme.{u}) :
    purTwistZlConstant T l ⟶ WeilConjectures.integralCoefficientCommRingSheaf l E T n :=
  purTwistConstantIntegersMap T l E ≫ purTwistIntegralQuotient T l E n

/-- The ordinary tensor H = L tensor over the constant Z_l sheaf with A. -/
def ambTateReduced (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T n) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (ambTateScalar l E n T) (ambTateConstantRootModule l T)

/-- A pure tensor in H, with the coefficient written first as in change of rings.
Source: Stacks Tag 03EK. -/
def ambTateReducedPure (T : Scheme.{u}) (U : T.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)) :
    (ambTateReduced l E n T).val.obj (op U) :=
  purScalarSection (purTwistZlConstant T l)
    (WeilConjectures.integralCoefficientCommRingSheaf l E T n)
    (ambTateScalar l E n T) (ambTateConstantRootModule l T) U a x

/-- The unique finite scalar map, given by the characteristic divisibility criterion.
Source: Stacks Tag 03EK. -/
def ambTateFiniteScalar (T : Scheme.{u}) (r : AmbTateLevel l E n) :
    purTwistFiniteRing T l r.val ⟶
      WeilConjectures.integralCoefficientCommRingSheaf l E T n :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom
        ((CharP.cast_eq_zero_iff (Padic.coefficientExtensionRing l E (n + 1))
          (ringChar (Padic.coefficientExtensionRing l E (n + 1))) (l ^ (r.val + 1))).mp
            r.property) (Padic.coefficientExtensionRing l E (n + 1))).comp
        ULift.ringEquiv.toRingHom)))

attribute [irreducible] ambTateFiniteScalar

/-- D_r is the recorded finite roots module tensored over the constant Z/l^r with A.
Source: Stacks Tag 03EK. -/
def ambTateFiniteRoots (T : Scheme.{u}) (r : AmbTateLevel l E n) :
    SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T n) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (ambTateFiniteScalar l E n T r) (purTwistRootsModule T l r.val)

/-- Pure tensors in D_r, using the existing sheafification unit.
Source: Stacks Tag 03EK. -/
def ambTateFinitePure (T : Scheme.{u}) (r : AmbTateLevel l E n) (U : T.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r.val + 1))).obj.obj (op U)) :
    (ambTateFiniteRoots l E n T r).val.obj (op U) :=
  purScalarSection (purTwistFiniteRing T l r.val)
    (WeilConjectures.integralCoefficientCommRingSheaf l E T n)
    (ambTateFiniteScalar l E n T r) (purTwistRootsModule T l r.val) U a x

/-- The double pure tensor in the prescribed P = (L tensor O_E) tensor A. -/
def ambTateSourcePure (T : Scheme.{u}) (U : T.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (b : (purTwistIntegralConstant T l E).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)) :
    (purTwistFiniteOne T l E n).val.obj (op U) :=
  purScalarSection (purTwistIntegralConstant T l E)
    (WeilConjectures.integralCoefficientCommRingSheaf l E T n)
    (purTwistIntegralQuotient T l E n) (purTwistIntegralOne T l E) U a
    (purTwistIntegralTensor T l E (op U) b x)

/-- The existing constant-coefficient direct image, with its coefficient type displayed.
Source: Stacks Tag 03D1. -/
def ambTateDirectImage {T T' : Scheme.{u}} (v : T' ⟶ T) :
    SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T' n) ⥤
      SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T n) :=
  proEtaleConstantModuleDirectImage v (Padic.coefficientExtensionRing l E (n + 1))

/-- Evaluation of an adjunct on a local section, exposing its target section type.
Source: Stacks Tag 03D1. -/
def ambTateDirectSection {T T' : Scheme.{u}} (v : T' ⟶ T)
    {M : SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T n)}
    {N : SheafOfModules.{u + 1} (WeilConjectures.integralCoefficientSheaf l E T' n)}
    (f : M ⟶ (ambTateDirectImage l E n v).obj N) (U : T.ProEt)
    (x : M.val.obj (op U)) : N.val.obj (op ((proEtaleBaseChange v).obj U)) :=
  f.val.app (op U) x

/-- The root-projection reduction data, with every map fixed by its specified root or
tensor formula. The fields c and b are the direct-image adjuncts of c_L and b_v, and the
square is the adjunct of the inverse-image base-change square. -/
structure AmbTateRootProjectionData where
  /-- Reassociation for the prescribed finite twist. -/
  j : ∀ T : AmbTateBase l, purTwistFiniteOne T.val l E n ≅ ambTateReduced l E n T.val
  /-- Reassociation is (x tensor b) tensor a to x tensor ba. -/
  j_pure : ∀ (T : AmbTateBase l) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (b : (purTwistIntegralConstant T.val l E).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)),
    (j T).hom.val.app (op U) (ambTateSourcePure l E n T.val U a b x) =
      ambTateReducedPure l E n T.val U
        (a * (purTwistIntegralQuotient T.val l E n).hom.app (op U) b) x
  /-- Projection-induced finite reduction is an isomorphism at every admissible level. -/
  theta : ∀ (T : AmbTateBase l) (r : AmbTateLevel l E n),
    purTwistFiniteOne T.val l E n ≅ ambTateFiniteRoots l E n T.val r
  /-- The precise p_r normalization of theta. -/
  theta_pure : ∀ (T : AmbTateBase l) (r : AmbTateLevel l E n) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)),
    (theta T r).hom.val.app (op U)
        ((j T).inv.val.app (op U) (ambTateReducedPure l E n T.val U a x)) =
      ambTateFinitePure l E n T.val r U a
        ((limit.π (proEtaleRootsOfUnityTower T.val l (Fact.out : l.Prime))
          (op r.val)).hom.app (op U) x)
  /-- Tensor of the power transition, over the different finite coefficient rings. -/
  transition : ∀ (T : AmbTateBase l) (r s : AmbTateLevel l E n) (_h : r.val ≤ s.val),
    ambTateFiniteRoots l E n T.val s ⟶ ambTateFiniteRoots l E n T.val r
  /-- Its normalization on every root tensor. -/
  transition_pure : ∀ (T : AmbTateBase l) (r s : AmbTateLevel l E n) (h : r.val ≤ s.val)
    (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T.val (l ^ (s.val + 1))).obj.obj (op U)),
    (transition T r s h).val.app (op U) (ambTateFinitePure l E n T.val s U a x) =
      ambTateFinitePure l E n T.val r U a
        ((proEtaleRootsOfUnityTransition T.val (l ^ (r.val + 1)) (l ^ (s.val + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
          (pow_dvd_pow l (Nat.add_le_add_right h 1))).hom.app (op U) x)
  /-- Compatibility with theta at all larger levels. -/
  transition_theta : ∀ (T : AmbTateBase l) (r s : AmbTateLevel l E n) (h : r.val ≤ s.val),
    (theta T s).hom ≫ transition T r s h = (theta T r).hom
  /-- Invertibility uses only the annihilation condition in AmbTateLevel. -/
  transition_isIso : ∀ (T : AmbTateBase l) (r s : AmbTateLevel l E n) (h : r.val ≤ s.val),
    IsIso (transition T r s h)
  /-- Identity transition. -/
  transition_id : ∀ (T : AmbTateBase l) (r : AmbTateLevel l E n),
    transition T r r le_rfl = 𝟙 _
  /-- Composition of transitions. -/
  transition_comp : ∀ (T : AmbTateBase l) (r s t : AmbTateLevel l E n)
    (h : r.val ≤ s.val) (k : s.val ≤ t.val),
    transition T s t k ≫ transition T r s h = transition T r t (h.trans k)
  /-- Adjunct of the comparison to the target root limit. -/
  c : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val),
    purTwistZlOne T.val l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T'.val l)
  /-- Every projection agrees with the specified pullback-of-units map. -/
  c_projection : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (s : ℕ),
    c v ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T'.val l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T.val l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))
  /-- Limit uniqueness, equivalently uniqueness of c_L under adjunction. -/
  c_unique : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val)
    (d : purTwistZlOne T.val l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T'.val l)),
    (∀ s : ℕ, d ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T'.val l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T.val l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))) → d = c v
  /-- Adjunct of b_v for the canonical constant-ring module pullback. -/
  b : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val),
    purTwistFiniteOne T.val l E n ⟶
      (ambTateDirectImage l E n v).obj
        (purTwistFiniteOne T'.val l E n)
  /-- Transport of c_L tensor 1 through j, stated on the double pure tensors. -/
  b_pure : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (z : (purTwistIntegralConstant T.val l E).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)),
    ambTateDirectSection l E n v (b v) U (ambTateSourcePure l E n T.val U a z x) =
      ambTateSourcePure l E n T'.val ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U) a)
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionIntegers l E)).hom.app (op U) z)
        ((c v).hom.app (op U) x)
  /-- Adjunct of the tensor of the canonical finite root map with 1. -/
  delta : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (r : AmbTateLevel l E n),
    ambTateFiniteRoots l E n T.val r ⟶
      (ambTateDirectImage l E n v).obj
        (ambTateFiniteRoots l E n T'.val r)
  /-- The specified finite root map, rather than an arbitrary comparison. -/
  delta_pure : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (r : AmbTateLevel l E n)
    (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T.val (l ^ (r.val + 1))).obj.obj (op U)),
    ambTateDirectSection l E n v (delta v r) U (ambTateFinitePure l E n T.val r U a x) =
      ambTateFinitePure l E n T'.val r ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U) a)
        ((proEtaleRootsOfUnityDirectImageMap v (l ^ (r.val + 1))).hom.app (op U) x)
  /-- The displayed base-change square, transposed under the module adjunction. -/
  square : ∀ {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (r : AmbTateLevel l E n),
    b v ≫ (ambTateDirectImage l E n v).map (theta T' r).hom =
      (theta T r).hom ≫ delta v r
  /-- Identity law for c_L, under the canonical identity fibre-product comparison. -/
  c_id : ∀ (T : AmbTateBase l) (U : T.val.ProEt)
    (x : (purTwistZlOne T.val l).obj.obj (op U)),
    (c (𝟙 T.val)).hom.app (op U) x = (purTwistZlOne T.val l).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T.val).hom.app U).op x
  /-- Composition law for c_L, under the canonical iterated pullback comparison. -/
  c_comp : ∀ {T T' T'' : AmbTateBase l} (v : T'.val ⟶ T.val) (w : T''.val ⟶ T'.val)
    (U : T.val.ProEt) (x : (purTwistZlOne T.val l).obj.obj (op U)),
    (c (w ≫ v)).hom.app (op U) x = (purTwistZlOne T''.val l).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      ((c w).hom.app (op ((proEtaleBaseChange v).obj U)) ((c v).hom.app (op U) x))
  /-- Identity law for b_v under the same canonical identity comparison. -/
  b_id : ∀ (T : AmbTateBase l) (U : T.val.ProEt)
    (x : (purTwistFiniteOne T.val l E n).val.obj (op U)),
    ambTateDirectSection l E n (𝟙 T.val) (b (𝟙 T.val)) U x = (purTwistFiniteOne T.val l E n).val.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T.val).hom.app U).op x
  /-- Composition law for b_v under the same canonical iterated pullback comparison. -/
  b_comp : ∀ {T T' T'' : AmbTateBase l} (v : T'.val ⟶ T.val) (w : T''.val ⟶ T'.val)
    (U : T.val.ProEt) (x : (purTwistFiniteOne T.val l E n).val.obj (op U)),
    ambTateDirectSection l E n (w ≫ v) (b (w ≫ v)) U x = (purTwistFiniteOne T''.val l E n).val.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      (ambTateDirectSection l E n w (b w) ((proEtaleBaseChange v).obj U)
        (ambTateDirectSection l E n v (b v) U x))

set_option backward.isDefEq.respectTransparency true
-- The generic scalar-extension API has expensive universe-polymorphic section variables.
set_option linter.unusedSectionVars false

private def ambReassoc (T : AmbTateBase l) :
    purTwistFiniteOne T.val l E n ≅ ambTateReduced l E n T.val :=
  SheafOfModules.scalarExtensionTowerIso.{u + 1, u, u + 1, u + 1}
    (purTwistConstantIntegersMap T.val l E) (purTwistIntegralQuotient T.val l E n)
    (ambTateConstantRootModule l T.val)

private theorem ambReassoc_pure (T : AmbTateBase l) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (b : (purTwistIntegralConstant T.val l E).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)) :
    (ambReassoc l E n T).hom.val.app (op U) (ambTateSourcePure l E n T.val U a b x) =
      ambTateReducedPure l E n T.val U
        (a * (purTwistIntegralQuotient T.val l E n).hom.app (op U) b) x := by
  have h := SheafOfModules.scalarExtensionTowerIso_hom.{u + 1, u, u + 1, u + 1}
    (purTwistConstantIntegersMap T.val l E) (purTwistIntegralQuotient T.val l E n)
    (ambTateConstantRootModule l T.val)
  exact (congrArg (fun f ↦ f.val.app (op U)
    (ambTateSourcePure l E n T.val U a b x)) h).trans
      (SheafOfModules.scalarExtensionTowerForward_tmul.{u + 1, u, u + 1, u + 1}
        (purTwistConstantIntegersMap T.val l E) (purTwistIntegralQuotient T.val l E n)
        (ambTateConstantRootModule l T.val) (op U) a b x)

private local instance ambCoeffAlgebra :
    Algebra ℤ_[l] (Padic.coefficientExtensionRing l E (n + 1)) :=
  ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
    (purTwistIntegersMap l E)).toAlgebra

private theorem ambScalar_eq (T : Scheme.{u}) :
    ambTateScalar l E n T =
      ambRootScalar l (Padic.coefficientExtensionRing l E (n + 1)) T := by
  unfold ambTateScalar purTwistConstantIntegersMap purTwistIntegralQuotient ambRootScalar
  erw [← Functor.map_comp]
  congr 1

private theorem ambFiniteScalar_eq (T : Scheme.{u}) (r : AmbTateLevel l E n) :
    ambTateFiniteScalar l E n T r =
      ambRootFiniteScalar l (Padic.coefficientExtensionRing l E (n + 1))
        r.val r.property T := by
  unfold ambTateFiniteScalar ambRootFiniteScalar
  rfl

private local instance ambLiftCoeffAlgebra :
    Algebra ℤ_[l] (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
  (ULift.ringEquiv.symm.toRingHom.comp
    (algebraMap ℤ_[l] (Padic.coefficientExtensionRing l E (n + 1)))).toAlgebra

private theorem ambTowerScalar_eq (T : Scheme.{u}) :
    rootTowerTensorScalar T l
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) =
      ambTateScalar l E n T := by
  rw [ambScalar_eq]
  unfold rootTowerTensorScalar ambRootScalar
  rfl

private theorem ambTowerFiniteScalar_eq (T : Scheme.{u}) (r : AmbTateLevel l E n) :
    tateFiniteScalar T l (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
      r.val (rootTowerResidueScalar l r.val _
        (show ((l ^ (r.val + 1) : ℕ) :
          ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) = 0 from
          ULift.ext r.property)) = ambTateFiniteScalar l E n T r := by
  unfold tateFiniteScalar rootTowerResidueScalar ambTateFiniteScalar
  apply congrArg ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective x.down
  have hx : x = (z : ULift.{u + 1} (ZMod (l ^ (r.val + 1)))) :=
    ULift.ext hz.symm
  rw [hx]
  exact (map_intCast _ z).trans (map_intCast _ z).symm

private theorem ambScalarIso_exists {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a b : R ⟶ S) (h : a = b)
    (M : SheafOfModules.{u + 1} (purTwistRing T R)) :
    ∃ e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M ≅
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} b M,
      ∀ (U : T.ProEt) (c : S.obj.obj (op U)) (x : M.val.obj (op U)),
        e.hom.val.app (op U) (purScalarSection R S a M U c x) =
          purScalarSection R S b M U c x := by
  subst b
  exact ⟨Iso.refl _, fun _ _ _ ↦ rfl⟩

private def ambHiso (T : Scheme.{u}) :
    ambTateReduced l E n T ≅ ambRootTensor l (Padic.coefficientExtensionRing l E (n + 1)) T :=
  (ambScalarIso_exists _ _ (ambScalar_eq l E n T)
    (ambTateConstantRootModule l T)).choose

private def ambDiso (T : Scheme.{u}) (r : AmbTateLevel l E n) :
    ambTateFiniteRoots l E n T r ≅
      ambRootFiniteTensor l (Padic.coefficientExtensionRing l E (n + 1)) r.val r.property T :=
  (ambScalarIso_exists _ _ (ambFiniteScalar_eq l E n T r)
    (purTwistRootsModule T l r.val)).choose

private theorem ambNormalized_transport {T : Scheme.{u}}
    {R R' S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a a' : R ⟶ S) (b b' : R' ⟶ S) (ha : a = a') (hb : b = b')
    (M : SheafOfModules.{u + 1} (purTwistRing T R))
    (N : SheafOfModules.{u + 1} (purTwistRing T R'))
    (p : ∀ U : T.ProEt, M.val.obj (op U) → N.val.obj (op U))
    (h : ∃ e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M ≅
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} b N,
      ∀ (U : T.ProEt) (c : S.obj.obj (op U)) (x : M.val.obj (op U)),
        e.hom.val.app (op U) (purScalarSection R S a M U c x) =
          purScalarSection R' S b N U c (p U x)) :
    ∃ e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a' M ≅
        SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} b' N,
      ∀ (U : T.ProEt) (c : S.obj.obj (op U)) (x : M.val.obj (op U)),
        e.hom.val.app (op U) (purScalarSection R S a' M U c x) =
          purScalarSection R' S b' N U c (p U x) := by
  subst a'
  subst b'
  exact h

private theorem ambFiniteIso_exists (T : AmbTateBase l) (r : AmbTateLevel l E n) :
    ∃ e : ambTateReduced l E n T.val ≅ ambTateFiniteRoots l E n T.val r,
      ∀ (U : T.val.ProEt)
        (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
        (x : (purTwistZlOne T.val l).obj.obj (op U)),
        e.hom.val.app (op U) (ambTateReducedPure l E n T.val U a x) =
          ambTateFinitePure l E n T.val r U a
            ((rootTowerProjection T.val l r.val).hom.app (op U) x) := by
  apply ambNormalized_transport
    (rootTowerTensorScalar T.val l
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) _
    (tateFiniteScalar T.val l
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) r.val
      (rootTowerResidueScalar l r.val _ (ULift.ext r.property))) _
    (ambTowerScalar_eq l E n T.val) (ambTowerFiniteScalar_eq l E n T.val r)
    (ambTateConstantRootModule l T.val) (purTwistRootsModule T.val l r.val)
    (fun U x ↦ (rootTowerProjection T.val l r.val).hom.app (op U) x)
  exact Exists.imp (fun _ h ↦ h.1)
    ((rootTower_finite_tensor T.val l T.property r.val).2.2.2
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.ext r.property))

private def ambFiniteIso (T : AmbTateBase l) (r : AmbTateLevel l E n) :
    ambTateReduced l E n T.val ≅ ambTateFiniteRoots l E n T.val r :=
  (ambFiniteIso_exists l E n T r).choose

private theorem ambHiso_pure (T : Scheme.{u}) (U : T.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)) :
    (ambHiso l E n T).hom.val.app (op U) (ambTateReducedPure l E n T U a x) =
      ambRootTensorPure l (Padic.coefficientExtensionRing l E (n + 1)) T U a x :=
  (ambScalarIso_exists _ _ (ambScalar_eq l E n T)
    (ambTateConstantRootModule l T)).choose_spec U a x

private theorem ambDiso_pure (T : Scheme.{u}) (r : AmbTateLevel l E n) (U : T.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r.val + 1))).obj.obj (op U)) :
    (ambDiso l E n T r).hom.val.app (op U) (ambTateFinitePure l E n T r U a x) =
      ambRootFinitePure l (Padic.coefficientExtensionRing l E (n + 1))
        r.val r.property T U a x :=
  (ambScalarIso_exists _ _ (ambFiniteScalar_eq l E n T r)
    (purTwistRootsModule T l r.val)).choose_spec U a x

private theorem ambDiso_inv_pure (T : Scheme.{u}) (r : AmbTateLevel l E n)
    (U : T.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r.val + 1))).obj.obj (op U)) :
    (ambDiso l E n T r).inv.val.app (op U)
      (ambRootFinitePure l (Padic.coefficientExtensionRing l E (n + 1))
        r.val r.property T U a x) = ambTateFinitePure l E n T r U a x := by
  rw [← ambDiso_pure]
  exact congrArg (fun f ↦ f.val.app (op U) (ambTateFinitePure l E n T r U a x))
    (ambDiso l E n T r).hom_inv_id

attribute [local irreducible] ambReassoc ambHiso ambDiso

private theorem ambFiniteIso_pure (T : AmbTateBase l) (r : AmbTateLevel l E n)
    (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)) :
    (ambFiniteIso l E n T r).hom.val.app (op U) (ambTateReducedPure l E n T.val U a x) =
      ambTateFinitePure l E n T.val r U a
        ((rootTowerProjection T.val l r.val).hom.app (op U) x) := by
  exact (ambFiniteIso_exists l E n T r).choose_spec U a x

attribute [local irreducible] ambFiniteIso

private local instance ambBaseInvertible (T : AmbTateBase l) :
    ∀ x : T.val, Invertible (l : T.val.presheaf.stalk x) :=
  fun x ↦ (T.property x).invertible

private def ambAlpha (d : AmbRootTowerPullbackCoherence.{u} l)
    (T : AmbTateBase l) (r : AmbTateLevel l E n) :
    ambTateReduced l E n T.val ⟶ ambTateFiniteRoots l E n T.val r :=
  (ambHiso l E n T.val).hom ≫
    d.alpha (Padic.coefficientExtensionRing l E (n + 1)) r.val r.property T.val ≫
    (ambDiso l E n T.val r).inv

private theorem ambPure_hom_ext {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : SheafOfModules.{u + 1} (purTwistRing T R))
    (N : SheafOfModules.{u + 1} (purTwistRing T S))
    (f g : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M ⟶ N)
    (h : ∀ (U : T.ProEt) (c : S.obj.obj (op U)) (x : M.val.obj (op U)),
      f.val.app (op U) (purScalarSection R S a M U c x) =
        g.val.app (op U) (purScalarSection R S a M U c x)) : f = g := by
  apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1} a M f g
  intro U c x
  exact h U.unop c x

attribute [local irreducible] ambAlpha

private theorem ambIso_hom_inv_apply {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (e : M ≅ N) (U : T.ProEtᵒᵖ)
    (x : N.val.obj U) : e.hom.val.app U (e.inv.val.app U x) = x :=
  congrArg (fun f ↦ f.val.app U x) e.inv_hom_id

private theorem ambIso_inv_hom_apply {T : Scheme.{u}}
    {R : Sheaf (ProEt.topology T) RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (e : M ≅ N) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U) : e.inv.val.app U (e.hom.val.app U x) = x :=
  congrArg (fun f ↦ f.val.app U x) e.hom_inv_id

private theorem ambAlpha_eq (d : AmbRootTowerPullbackCoherence.{u} l)
    (T : AmbTateBase l) (r : AmbTateLevel l E n) :
    ambAlpha l E n d T r = (ambFiniteIso l E n T r).hom := by
  refine ambPure_hom_ext (ambTateScalar l E n T.val)
    (ambTateConstantRootModule l T.val) (ambTateFiniteRoots l E n T.val r)
    (ambAlpha l E n d T r) (ambFiniteIso l E n T r).hom ?_
  intro U a x
  change (ambAlpha l E n d T r).val.app (op U)
    (ambTateReducedPure l E n T.val U a x) = _
  unfold ambAlpha
  change (ambDiso l E n T.val r).inv.val.app (op U)
    ((d.alpha (Padic.coefficientExtensionRing l E (n + 1)) r.val r.property T.val).val.app (op U)
      ((ambHiso l E n T.val).hom.val.app (op U)
        (ambTateReducedPure l E n T.val U a x))) = _
  exact ((congrArg ((ambDiso l E n T.val r).inv.val.app (op U))
    ((congrArg
      ((d.alpha (Padic.coefficientExtensionRing l E (n + 1))
        r.val r.property T.val).val.app (op U))
      (ambHiso_pure l E n T.val U a x)).trans
        (d.alpha_pure (Padic.coefficientExtensionRing l E (n + 1))
          r.val r.property T.val U a x))).trans
    (ambDiso_inv_pure l E n T.val r U a _)).trans
      (ambFiniteIso_pure l E n T r U a x).symm

private theorem ambTransition_inclusion (T : Scheme.{u}) (r s : ℕ) (h : r ≤ s) :
    proEtaleRootsOfUnityTransition T (l ^ (r + 1)) (l ^ (s + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.add_le_add_right h 1)) ≫
      proEtaleRootsOfUnityInclusion T (l ^ (r + 1)) =
    proEtaleRootsOfUnityInclusion T (l ^ (s + 1)) ≫
      ((l ^ (s - r)) • 𝟙 (proEtaleUnitsSheaf T)) := by
  have hd : l ^ (s + 1) / l ^ (r + 1) = l ^ (s - r) := by
    rw [← Nat.sub_add_cancel (Nat.add_le_add_right h 1), pow_add,
      Nat.mul_div_cancel _ (pow_pos (Fact.out : l.Prime).pos _)]
    congr 1
    omega
  exact (kernel.lift_ι _ _ _).trans (congrArg
    (fun k ↦ proEtaleRootsOfUnityInclusion T (l ^ (s + 1)) ≫
      (k • 𝟙 (proEtaleUnitsSheaf T))) hd)

private theorem ambTower_inclusion (T : Scheme.{u}) (r s : ℕ) (h : r ≤ s) :
    (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)).map (homOfLE h).op ≫
      proEtaleRootsOfUnityInclusion T (l ^ (r + 1)) =
    proEtaleRootsOfUnityInclusion T (l ^ (s + 1)) ≫
      ((l ^ (s - r)) • 𝟙 (proEtaleUnitsSheaf T)) := by
  induction s, h using Nat.le_induction with
  | base => simp
  | succ s h ih =>
    have hf : (homOfLE (Nat.le_succ s)).op ≫ (homOfLE h).op =
        (homOfLE (Nat.le_trans h (Nat.le_succ s))).op := Subsingleton.elim _ _
    rw [← hf, Functor.map_comp, Category.assoc, ih]
    rw [show (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)).map
      (homOfLE (Nat.le_succ s)).op =
      proEtaleRootsOfUnityTransition T (l ^ (s + 1)) (l ^ (s + 2))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.le_succ (s + 1))) from
          Functor.ofOpSequence_map_homOfLE_succ _ s]
    erw [← Category.assoc, ambTransition_inclusion l T s (s + 1) (Nat.le_succ s)]
    simp only [Preadditive.comp_nsmul, Category.comp_id]
    erw [smul_smul]
    congr 1
    rw [show s + 1 - s = 1 by omega, pow_one,
      show s + 1 - r = (s - r) + 1 by omega, pow_succ]

private theorem ambTower_map (T : Scheme.{u}) (r s : ℕ) (h : r ≤ s) :
    (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)).map (homOfLE h).op =
      proEtaleRootsOfUnityTransition T (l ^ (r + 1)) (l ^ (s + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
        (pow_dvd_pow l (Nat.add_le_add_right h 1)) := by
  have : Mono (proEtaleRootsOfUnityInclusion T (l ^ (r + 1))) :=
    inferInstanceAs (Mono (kernel.ι (proEtaleUnitsPower T (l ^ (r + 1)))))
  apply (cancel_mono (proEtaleRootsOfUnityInclusion T (l ^ (r + 1)))).mp
  exact (ambTower_inclusion l T r s h).trans (ambTransition_inclusion l T r s h).symm

private theorem ambProjection_transition (T : Scheme.{u}) (r s : ℕ) (h : r ≤ s)
    (U : T.ProEt) (x : (purTwistZlOne T l).obj.obj (op U)) :
    (proEtaleRootsOfUnityTransition T (l ^ (r + 1)) (l ^ (s + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.add_le_add_right h 1))).hom.app (op U)
      ((rootTowerProjection T l s).hom.app (op U) x) =
        (rootTowerProjection T l r).hom.app (op U) x := by
  have hh := limit.w (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (homOfLE h).op
  rw [ambTower_map] at hh
  exact congrArg (fun f ↦ f.hom.app (op U) x) hh

private def ambTransition (T : AmbTateBase l) (r s : AmbTateLevel l E n) :
    ambTateFiniteRoots l E n T.val s ⟶ ambTateFiniteRoots l E n T.val r :=
  (ambFiniteIso l E n T s).inv ≫ (ambFiniteIso l E n T r).hom

private theorem ambFinitePure_natural (T : Scheme.{u}) (r : AmbTateLevel l E n)
    {U V : T.ProEt} (f : V ⟶ U)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r.val + 1))).obj.obj (op U)) :
    (ambTateFiniteRoots l E n T r).val.map f.op (ambTateFinitePure l E n T r U a x) =
      ambTateFinitePure l E n T r V
        ((WeilConjectures.integralCoefficientCommRingSheaf l E T n).obj.map f.op a)
        ((proEtaleRootsOfUnitySheaf T (l ^ (r.val + 1))).obj.map f.op x) := by
  exact SheafOfModules.scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
    (ambTateFiniteScalar l E n T r) (purTwistRootsModule T l r.val) f.op a x

private theorem ambTransition_pure (T : AmbTateBase l) (r s : AmbTateLevel l E n)
    (h : r.val ≤ s.val) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T.val (l ^ (s.val + 1))).obj.obj (op U)) :
    (ambTransition l E n T r s).val.app (op U) (ambTateFinitePure l E n T.val s U a x) =
      ambTateFinitePure l E n T.val r U a
        ((proEtaleRootsOfUnityTransition T.val (l ^ (r.val + 1)) (l ^ (s.val + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
          (pow_dvd_pow l (Nat.add_le_add_right h 1))).hom.app (op U) x) := by
  let p := rootTowerProjection T.val l s.val
  have : Sheaf.IsLocallySurjective p :=
    (rootTower_finite_tensor T.val l T.property s.val).1
  apply (ambTateFiniteRoots l E n T.val r).isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem (ProEt.topology T.val) p.hom x)
  intro V f hf
  obtain ⟨y, hy⟩ := hf
  change p.hom.app (op V) y =
    (proEtaleRootsOfUnitySheaf T.val (l ^ (s.val + 1))).obj.map f.op x at hy
  change (ambTateFiniteRoots l E n T.val r).val.map f.op
    ((ambTransition l E n T r s).val.app (op U) _) =
      (ambTateFiniteRoots l E n T.val r).val.map f.op _
  erw [← PresheafOfModules.naturality_apply (ambTransition l E n T r s).val,
    ambFinitePure_natural, ← hy]
  rw [← ambFiniteIso_pure l E n T s V _ y]
  change (ambFiniteIso l E n T r).hom.val.app (op V)
    ((ambFiniteIso l E n T s).inv.val.app (op V)
      ((ambFiniteIso l E n T s).hom.val.app (op V) _)) = _
  erw [ambIso_inv_hom_apply, ambFiniteIso_pure,
    ← ambProjection_transition l T.val r.val s.val h V y]
  rw [hy, ambFinitePure_natural]
  congr 1
  exact NatTrans.naturality_apply
    (proEtaleRootsOfUnityTransition T.val (l ^ (r.val + 1)) (l ^ (s.val + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.add_le_add_right h 1))).hom f.op x

private def ambK (T : AmbTateBase l) :
    purTwistFiniteOne T.val l E n ≅
      ambRootTensor l (Padic.coefficientExtensionRing l E (n + 1)) T.val :=
  ambReassoc l E n T ≪≫ ambHiso l E n T.val

attribute [local irreducible] ambK

private theorem ambK_pure (T : AmbTateBase l) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (b : (purTwistIntegralConstant T.val l E).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)) :
    (ambK l E n T).hom.val.app (op U) (ambTateSourcePure l E n T.val U a b x) =
      ambRootTensorPure l (Padic.coefficientExtensionRing l E (n + 1)) T.val U
        (a * (purTwistIntegralQuotient T.val l E n).hom.app (op U) b) x := by
  unfold ambK
  change (ambHiso l E n T.val).hom.val.app (op U)
    ((ambReassoc l E n T).hom.val.app (op U) _) = _
  rw [ambReassoc_pure, ambHiso_pure]

private def ambTheta (T : AmbTateBase l) (r : AmbTateLevel l E n) :
    purTwistFiniteOne T.val l E n ≅ ambTateFiniteRoots l E n T.val r :=
  ambReassoc l E n T ≪≫ ambFiniteIso l E n T r

private def ambB (d : AmbRootTowerPullbackCoherence.{u} l)
    {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) :
    purTwistFiniteOne T.val l E n ⟶
      (ambTateDirectImage l E n v).obj (purTwistFiniteOne T'.val l E n) :=
  (ambK l E n T).hom ≫ d.h (Padic.coefficientExtensionRing l E (n + 1)) v ≫
    (ambTateDirectImage l E n v).map (ambK l E n T').inv

private def ambDelta (d : AmbRootTowerPullbackCoherence.{u} l)
    {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (r : AmbTateLevel l E n) :
    ambTateFiniteRoots l E n T.val r ⟶
      (ambTateDirectImage l E n v).obj (ambTateFiniteRoots l E n T'.val r) :=
  (ambDiso l E n T.val r).hom ≫
    d.d (Padic.coefficientExtensionRing l E (n + 1)) r.val r.property v ≫
    (ambTateDirectImage l E n v).map (ambDiso l E n T'.val r).inv

attribute [local irreducible] ambB ambDelta

private theorem ambConstant_unit {T T' : Scheme.{u}} (v : T' ⟶ T)
    (A : CommRingCat.{u + 1}) (U : T.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj A)).app U ≫
        (proEtaleConstantDirectImageMap v CommRingCat.{u + 1} A).hom.app U =
      (toSheafify (ProEt.topology T') ((Functor.const T'.ProEtᵒᵖ).obj A)).app
        ((proEtaleBaseChange v).op.obj U) := by
  have h := (sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    ((Functor.const T.ProEtᵒᵖ).obj A)
    ((proEtaleSheafDirectImage v CommRingCat.{u + 1}).obj
      ((constantSheaf (ProEt.topology T') CommRingCat.{u + 1}).obj A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange v).op
      (toSheafify (ProEt.topology T') ((Functor.const T'.ProEtᵒᵖ).obj A)))
  exact congrArg (fun k ↦ k.app U) h

private theorem ambConstant_natural {T T' : Scheme.{u}} (v : T' ⟶ T)
    {A B : CommRingCat.{u + 1}} (f : A ⟶ B) :
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map f ≫
        proEtaleConstantDirectImageMap v CommRingCat.{u + 1} B =
      proEtaleConstantDirectImageMap v CommRingCat.{u + 1} A ≫
        (proEtaleSheafDirectImage v CommRingCat.{u + 1}).map
          ((constantSheaf (ProEt.topology T') CommRingCat.{u + 1}).map f) := by
  apply (sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).homEquiv _ _
    |>.injective
  apply NatTrans.ext
  funext U
  change _ ≫ _ ≫ _ = _ ≫ _ ≫ _
  have h := congrArg (fun k ↦ k.app U)
    ((sheafificationAdjunction (ProEt.topology T) CommRingCat.{u + 1}).unit.naturality
      ((Functor.const T.ProEtᵒᵖ).map f))
  change f ≫ (toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj B)).app U =
    (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj A)).app U ≫
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map f).hom.app U at h
  erw [← Category.assoc, ← h, Category.assoc, ambConstant_unit,
    ← Category.assoc, ambConstant_unit]
  exact congrArg (fun k ↦ k.app ((proEtaleBaseChange v).op.obj U))
    ((sheafificationAdjunction (ProEt.topology T') CommRingCat.{u + 1}).unit.naturality
      ((Functor.const T'.ProEtᵒᵖ).map f))

private theorem ambQuotient_natural {T T' : Scheme.{u}} (v : T' ⟶ T) (U : T.ProEt)
    (z : (purTwistIntegralConstant T l E).obj.obj (op U)) :
    (proEtaleCoefficientDirectImageMap v (Padic.coefficientExtensionRing l E (n + 1))).hom.app
      (op U) ((purTwistIntegralQuotient T l E n).hom.app (op U) z) =
    (purTwistIntegralQuotient T' l E n).hom.app (op ((proEtaleBaseChange v).obj U))
      ((proEtaleCoefficientDirectImageMap v (Padic.coefficientExtensionIntegers l E)).hom.app
        (op U) z) := by
  exact congrArg (fun f ↦ f.hom.app (op U) z)
    (ambConstant_natural v (CommRingCat.ofHom (ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        ULift.ringEquiv.{u, u + 1}.toRingHom))))

private theorem ambB_pure (d : AmbRootTowerPullbackCoherence.{u} l)
    {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (z : (purTwistIntegralConstant T.val l E).obj.obj (op U))
    (x : (purTwistZlOne T.val l).obj.obj (op U)) :
    ambTateDirectSection l E n v (ambB l E n d v) U
      (ambTateSourcePure l E n T.val U a z x) =
      ambTateSourcePure l E n T'.val ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U) a)
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionIntegers l E)).hom.app (op U) z)
        ((d.c v).hom.app (op U) x) := by
  unfold ambTateDirectSection ambB
  change (ambK l E n T').inv.val.app (op ((proEtaleBaseChange v).obj U))
    ((d.h (Padic.coefficientExtensionRing l E (n + 1)) v).val.app (op U)
      ((ambK l E n T).hom.val.app (op U) _)) = _
  have hcoeff :
      (proEtaleCoefficientDirectImageMap v
        (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U)
        (a * (purTwistIntegralQuotient T.val l E n).hom.app (op U) z) =
      (show (WeilConjectures.integralCoefficientCommRingSheaf l E T'.val n).obj.obj
        (op ((proEtaleBaseChange v).obj U)) from
        (proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U) a) *
      (purTwistIntegralQuotient T'.val l E n).hom.app
        (op ((proEtaleBaseChange v).obj U))
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionIntegers l E)).hom.app (op U) z) := by
    exact (map_mul ((proEtaleCoefficientDirectImageMap v
      (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U)).hom a _).trans
        (congrArg (fun y ↦ (show
          (WeilConjectures.integralCoefficientCommRingSheaf l E T'.val n).obj.obj
            (op ((proEtaleBaseChange v).obj U)) from
          (proEtaleCoefficientDirectImageMap v
            (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U) a) * y)
              (ambQuotient_natural l E n v U z))
  have h := (congrArg
    ((d.h (Padic.coefficientExtensionRing l E (n + 1)) v).val.app (op U))
    (ambK_pure l E n T U a z x)).trans
      (d.h_pure (Padic.coefficientExtensionRing l E (n + 1)) v U _ x)
  refine (congrArg ((ambK l E n T').inv.val.app
    (op ((proEtaleBaseChange v).obj U))) h).trans ?_
  erw [hcoeff, ← ambK_pure]
  exact ambIso_inv_hom_apply (ambK l E n T') _ _

private theorem ambDelta_pure (d : AmbRootTowerPullbackCoherence.{u} l)
    {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (r : AmbTateLevel l E n)
    (U : T.val.ProEt)
    (a : (WeilConjectures.integralCoefficientCommRingSheaf l E T.val n).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T.val (l ^ (r.val + 1))).obj.obj (op U)) :
    ambTateDirectSection l E n v (ambDelta l E n d v r) U
      (ambTateFinitePure l E n T.val r U a x) =
      ambTateFinitePure l E n T'.val r ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v
          (Padic.coefficientExtensionRing l E (n + 1))).hom.app (op U) a)
        ((proEtaleRootsOfUnityDirectImageMap v (l ^ (r.val + 1))).hom.app (op U) x) := by
  unfold ambTateDirectSection ambDelta
  change (ambDiso l E n T'.val r).inv.val.app (op ((proEtaleBaseChange v).obj U))
    ((d.d (Padic.coefficientExtensionRing l E (n + 1)) r.val r.property v).val.app (op U)
      ((ambDiso l E n T.val r).hom.val.app (op U) _)) = _
  exact (congrArg ((ambDiso l E n T'.val r).inv.val.app
    (op ((proEtaleBaseChange v).obj U)))
      ((congrArg
        ((d.d (Padic.coefficientExtensionRing l E (n + 1))
          r.val r.property v).val.app (op U))
        (ambDiso_pure l E n T.val r U a x)).trans
          (d.d_pure (Padic.coefficientExtensionRing l E (n + 1))
            r.val r.property v U a x))).trans
    (ambDiso_inv_pure l E n T'.val r _ _ _)

private theorem ambB_id (d : AmbRootTowerPullbackCoherence.{u} l)
    (T : AmbTateBase l) (U : T.val.ProEt)
    (x : (purTwistFiniteOne T.val l E n).val.obj (op U)) :
    ambTateDirectSection l E n (𝟙 T.val) (ambB l E n d (𝟙 T.val)) U x =
      (purTwistFiniteOne T.val l E n).val.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T.val).hom.app U).op x := by
  unfold ambTateDirectSection ambB
  change (ambK l E n T).inv.val.app (op ((proEtaleBaseChange (𝟙 T.val)).obj U))
    ((d.h (Padic.coefficientExtensionRing l E (n + 1)) (𝟙 T.val)).val.app (op U)
      ((ambK l E n T).hom.val.app (op U) x)) = _
  exact (congrArg ((ambK l E n T).inv.val.app
    (op ((proEtaleBaseChange (𝟙 T.val)).obj U)))
      (d.h_id (Padic.coefficientExtensionRing l E (n + 1)) T.val U _)).trans
    ((PresheafOfModules.naturality_apply (ambK l E n T).inv.val
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T.val).hom.app U).op _).trans
        (congrArg ((purTwistFiniteOne T.val l E n).val.map
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T.val).hom.app U).op)
            (ambIso_inv_hom_apply (ambK l E n T) (op U) x)))

private theorem ambB_comp (d : AmbRootTowerPullbackCoherence.{u} l)
    {T T' T'' : AmbTateBase l} (v : T'.val ⟶ T.val) (w : T''.val ⟶ T'.val)
    (U : T.val.ProEt) (x : (purTwistFiniteOne T.val l E n).val.obj (op U)) :
    ambTateDirectSection l E n (w ≫ v) (ambB l E n d (w ≫ v)) U x =
      (purTwistFiniteOne T''.val l E n).val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
        (ambTateDirectSection l E n w (ambB l E n d w) ((proEtaleBaseChange v).obj U)
          (ambTateDirectSection l E n v (ambB l E n d v) U x)) := by
  unfold ambTateDirectSection ambB
  change (ambK l E n T'').inv.val.app (op ((proEtaleBaseChange (w ≫ v)).obj U))
    ((d.h (Padic.coefficientExtensionRing l E (n + 1)) (w ≫ v)).val.app (op U)
      ((ambK l E n T).hom.val.app (op U) x)) = _
  refine (congrArg ((ambK l E n T'').inv.val.app
    (op ((proEtaleBaseChange (w ≫ v)).obj U)))
      (d.h_comp (Padic.coefficientExtensionRing l E (n + 1)) v w U _)).trans ?_
  refine (PresheafOfModules.naturality_apply (ambK l E n T'').inv.val
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      _).trans ?_
  apply congrArg ((purTwistFiniteOne T''.val l E n).val.map
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op)
  change _ = (ambK l E n T'').inv.val.app _
    ((d.h (Padic.coefficientExtensionRing l E (n + 1)) w).val.app _
      ((ambK l E n T').hom.val.app _
        ((ambK l E n T').inv.val.app _
          ((d.h (Padic.coefficientExtensionRing l E (n + 1)) v).val.app _
            ((ambK l E n T).hom.val.app _ x)))))
  exact congrArg (fun y ↦ (ambK l E n T'').inv.val.app _
    ((d.h (Padic.coefficientExtensionRing l E (n + 1)) w).val.app _ y))
    (ambIso_hom_inv_apply (ambK l E n T') _ _).symm

private theorem ambTheta_eq (d : AmbRootTowerPullbackCoherence.{u} l)
    (T : AmbTateBase l) (r : AmbTateLevel l E n) :
    (ambTheta l E n T r).hom = (ambK l E n T).hom ≫
      d.alpha (Padic.coefficientExtensionRing l E (n + 1)) r.val r.property T.val ≫
        (ambDiso l E n T.val r).inv := by
  change (ambReassoc l E n T).hom ≫ (ambFiniteIso l E n T r).hom = _
  rw [← ambAlpha_eq l E n d T r]
  simp only [ambAlpha, ambK, Iso.trans_hom, Category.assoc]

private theorem ambTransport_square {C D : Type*} [Category C] [Category D]
    (F : D ⥤ C) {P H R Q : C} {P' H' R' Q' : D}
    (k : P ≅ H) (k' : P' ≅ H') (z : R ≅ Q) (z' : R' ≅ Q')
    (a : H ⟶ Q) (a' : H' ⟶ Q') (h : H ⟶ F.obj H') (d : Q ⟶ F.obj Q')
    (w : h ≫ F.map a' = a ≫ d) :
    (k.hom ≫ h ≫ F.map k'.inv) ≫ F.map (k'.hom ≫ a' ≫ z'.inv) =
      (k.hom ≫ a ≫ z.inv) ≫ (z.hom ≫ d ≫ F.map z'.inv) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← Category.assoc h (F.map a') (F.map z'.inv), w]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem ambSquare (d : AmbRootTowerPullbackCoherence.{u} l)
    {T T' : AmbTateBase l} (v : T'.val ⟶ T.val) (r : AmbTateLevel l E n) :
    ambB l E n d v ≫ (ambTateDirectImage l E n v).map (ambTheta l E n T' r).hom =
      (ambTheta l E n T r).hom ≫ ambDelta l E n d v r := by
  rw [ambTheta_eq l E n d T r, ambTheta_eq l E n d T' r]
  unfold ambB ambDelta
  exact ambTransport_square (ambTateDirectImage l E n v)
    (ambK l E n T) (ambK l E n T')
    (ambDiso l E n T.val r) (ambDiso l E n T'.val r)
    _ _ _ _ (d.square (Padic.coefficientExtensionRing l E (n + 1))
      r.val r.property v)

/-- Root-projection reduction with arbitrary ramification and annihilated finite coefficients.
Source: Stacks Tags 0990, 090K, 03EK and 03EL.
-/
theorem ambTateRootProjectionReduction :
    Nonempty (AmbTateRootProjectionData l E n) := by
  classical
  obtain ⟨d⟩ := ambRootTowerPullbackCoherence.{u} l
  refine ⟨{
    j := ambReassoc l E n
    j_pure := ambReassoc_pure l E n
    theta := ambTheta l E n
    theta_pure := ?_
    transition := fun T r s _h ↦ ambTransition l E n T r s
    transition_pure := ambTransition_pure l E n
    transition_theta := ?_
    transition_isIso := ?_
    transition_id := ?_
    transition_comp := ?_
    c := fun {_ _} v ↦ d.c v
    c_projection := fun v s ↦ d.c_projection v s
    c_unique := fun v f hf ↦ d.c_unique v f hf
    b := fun {_ _} v ↦ ambB l E n d v
    b_pure := ambB_pure l E n d
    delta := fun {_ _} v r ↦ ambDelta l E n d v r
    delta_pure := ambDelta_pure l E n d
    square := ambSquare l E n d
    c_id := fun T U x ↦ d.c_id T.val U x
    c_comp := fun v w U x ↦ d.c_comp v w U x
    b_id := ambB_id l E n d
    b_comp := ambB_comp l E n d }⟩
  · intro T r U a x
    change (ambFiniteIso l E n T r).hom.val.app (op U)
      ((ambReassoc l E n T).hom.val.app (op U)
        ((ambReassoc l E n T).inv.val.app (op U) _)) = _
    erw [ambIso_hom_inv_apply]
    exact ambFiniteIso_pure l E n T r U a x
  · intro T r s h
    simp [ambTheta, ambTransition, Category.assoc]
  · intro T r s h
    dsimp only [ambTransition]
    infer_instance
  · intro T r
    exact (ambFiniteIso l E n T r).inv_hom_id
  · intro T r s t h k
    simp [ambTransition, Category.assoc]

end AlgebraicGeometry.Scheme
