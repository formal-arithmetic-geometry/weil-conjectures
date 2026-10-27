/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FixedFinitePositiveCoefficientTwist
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.AlgebraicGeometry.FiniteRootSiteComparison
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Data for evaluation-normalized signed finite Tate site comparison

Source: Stacks Project, Tags 07A4, 03EL, 0GMX and 0FNY; the root-normalized signed
refinement of the coefficient identification in def-pur-frame-class
(blueprint: lem-pur-signed-twist-site-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- The existing quotient at positive level n+1, in the common sheaf universe.
Source: def-pur-conventions, A=O_E/(varpi^n)
(blueprint: lem-pur-signed-twist-site-transport). -/
abbrev signedSiteCoefficient (P : PurityFiniteSetting.{u}) (n : ℕ) :=
  finiteTateCoefficient P.coefficients.l P.extension n

/-- The specified integer tensor/dual powers on the small etale site.
Source: lem-asd-etale-finite-twist-pullback
(blueprint: lem-pur-signed-twist-site-transport). -/
abbrev signedSiteEtale (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (X : Scheme.{u}) (r : ℤ) :=
  finiteEtaleTateSheaf (P.signedSiteCoefficient n) (P.coefficients.l ^ (n + 1)) X hA r

/-- The actual specified pro-etale twist, with its constant scalar action retained.
Source: def-coefficient-twists-detailed and finiteTateConstantRestriction
(blueprint: lem-pur-signed-twist-site-transport). -/
abbrev signedSitePro (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) (r : ℤ) :=
  (finiteTateConstantRestriction P.coefficients.l P.extension n X).obj
    (finiteCoefficientTwist P.coefficients.l P.extension X n r)

/-- The actual pro-etale module before constant-scalar restriction.
Source: def-coefficient-twists-detailed, signed finite line
(blueprint: lem-pur-signed-twist-site-transport). -/
abbrev signedSiteModule (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) (r : ℤ) :=
  finiteCoefficientTwist P.coefficients.l P.extension X n r

/-- A pulled section on an arbitrary pro-etale test over an etale object, using the
actual comparison-adjunction unit and restriction. Source: Stacks 0GLZ
(blueprint: lem-pur-signed-twist-site-transport). -/
def signedSiteImage (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (X : Scheme.{u}) (r : ℤ) (U : X.Etaleᵒᵖ) (W : X.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt X).obj U.unop)
    (x : (P.signedSiteEtale n hA X r).obj.obj U) :
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
      (P.signedSiteEtale n hA X r)).obj.obj W :=
  ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
    (P.signedSiteEtale n hA X r)).obj.map f.op
      (((ProEtale.comparisonAdjunction
        (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).unit.app
          (P.signedSiteEtale n hA X r)).hom.app U x)

/-- Evaluation in the existing etale closed monoidal category, on a pure tensor.
The order of ihom.ev is positive then dual; the symmetry gives the dual-first
pairing of the node. Source: Stacks 03EO and 0FNY
(blueprint: lem-pur-signed-twist-site-transport). -/
def signedSiteEtaleEvaluation (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (X : Scheme.{u}) (d : ℕ) (U : X.Etaleᵒᵖ)
    (φ : (P.signedSiteEtale n hA X (.negSucc d)).obj.obj U)
    (x : (P.signedSiteEtale n hA X (.ofNat (d + 1))).obj.obj U) :
    (P.signedSiteEtale n hA X 0).obj.obj U :=
  (((ihom.ev (P.signedSiteEtale n hA X (.ofNat (d + 1)))).app
    (P.signedSiteEtale n hA X 0)).hom.app U)
      ((Functor.LaxMonoidal.μ
        (sheafToPresheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (P.signedSiteCoefficient n)))
        (P.signedSiteEtale n hA X (.ofNat (d + 1)))
        (P.signedSiteEtale n hA X (.negSucc d))).app U (x ⊗ₜ[_] φ))

/-- Evaluation of the actual slice sheaf Hom defining the negative pro-etale power.
Source: Stacks 0GMX and 0FNY (blueprint: lem-pur-signed-twist-site-transport). -/
def signedSiteProEvaluation (P : PurityFiniteSetting.{u}) (n : ℕ)
    (X : Scheme.{u}) (d : ℕ) (W : X.ProEtᵒᵖ)
    (φ : (P.signedSitePro n X (.negSucc d)).obj.obj W)
    (x : (P.signedSitePro n X (.ofNat (d + 1))).obj.obj W) :
    (P.signedSitePro n X 0).obj.obj W :=
  φ.app (op (Over.mk (𝟙 W.unop))) x

/-- The evaluation equation characterizing each negative site comparison, on all
local sections and after every restriction to a pro-etale test.
Source: Stacks 0GMX and 0FNY (blueprint: lem-pur-signed-twist-site-transport). -/
def SignedSiteEvaluation (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (q : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X r) ≅ P.signedSitePro n X r) : Prop :=
  ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (d : ℕ)
    (U : X.Etaleᵒᵖ) (W : X.ProEtᵒᵖ) (f : W.unop ⟶ (toProEt X).obj U.unop)
    (φ : (P.signedSiteEtale n hA X (.negSucc d)).obj.obj U)
    (x : (P.signedSiteEtale n hA X (.ofNat (d + 1))).obj.obj U),
    P.signedSiteProEvaluation n X d W
      ((q X a (.negSucc d)).hom.hom.app W (P.signedSiteImage n hA X _ U W f φ))
      ((q X a (.ofNat (d + 1))).hom.hom.app W (P.signedSiteImage n hA X _ U W f x)) =
    (q X a 0).hom.hom.app W
      (P.signedSiteImage n hA X 0 U W f (P.signedSiteEtaleEvaluation n hA X d U φ x))

/-- The intrinsic ordered product on every signed power, with the same coefficient
ring sheaf as the prescribed twists. Source: Stacks 03EK, 0FNY
(blueprint: lem-pur-signed-twist-site-transport). -/
abbrev SignedSiteProducts (P : PurityFiniteSetting.{u}) (n : ℕ) :=
  ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (r s : ℤ),
    (SheafOfModules.siteSheafTensorRight (P.signedSiteModule n X s)).obj
      (P.signedSiteModule n X r) ≅ P.signedSiteModule n X (r + s)

/-- The multiplication square on pure tensors after arbitrary local restriction.
Source: Stacks 03EL; node proof Step 3
(blueprint: lem-pur-signed-twist-site-transport). -/
def SignedSiteMultiplication (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hlevel : P.level = n + 1)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (μ : P.SignedSiteProducts n)
    (q : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X r) ≅ P.signedSitePro n X r) : Prop :=
  ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (r s : ℤ)
    (U : X.Etaleᵒᵖ) (W : X.ProEtᵒᵖ) (f : W.unop ⟶ (toProEt X).obj U.unop)
    (x : (P.signedSiteEtale n hA X r).obj.obj U)
    (y : (P.signedSiteEtale n hA X s).obj.obj U),
    (q X a (r + s)).hom.hom.app W
      (P.signedSiteImage n hA X _ U W f
        ((((finiteEtaleTwistPullbackData (P.signedSiteCoefficient n)
          (P.coefficients.l ^ (n + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA).p X
          (by simpa [diagonalExponent, hlevel]
            using P.diagonalExponent_isUnit a) r s).hom.hom.app U)
          ((Functor.LaxMonoidal.μ
            (sheafToPresheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} (P.signedSiteCoefficient n)))
            (P.signedSiteEtale n hA X r) (P.signedSiteEtale n hA X s)).app U
              (x ⊗ₜ[_] y)))) =
    (μ X a r s).hom.val.app W
      (SheafOfModules.siteSheafTensorTmul
        (P.signedSiteModule n X r) (P.signedSiteModule n X s) W
        ((q X a r).hom.hom.app W (P.signedSiteImage n hA X r U W f x))
        ((q X a s).hom.hom.app W (P.signedSiteImage n hA X s U W f y)))
/-- A geometric pullback family in the fixed coefficient presentation.
Source: Stacks 03EL, 0GMX (blueprint: lem-pur-signed-twist-site-transport). -/
abbrev SignedSiteGeometric (P : PurityFiniteSetting.{u}) (n : ℕ) :=
  ∀ {X X' : Scheme.{u}} (v : X' ⟶ X) (_a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
    (ProEtale.upperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) v).obj
      (P.signedSitePro n X r) ≅ P.signedSitePro n X' r

/-- Adjunct section of geometric pullback; no interchange with an infinite limit.
Source: Stacks 09A5 and 0GMX (blueprint: lem-pur-signed-twist-site-transport). -/
def signedSiteGeometricSection (P : PurityFiniteSetting.{u}) (n : ℕ)
    (τ : P.SignedSiteGeometric n) {X X' : Scheme.{u}} (v : X' ⟶ X)
    (a : X ⟶ Spec (.of P.field.k)) (r : ℤ) (U : X.ProEtᵒᵖ)
    (x : (P.signedSitePro n X r).obj.obj U) :
    (P.signedSitePro n X' r).obj.obj ((proEtaleBaseChange v).op.obj U) :=
  ((ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) v).homEquiv _ _
      (τ v a r).hom).hom.app U x

/-- Root pullback for nonnegative degrees, dual evaluation for negative degrees,
and the canonical identity and composition laws for the resulting family.
Source: Stacks 03EL, 0GMX and 09A5; node proof Step 4
(blueprint: lem-pur-signed-twist-site-transport). -/
def SignedSiteGeometricLaws (P : PurityFiniteSetting.{u}) (n : ℕ)
    (τ : P.SignedSiteGeometric n) : Prop :=
  (∀ {X X' : Scheme.{u}} (v : X' ⟶ X) (a : X ⟶ Spec (.of P.field.k)) (k : ℕ),
    IsFiniteTateProPullback P.coefficients.l P.extension n X v k (τ v a k)) ∧
  (∀ {X X' : Scheme.{u}} (v : X' ⟶ X) (a : X ⟶ Spec (.of P.field.k))
    (d : ℕ) (U : X.ProEtᵒᵖ)
    (φ : (P.signedSitePro n X (.negSucc d)).obj.obj U)
    (x : (P.signedSitePro n X (.ofNat (d + 1))).obj.obj U),
    P.signedSiteProEvaluation n X' d ((proEtaleBaseChange v).op.obj U)
      (P.signedSiteGeometricSection n τ v a (.negSucc d) U φ)
      (P.signedSiteGeometricSection n τ v a (.ofNat (d + 1)) U x) =
    P.signedSiteGeometricSection n τ v a 0 U (P.signedSiteProEvaluation n X d U φ x)) ∧
  (∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
    τ (𝟙 X) a r =
      (ProEtale.upperStarId (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).app
        (P.signedSitePro n X r)) ∧
  (∀ {X X' X'' : Scheme.{u}} (v : X' ⟶ X) (w : X'' ⟶ X')
    (a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
    τ (w ≫ v) a r =
      (ProEtale.upperStarComp (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) w v).app
        (P.signedSitePro n X r) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) w).mapIso
        (τ v a r) ≪≫ τ w (v ≫ a) r)

/-- The negative scheme-pullback square with the actual canonical comparison mate
and the root/evaluation-normalized etale comparison. Source: Stacks 03EL, 0GMX
(blueprint: lem-pur-signed-twist-site-transport). -/
def SignedSitePullbackSquare (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hlevel : P.level = n + 1)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (τ : P.SignedSiteGeometric n)
    (q : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X r) ≅ P.signedSitePro n X r) : Prop :=
  ∀ {X X' : Scheme.{u}} (v : X' ⟶ X) (a : X ⟶ Spec (.of P.field.k)) (d : ℕ),
    (ProEtale.upperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) v).mapIso
      (q X a (.negSucc d)) ≪≫ τ v a (.negSucc d) =
    (ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) v).app
        (P.signedSiteEtale n hA X (.negSucc d)) ≪≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X').mapIso
        ((finiteEtaleTwistPullbackData (P.signedSiteCoefficient n)
          (P.coefficients.l ^ (n + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA).c v
            (by simpa [diagonalExponent, hlevel] using P.diagonalExponent_isUnit a)
            (by simpa [diagonalExponent, hlevel] using P.diagonalExponent_isUnit (v ≫ a))
            (.negSucc d)) ≪≫ q X' (v ≫ a) (.negSucc d)

/-- The projection-induced theta, in the published constant-scalar presentation.
Source: def-pur-frame-class and lem-amb-tate-root-projection-reduction
(blueprint: lem-pur-signed-twist-site-transport). -/
abbrev SignedSiteTheta (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0) :=
  ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)),
    P.signedSitePro n X 1 ≅ finiteRootProTensor (P.signedSiteCoefficient n)
      (P.coefficients.l ^ (n + 1)) (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA X

/-- The defining projection formula for theta on every local root-limit tensor.
Source: def-pur-frame-class, theta(z tensor a)=pi_n(z) tensor a
(blueprint: lem-pur-signed-twist-site-transport). -/
def SignedSiteThetaNormalized (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (θ : P.SignedSiteTheta n hA) : Prop :=
  ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (W : X.ProEtᵒᵖ)
    (c : P.signedSiteCoefficient n) (x : (purTwistZlOne X P.coefficients.l).obj.obj W),
    (θ X a).hom.hom.app W (finiteTateProGenerator P.coefficients.l P.extension n X W c x) =
      finiteRootProGenerator (P.signedSiteCoefficient n) (P.coefficients.l ^ (n + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA X W c
        ((limit.π (proEtaleRootsOfUnityTower X P.coefficients.l
          (Fact.out : P.coefficients.l.Prime)) (op n)).hom.app W x)

/-- Equality with the precise sigma_X c_m,X coefficient map, on every local root.
It is an equality of sheaf morphisms, tested on adjunction-unit sections and all
restrictions, before applying cohomology. Source: def-pur-frame-class
(blueprint: lem-pur-signed-twist-site-transport). -/
def SignedSiteRootCoefficient (P : PurityFiniteSetting.{u}) (n : ℕ)
    (hlevel : P.level = n + 1)
    (hA : ((P.coefficients.l ^ (n + 1) : ℕ) : P.signedSiteCoefficient n) = 0)
    (θ : P.SignedSiteTheta n hA)
    (q : ∀ (X : Scheme.{u}) (_a : X ⟶ Spec (.of P.field.k)) (r : ℤ),
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (P.signedSiteCoefficient n)) X).obj
        (P.signedSiteEtale n hA X r) ≅ P.signedSitePro n X r) : Prop :=
  ∀ (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k))
    (U : X.Etaleᵒᵖ) (W : X.ProEtᵒᵖ) (f : W.unop ⟶ (toProEt X).obj U.unop)
    (z : (X.rootsOfUnitySheaf (P.coefficients.l ^ (n + 1))).obj.obj U),
    (q X a 1).hom.hom.app W
      (P.signedSiteImage n hA X 1 U W f
        (finiteEtaleTateOneGenerator (P.signedSiteCoefficient n)
          (P.coefficients.l ^ (n + 1)) X hA U 1 z)) =
    (θ X a).inv.hom.app W
      (finiteRootProGenerator (P.signedSiteCoefficient n) (P.coefficients.l ^ (n + 1))
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA X W 1
        ((ProEtale.cartierRootsIso X (P.coefficients.l ^ (n + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
          (by simpa [diagonalExponent, hlevel] using P.diagonalExponent_isUnit a)).hom.hom.app W
          (((ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} X).obj
            (X.rootsOfUnitySheaf (P.coefficients.l ^ (n + 1)))).obj.map f.op
              (((ProEtale.comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
                (X.rootsOfUnitySheaf (P.coefficients.l ^ (n + 1)))).hom.app U z))))

end WeilConjectures.PurityFiniteSetting
