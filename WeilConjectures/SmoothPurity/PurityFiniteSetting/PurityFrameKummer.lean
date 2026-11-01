/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1Decomposition
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal

/-!
# Concrete Kummer classes at every finite level

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
def-pur-frame-class, and the expanded finite-level prescription in the DAG
(blueprint: def-pur-frame-kummer-class).

Kummer classes use the actual Kummer extension at exponent ell^n, followed by
the root scalar-extension unit and exact etale-to-pro-etale inverse image. The
normalized pullback maps retain the local root and pure-tensor formulas.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The existing finite Tate sheaf at the universal annihilator ell^n. In particular
this includes ramified levels not divisible by e. Source: def-pur-frame-class,
coefficient identification (blueprint: def-pur-frame-kummer-class). -/
abbrev frameTwistEtale (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
    P.diagonalExponent_annihilates (d : ℤ)

/-- Its canonical inverse image on the small pro-etale site; this is the finite
root-tensor presentation of A(d), not a chosen trivialization.
Source: def-pur-frame-class, theta (blueprint: def-pur-frame-kummer-class). -/
abbrev frameTwist (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj (P.frameTwistEtale X d)

/-- Scalar extension of the actual Kummer boundary. The module/abelian comparison
is the published bijection, so its inverse selects a uniquely determined class.
Source: def-pur-frame-class, delta and sigma (blueprint: def-pur-frame-kummer-class). -/
def frameKummerEtale (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.constantEtale X) (P.frameTwistEtale X 1) 1 :=
  (Equiv.ofBijective _ (P.moduleClassToAbelian_bijective X (P.frameTwistEtale X 1))).symm
    (Sheaf.H.map (Etale.ordinaryFiniteRootMap P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates X) 1
        (X.kummerδ₀ P.diagonalExponent (P.diagonalExponent_isUnit a) (Additive.ofMul v)))

/-- Exact comparison inverse image of the concrete Kummer class. The root map is
z to 1 tensor z; exact inverse image gives precisely comp followed by sigma rho.
Source: def-pur-frame-class, kappa (blueprint: def-pur-frame-kummer-class). -/
def frameKummer (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.constant X) (P.frameTwist X 1) 1 :=
  (P.frameKummerEtale X a v).mapExactFunctor
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)

/-- The canonical pullback of the constant coefficient unit, including site comparison.
Source: def-pur-frame-class, restriction to the complementary open
(blueprint: def-pur-frame-kummer-class). -/
def frameConstantPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.constant Y) ≅ P.constant X :=
  (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient) f).app
      (P.constantEtale Y) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).app
        (ModuleCat.of P.Coefficient P.Coefficient))

/-- The root-normalized finite-twist comparison supplied by the published theorem.
Its kernel-inclusion and pure-tensor formulas determine these maps uniquely. No
root of unity or unspecified isomorphism is chosen.
Source: def-pur-frame-class, restriction through roots and tensors
(blueprint: def-pur-frame-kummer-class). -/
def frameEtalePullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.frameTwistEtale Y d) ≅
      P.frameTwistEtale X d :=
  Etale.p1DecompositionSheafPullback P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates f (P.diagonalExponent_isUnit a) d

/-- The same normalized comparison on the small pro-etale sites.
Source: def-pur-frame-class, restriction of A(1) (blueprint: def-pur-frame-kummer-class). -/
def frameTwistPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.frameTwist Y d) ≅
      P.frameTwist X d :=
  (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient) f).app
      (P.frameTwistEtale Y d) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapIso
      (P.frameEtalePullback f a d)

end WeilConjectures.PurityFiniteSetting
