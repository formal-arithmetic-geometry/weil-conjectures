/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteGeometricPurityCoordinates

/-! # The two factors of finite geometric purity in fixed coefficient coordinates

Source: current blueprint, sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.md, (1)--(2).
(blueprint: lem-pur-finite-geometric-purity-factorization).

The orientation factor contains the realization unit, reassociation and inverse Pi.
The tensor factor is the existing theta, followed by the exceptional image of the
inverse realization unit. Their composite is exactly the recorded geometric purity map.
The dualizing exchange is constructed from ordinary exceptional base change at the
coefficient unit, without using either orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The double realization of M, with its specified unit isomorphism from M.
Source: fixed-scalar realization of purity
(blueprint: lem-pur-finite-geometric-purity-factorization).
-/
abbrev geometricPurityRealized (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient))) :=
  (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj M)

section Map
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
variable (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The tensor source before applying theta, retaining the realization coordinates.
Source: base-change factors (2) (blueprint: lem-pur-finite-geometric-purity-factorization). -/
abbrev geometricPurityTensorObject
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient))) :=
  letI : HasCompactification f := (P.geometricPurityCompactification f aY).hasCompactification
  ((smoothPurityTensor P.Coefficient X).obj
    ((P.smoothPurityPullback f).obj (P.geometricPurityRealized Y M))).obj
      (P.diagonalDualizing f)

/-- The existing tensor counit transpose in any specified etale presentation.
Source: base-change factors (2) (blueprint: lem-pur-finite-geometric-purity-factorization). -/
def geometricPurityTensorFactor
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient)))
    (M₀ : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj M₀ ≅
        P.geometricPurityRealized Y M) :
    P.geometricPurityTensorObject f aY M ⟶ (P.smoothPurityExceptionalOver f aY).obj M :=
  letI : HasCompactification f := (P.geometricPurityCompactification f aY).hasCompactification
  P.smoothPurityTheta f (P.geometricPurityRealized Y M) M₀ e ≫
    (P.smoothPurityExceptionalOver f aY).map
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.inv.app M)

/-- Reassociation and tensoring the inverse normalized diagonal orientation.
This factor has no tensor counit transpose.
Source: base-change factors (1) (blueprint: lem-pur-finite-geometric-purity-factorization). -/
def geometricPurityOrientationFactor (d : ℕ) [SmoothOfRelativeDimension d f]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient))) :
    (P.compositionTwistShift X d).obj ((P.smoothPurityPullback f).obj M) ⟶
      P.geometricPurityTensorObject f aY M :=
  letI : HasCompactification f := (P.geometricPurityCompactification f aY).hasCompactification
  (P.smoothPurityPullback f ⋙ P.compositionTwistShift X d).map
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.hom.app M) ≫
    (P.smoothPurityReassociation X d
      ((P.smoothPurityPullback f).obj (P.geometricPurityRealized Y M))).hom ≫
    ((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj (P.geometricPurityRealized Y M))).map
        (P.diagonalDualizingObject d f aY).inv

/-- The unit component of ordinary exceptional base change, in fixed coordinates.
No diagonal orientation is used to construct this map.
Source: base-change factors (1), e_1
(blueprint: lem-pur-finite-geometric-purity-factorization). -/
def geometricPurityDualizingExchange
    (gX : X ⟶ X) (gY : Y ⟶ Y) (sq : IsPullback gX f f gY) :
    letI : HasCompactification f := (P.geometricPurityCompactification f aY).hasCompactification
    (P.smoothPurityPullback gX).obj (P.diagonalDualizing f) ⟶ P.diagonalDualizing f :=
  letI : HasCompactification f := (P.geometricPurityCompactification f aY).hasCompactification
  (P.smoothPurityPullbackComparison gX (P.diagonalDualizing f)
      (P.diagonalOrdinaryDualizing f) (P.diagonalDualizingComparison f).symm).hom ≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app
            (Etale.ordinaryFiniteUnit P.Coefficient Y) ≫
          (Etale.rightDerivedUpperShriek P.Coefficient f).map
            (Etale.ordinaryFiniteUnitPullback P.Coefficient gY).hom) ≫
    (P.diagonalDualizingComparison f).inv

/-- Tensor pullback and the inverse-image square, with exactly the realization units
used by both tensor factors. There is no orientation or exceptional exchange in it.
Source: base-change factors (2), tensor-source comparison
(blueprint: lem-pur-finite-geometric-purity-factorization). -/
def geometricPurityTensorSquare
    (gX : X ⟶ X) (gY : Y ⟶ Y) (w : gX ≫ f = f ≫ gY)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient))) :
    letI : HasCompactification f := (P.geometricPurityCompactification f aY).hasCompactification
    (P.smoothPurityPullback gX).obj (P.geometricPurityTensorObject f aY M) ≅
      ((smoothPurityTensor P.Coefficient X).obj
        ((P.smoothPurityPullback f).obj
          (P.geometricPurityRealized Y ((P.smoothPurityPullback gY).obj M)))).obj
            ((P.smoothPurityPullback gX).obj (P.diagonalDualizing f)) :=
  letI : HasCompactification f := (P.geometricPurityCompactification f aY).hasCompactification
  compositionPullbackTensorFixed P.Ring gX
      ((P.smoothPurityPullback f).obj (P.geometricPurityRealized Y M))
      (P.diagonalDualizing f) ≪≫
    compositionTensorMapIso (smoothPurityTensor P.Coefficient X)
      ((P.smoothPurityPullback gX).mapIso ((P.smoothPurityPullback f).mapIso
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app M).symm) ≪≫
        P.geometricPurityPullbackSquare f gX gY w M ≪≫
        (P.smoothPurityPullback f).mapIso
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app
            ((P.smoothPurityPullback gY).obj M))) (Iso.refl _)

end Map

section Factorization
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The two factors compose to the specified Gamma, for every etale presentation.
Source: definition of smoothPurityMap and base-change factors (1)--(2)
(blueprint: lem-pur-finite-geometric-purity-factorization).
Proof: use the defining presentation equation of the uniquely normalized tensor map.
Expand its tensor-with-inverse-Pi and theta composite. The realization units and
reassociation are precisely those of geometricPurityMap; associativity gives the claim.
-/
theorem geometricPurityMap_factors
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj M))
    (M₀ : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj M₀ ≅
        P.geometricPurityRealized Y M) :
    P.geometricPurityMap f d M hM =
      P.geometricPurityOrientationFactor f (Y ↘ Spec (.of P.field.k)) d M ≫
        P.geometricPurityTensorFactor f (Y ↘ Spec (.of P.field.k)) M M₀ e := by
  have hex := P.existsUnique_smoothPurityTensorMap f d
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj M) hM
  have h := hex.exists.choose_spec M₀ e
  dsimp only [smoothPurityTensorSource] at h
  unfold geometricPurityMap
  rw [h]
  simp only [geometricPurityOrientationFactor, geometricPurityTensorFactor,
    smoothPurityTensorMapInPresentation, geometricPurityRealized, Category.assoc]

end Factorization
end WeilConjectures.PurityFiniteSetting
