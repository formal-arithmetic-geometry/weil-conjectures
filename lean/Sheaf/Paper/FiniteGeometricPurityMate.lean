/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.FiniteGeometricPurityCoordinates
import Sheaf.Paper.FiniteGeometricOrientationExchange
import Sheaf.Paper.FiniteGeometricTensorExchange

/-! # Finite geometric purity and its counit mate.

The coordinate constructions are reexported from FiniteGeometricPurityCoordinates.
(blueprint: lem-pur-finite-geometric-purity-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

section Frobenius
variable (P : PurityFiniteSetting.{u})
variable (X₀ Y₀ : Over (Spec (.of P.field.k₀)))
variable [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
variable [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
variable (f₀ : X₀ ⟶ Y₀)
variable [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
variable (d : ℕ) [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]

/-- Geometric Frobenius purity is the canonical compact-support counit mate, with the
specified roots-of-unity source comparison and its literal inverse-purity formula.
Source: current blueprint equivariance proof, Steps 1--2, and finite-ring purity
base-change factors (blueprint: lem-pur-finite-geometric-purity-mate).

Proof:
1. Use the Cartesian Frobenius square and retag each source structure map by
   Spec gamma. Retagging retains the same separated finite-type schemes and makes
   the four arrows k-morphisms; smoothness and its pure relative dimension persist.
2. The small sites, complexes, compactification, proper/open functors and projection
   words do not change. The counit-preserving right-adjoint identification fixes the
   exceptional functor. Ground-field invariance fixes the diagonal orientation.
3. The tensor purity arrow is the transpose of the same projection/counit word.
   Injectivity of its Hom bijection fixes that arrow, so both purity factors are
   unchanged by retagging, as recorded in geometricPurityRetagging.
4. The coefficient ring is finite and ell^n annihilates it: in the DVR ell is a unit
   times a positive power of the uniformizer. Apply finite-ring compact-support
   base change to the retagged square. Its proper/open formula is exactly B. The
   counit equation identifies the transported exceptional base change with e.
5. Identify the finite root line with the reduction of the integral root line by
   the level-n projection. Finite-general-ring orientation normalization gives
   the same direct-A diagonal orientation and the same tensor formula.
6. Base change of the orientation and of the tensor transpose separately gives
   Q Gamma_K followed by e_K equal to b_K followed by Gamma_(P K).
7. The roots-of-unity inverse-image comparison is transition compatible and is
   the identity on the units of each retained test scheme. Inverse image along
   the scheme isomorphism commutes with the inverse limit. Tensor with O_E,
   reduce to A and take the ordered dth power. This is precisely tau_d: in the
   existing root charts its target root is gamma(zeta), as fixed above. For d=0
   this is the coefficient-unit comparison. There is no further scalar.
8. Finite-coefficient smooth purity makes Gamma_K and Gamma_(P K) invertible.
   Geometric inverse image preserves the bounded constructible finite-Tor domain.
   Cancel Q Gamma_K in the first equality to obtain the second displayed formula.
The inverse is that of the specified Gamma, not an independent map. Empty schemes,
K=0, f=id, d=0, n=1 and ramified E are included. -/
theorem finiteGeometricPurityMate
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hM : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left
      ((Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj M)) :
    IsIso (P.geometricPurityB (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
      (P.frobeniusGaloisMap X₀) (P.frobeniusGaloisMap Y₀)
      (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1
      ((P.smoothPurityExceptionalOver (P.frobeniusMap f₀)
        (P.frobeniusFiber Y₀).hom).obj M)) ∧
    (P.smoothPurityPullback (P.frobeniusGaloisMap X₀)).map
        (P.geometricPurityMap (P.frobeniusMap f₀) d M hM) ≫
      P.geometricPurityMate X₀ Y₀ f₀ M hM =
      (P.geometricPuritySource X₀ Y₀ f₀ d M).hom ≫
        P.geometricPurityMap (P.frobeniusMap f₀) d
          ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M)
          (P.geometricPurityInput Y₀ M hM) ∧
    P.geometricPurityMate X₀ Y₀ f₀ M hM =
      ((P.smoothPurityPullback (P.frobeniusGaloisMap X₀)).mapIso
        (P.geometricPurityIso (P.frobeniusMap f₀) d M hM)).inv ≫
      (P.geometricPuritySource X₀ Y₀ f₀ d M).hom ≫
        P.geometricPurityMap (P.frobeniusMap f₀) d
          ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj M)
          (P.geometricPurityInput Y₀ M hM) := by
  let f := P.frobeniusMap f₀
  let aY := (P.frobeniusFiber Y₀).hom
  let := isNoetherian_of_locallyOfFiniteType aY
  let := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  let : HasCompactification f := inferInstance
  let : CompactSpace (P.frobeniusFiber Y₀).left :=
    QuasiCompact.compactSpace_of_compactSpace aY
  let Q := P.smoothPurityPullback (P.frobeniusGaloisMap X₀)
  let R := P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)
  let E := Scheme.sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring
  have hOrigin := P.geometricPurityOrigin _ M hM
  have hInput := P.geometricPurityInput Y₀ M hM
  have hROrigin := P.geometricPurityOrigin _ (R.obj M) hInput
  have hN : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber Y₀).left
      (P.geometricPurityRealized (P.frobeniusFiber Y₀).left M) :=
    ObjectProperty.prop_of_iso _ (E.unitIso.app M) hOrigin
  have hNR : ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber Y₀).left
      (P.geometricPurityRealized (P.frobeniusFiber Y₀).left (R.obj M)) :=
    ObjectProperty.prop_of_iso _ (E.unitIso.app (R.obj M)) hROrigin
  obtain ⟨M₀, _, ⟨e₀⟩⟩ := hN
  obtain ⟨M₁, _, ⟨e₁⟩⟩ := hNR
  have hGamma := P.geometricPurityMap_factors f d M hM M₀ e₀
  have hGammaR := P.geometricPurityMap_factors f d (R.obj M) hInput M₁ e₁
  change P.geometricPurityMap f d M hM =
    P.geometricPurityOrientationFactor f aY d M ≫
      P.geometricPurityTensorFactor f aY M M₀ e₀ at hGamma
  change P.geometricPurityMap f d (R.obj M) hInput =
    P.geometricPurityOrientationFactor f aY d (R.obj M) ≫
      P.geometricPurityTensorFactor f aY (R.obj M) M₁ e₁ at hGammaR
  have hTensor := P.geometricPurityTensor_exchange X₀ Y₀ f₀ M hM M₀ M₁ e₀ e₁
  have hOrientation := P.geometricPurityOrientation_exchange X₀ Y₀ f₀ d M
  have hSquare : Q.map (P.geometricPurityMap f d M hM) ≫
      P.geometricPurityMate X₀ Y₀ f₀ M hM =
      (P.geometricPuritySource X₀ Y₀ f₀ d M).hom ≫
        P.geometricPurityMap f d (R.obj M) hInput := by
    dsimp only [f, aY, Q, R] at hGamma hGammaR ⊢
    rw [hGamma, Functor.map_comp, Category.assoc, hTensor]
    simpa only [Category.assoc, hGammaR] using
      congrArg (fun k => k ≫
        P.geometricPurityTensorFactor f aY (R.obj M) M₁ e₁) hOrientation
  refine ⟨?_, hSquare, ?_⟩
  · have hG : ProEtale.DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} P.Coefficient) (P.frobeniusFiber X₀).left
        ((P.smoothPurityExceptionalOver f aY).obj M) :=
      ProEtale.plusEtaleOrigin_rightDerivedUpperShriek_obj f hOrigin.plus
    exact P.geometricPurityBIsIsoOfOrigin f aY _ _ _ _ hG
  · let t := Q.mapIso (P.geometricPurityIso f d M hM)
    change P.geometricPurityMate X₀ Y₀ f₀ M hM =
      t.inv ≫ (P.geometricPuritySource X₀ Y₀ f₀ d M).hom ≫
        P.geometricPurityMap f d (R.obj M) hInput
    calc
      _ = t.inv ≫ (t.hom ≫ P.geometricPurityMate X₀ Y₀ f₀ M hM) := by simp
      _ = _ := by rw [show t.hom = Q.map (P.geometricPurityMap f d M hM) from rfl,
        hSquare]

end Frobenius
end WeilConjectures.PurityFiniteSetting
