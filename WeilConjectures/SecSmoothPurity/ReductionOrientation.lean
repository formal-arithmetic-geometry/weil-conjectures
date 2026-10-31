/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteGeneralRing
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteNormalizedOrientationScalar

/-! # Coefficient change of the normalized inverse smooth orientation

Source: smooth-purity coefficient compatibilities, proof (3), Orientation.
(blueprint: lem-sp-reduction-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- Inverse diagonal orientations commute with finite coefficient change.
Source: sk-lem-sp-reduction-compatibilities.proof.md (3), Orientation, and
sk-thm-smooth-purity-general-ring, clauses (1)-(2).
(blueprint: lem-sp-reduction-orientation).

Proof: use the common exponent n and the unital chain Z/ell^n -> A -> B.
The general-ring orientation theorem identifies each normalized direct orientation
with extension of the prime-power diagonal orientation. Apply the cocycle for
counit-defined exceptional coefficient mates at the coefficient unit to this chain.
The scalar unit and tensor associators identify the two resulting dualizing maps.
The generator normalization of e identifies its ordered root-line tensor comparison
with the same scalar associator. Substitute both common-origin equations and cancel
the prime-power comparison to obtain the displayed inverse-orientation equation.
The identification with each supplied normalized orientation follows from uniqueness
of the t=1-normalized Rees comparison and the integration-normalized bundle factor.
This includes d=0 (unit tensors), the zero ring, and empty schemes; no flatness of
B over A is used. -/
theorem reductionOrientation
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasCompactification f]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (hn : 1 ≤ n)
    (hA : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} A) = 0)
    (hB : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} B) = 0)
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alphaA : Etale.dualizingComplex (ULift.{u + 1, u} A) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) (ℓ ^ n) hA X d)
    (alphaB : Etale.dualizingComplex (ULift.{u + 1, u} B) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} B) (ℓ ^ n) hB X d)
    (_ha : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A) _ _
      (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n) hA X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
          (X ↘ Spec (.of D.k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
          (X ↘ Spec (.of D.k)) } f _
      (@quasiCompact_of_compactSpace X Y f
        (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
        (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))) _ d geometry
      ((finiteGeneralRingPrimeSetting D ℓ hℓ n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) alphaA)
    (_hb : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} B) _ _
      (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n) hB X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
          (X ↘ Spec (.of D.k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
          (X ↘ Spec (.of D.k)) } f _
      (@quasiCompact_of_compactSpace X Y f
        (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
        (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))) _ d geometry
      ((finiteGeneralRingPrimeSetting D ℓ hℓ n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) alphaB)
    (e : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ℓ ^ n) (ℓ ^ n) hA hB X)
 :
    (Etale.FiniteSmoothPurity.ordinaryScalar
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).map alphaA.inv ≫
        Etale.ExceptionalCoefficients.dualizingScalarMap
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) f =
      (e.tensorPower d).hom ≫ alphaB.inv := by
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (X ↘ Spec (.of D.k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (X ↘ Spec (.of D.k)) }
  let : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (Y ↘ Spec (.of D.k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (Y ↘ Spec (.of D.k)) }
  let : QuasiCompact f :=
    @quasiCompact_of_compactSpace X Y f
      (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
      (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))
  exact Etale.FiniteSmoothPurity.normalizedOrientation_scalar
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ℓ ^ n) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (pow_pos (Fact.out : ℓ.Prime).pos n)
    (dvd_refl _) hA hB
    ((finiteGeneralRingPrimeSetting D ℓ hℓ n hn).diagonalExponent_isUnit
      (Y ↘ Spec (.of D.k))) f d geometry
    ((finiteGeneralRingPrimeSetting D ℓ hℓ n hn).diagonalExponent_isUnit
      (X ↘ Spec (.of D.k)))
    ((finiteGeneralRingPrimeSetting D ℓ hℓ n hn).diagonalExponent_isUnit
      (X ↘ Spec (.of D.k))) alphaA alphaB _ha _hb e

end AlgebraicGeometry.ProEtale
