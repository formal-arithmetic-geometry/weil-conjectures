/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteGeneralRing
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
import WeilConjectures.SecSmoothPurity.ReductionDirectImage

/-! # The general finite-ring diagonal orientation square

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, Proof (3), Orientation
(blueprint: lem-sp-reduction-dnc-orientation).

The fixed-module presentation below is canonically equivalent to ordinary constant-ring
modules on the original small pro-etale site. Scalar extension is the intrinsic functor
in these coordinates, with its canonical comparison to fixed-module scalar extension.
The ordered line model includes the shift [2d].
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The normalized forward orientation square at the coefficient unit.
Source: sk-lem-sp-reduction-compatibilities.proof.md, Proof (3), Orientation
(blueprint: lem-sp-reduction-dnc-orientation).

The ordinary orientations alphaA and alphaB have the actual diagonal/Rees/integration
normalization of finiteGeneralRingSmoothPurity (1)-(2). The equations for thetaA and
thetaB identify their pro-etale orientations through the canonical dualizing-unit map.
The comparison e is fixed on every root/scalar generator; its ordered tensor power
is precisely the common-exponent Tate scalar comparison followed by the shift.

Proof:
1. Put R=Z/ell^n. By det-sp-finite-general-ring (1)-(2), each stipulated orientation
   thetaS, for S=A,B, satisfies thetaS eS = sRS (alphaR)_S, with eS the canonical
   exceptional scalar comparison at the unit. These are the direct normalized
   orientations, rather than independently chosen trivializations.
2. Apply lem-sp-reduction-composition-transpose to R -> A -> B at R_Y. The transpose
   of cAB (eA)_B is scalar extension of the R-counit after the inverse composite
   compact-support comparison. The cocycle of det-sp-reduction-direct-image makes
   it the transpose of eB. Injectivity of the adjunction Hom equivalence gives
   cAB (eA)_B = eB, including the scalar associator and unit identifications.
3. The Tate comparisons satisfy sAB (sRA)_B = sRB: rank-one lines are flat, so both
   paths are ordinary tensors and send ((z tensor a) tensor b) to z tensor phi(a)b.
   The same formula gives the d-fold tensor identity; at d=0 use the tensor unitor.
   Exact scalar extension respects the common shift and associator naturality.
4. Precompose both sides with the invertible (eA)_B. Substitute the normalization
   at A, the Tate cocycle, the normalization at B, and the exceptional cocycle,
   in that order. Cancel (eA)_B. The displayed presentation comparisons merely
   express the same equality in the fixed-module coordinates.
-/
theorem reductionDncOrientation
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
    (ha : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A) _ _
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
    (hb : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} B) _ _
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
    (thetaA :
      (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} A) f).obj
          (finiteGeneralRingUnit (ULift.{u + 1, u} A) Y) ≅
        (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).obj
          (Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) (ℓ ^ n) hA X d))
    (thetaB :
      (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} B) f).obj
          (finiteGeneralRingUnit (ULift.{u + 1, u} B) Y) ≅
        (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} B) X).obj
          (Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} B) (ℓ ^ n) hB X d))
    (hThetaA : finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f ≫ thetaA.hom =
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map alphaA.hom)
    (hThetaB : finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} B) f ≫ thetaB.hom =
      (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} B) X).map alphaB.hom) :
    (finiteGeneralRingScalar φ X).map thetaA.hom ≫
        (finiteGeneralRingScalarIso φ X
          ((Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).obj
          (Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) (ℓ ^ n) hA X d))).hom ≫
        Etale.FiniteSmoothPurity.proTwistMap d e =
      (finiteGeneralRingScalarIso φ X
          ((Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} A) f).obj
          (finiteGeneralRingUnit (ULift.{u + 1, u} A) Y))).hom ≫
        Etale.FiniteSmoothPurity.proCoefficientMap
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) f
          (finiteGeneralRingUnit (ULift.{u + 1, u} A) Y) ≫
        (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} B) f).map
          (finiteGeneralRingScalarUnitIso
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).hom ≫ thetaB.hom := by
  sorry

end AlgebraicGeometry.ProEtale
