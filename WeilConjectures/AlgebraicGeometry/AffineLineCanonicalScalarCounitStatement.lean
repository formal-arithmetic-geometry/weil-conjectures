/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility2
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartP1CounitScalar
import WeilConjectures.AlgebraicGeometry.AffineLineBetaCompactScalarNormalization
import WeilConjectures.AlgebraicGeometry.AffineLineBetaOpenMapNormalization
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.OrdinaryScalarSiteComparisons
import all WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import all WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import all WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenDerivedConjugate

/-! # Canonical affine-line scalar counit over the corrected field domain

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md`, Charts, iterated projective-line integration
(blueprint: lem-sp-affine-line-canonical-scalar-counit).

The coefficient arrow is the specified proper counit mate followed by the canonical
open scalar comparison. The right comparison is the existing root-normalized one.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The root-normalized comparison for one affine coordinate respects the actual
standard open/projective composite counit over a finite or algebraically closed field.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md`, Charts, iterated projective-line integration
(blueprint: lem-sp-affine-line-canonical-scalar-counit).

Proof plan: Since char(k) differs from ell, ell and its powers are units on T.
Apply the composite-adjunction counit identity to the standard open chart and the
normalized projective-line adjunction. The open scalar square is the counit equation
of the scalar/pullback mate. The projective square is lem-sp-p1-counit-scalar with
its Kummer-normalized trace. The equal-annihilator root map fixes the Tate generators,
so its derived adjunct is reductionEtaleTateExtensionMap and the right comparison
is exactly reductionEtaleLineScalarIso. Expand the composite counit, use naturality
to move the projective right comparison past the open counit, and apply these two
squares. The proper coefficient mate followed by the open scalar comparison is
precisely beta for affineTraceLineCompactification. This gives the stated equation.
The finite-Tor constructibility condition retains the intended chart domain;
no flatness of B over A is used. -/
theorem affineLineCanonicalScalarCounitOfField
    (ell n : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (_hchar : ringChar k ≠ ell)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] :
    ∃ hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤)),
      ∀ (tA : OrdinaryFiniteTwistTransport A (ell ^ n) hA)
        (tB : OrdinaryFiniteTwistTransport B (ell ^ n) hB)
        (dA : OrdinaryFiniteP1Datum A (ell ^ n) hA tA T hT)
        (dB : OrdinaryFiniteP1Datum B (ell ^ n) hB tB T hT)
        (K : DerivedCategoryModule A T)
        (_hK : ProEtale.CoefficientCompatibility.Input A T K),
      (ProEtale.CoefficientCompatibility.beta φ (affineTraceLineCompactification T)).app
          ((affineTraceLineRight A (ell ^ n) hA T).obj K) ≫
        (affineTraceLineLeft B T).map
          (ProEtale.reductionEtaleLineScalarIso φ T (ell ^ n) hA hB hT K).hom ≫
        (affineTraceLineAdjunction B (ell ^ n) hB tB T hT dB).counit.app
          ((scalarExtension φ T).obj K) =
      (scalarExtension φ T).map
        ((affineTraceLineAdjunction A (ell ^ n) hA tA T hT dA).counit.app K) := by
  have hne : (ell : k) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime) _hchar
  have hu := (isUnit_iff_ne_zero.mpr (pow_ne_zero n hne)).map
    (Scheme.ΓSpecIso (.of k)).inv.hom
  have hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤)) := by
    simpa only [map_pow, map_natCast, Nat.cast_pow] using
      hu.map (T ↘ Spec (.of k)).appTop.hom
  refine ⟨hT, ?_⟩
  intro tA tB dA dB K hK
  let : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  let : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace
    (T ↘ Spec (.of k))
  let : IsNoetherian T := ⟨⟩
  have h := line_scalar_counit φ (ell ^ n)
    (pow_pos (Fact.out : ell.Prime).pos n) hA hB T hT tA tB dA dB K
  rw [affineLineBetaCompactScalarNormalization]
  exact h

end AlgebraicGeometry.Etale
