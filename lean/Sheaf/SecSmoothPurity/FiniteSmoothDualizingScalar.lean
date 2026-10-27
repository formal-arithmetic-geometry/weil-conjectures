/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.SecSmoothPurity.DncCoefficientTransportData

/-! # Smooth dualizing coefficient comparison in ordinary etale coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Invertibility and the counit-normalized chart value of the ordinary dualizing
coefficient map for finite rings killed by a positive prime power invertible on the base.
Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, etale chart argument, and
sk-thm-smooth-purity-general-ring.proof.md, Proof (2), first sentences
(blueprint: lem-pur-finite-smooth-dualizing-scalar).
Proof: identify the intrinsic constructible right adjoints in reductionExceptional_isIso
with the ordinary rightDerivedUpperShriek by their counits, using its realization
clauses. Evaluate at the free rank-one coefficient unit and use the scalar-unit
isomorphism. The result is precisely dualizingScalarMap, since adjunction transposition
is injective. On a chart the same counit is etale summation followed by the ordered
affine trace. The chart clause therefore identifies the map with the specified
root-normalized Tate reassociation. The ordinary coefficient unit is bounded
constructible of finite Tor dimension, so every use of the intrinsic theorem is
on its asserted domain. The free-line calculation uses no flatness of B over A.
Isomorphism detection on the etale chart cover gives the global assertion. -/
theorem finite_smooth_dualizing_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤))) (g : V ⟶ S) [HasCompactification g]
    [IsSeparated g] [QuasiCompact g] (d : ℕ) [SmoothOfRelativeDimension d g] :
    IsIso (ExceptionalCoefficients.dualizingScalarMap φ g) ∧
    ∀ {U : Scheme.{u}} [IsNoetherian U] (i : U ⟶ V) [IsOpenImmersion i]
      (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e]
      [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (he : i ≫ g = e ≫ affineTraceProjection S d)
      (MA : EtaleCompactSupportNormalization A)
      (MB : EtaleCompactSupportNormalization B)
      (tA : OrdinaryFiniteTwistTransport A (ell ^ n) hA)
      (tB : OrdinaryFiniteTwistTransport B (ell ^ n) hB)
      (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum A (ell ^ n) hA tA T hT)
      (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum B (ell ^ n) hB tB T hT),
      (scalarExtension φ U).map
          ((ProEtale.reductionEtaleChartRightIso A MA g i d e he
            (HasCompactification.compactification g)
            (rightDerivedUpperShriek (ModuleCat.{u + 1} A) g)
            (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) g)
            (ell ^ n) hA tA PA hS).hom.app (𝟙_ _)) ≫
        (ProEtale.reductionEtaleChartScalarIso φ (ell ^ n) hA hB hS d e (𝟙_ _)).hom ≫
        (affineTraceRight B (ell ^ n) hB S d ⋙ ordinaryFinitePullback B e).map
          (ExceptionalCoefficients.unitIso φ S).hom =
      (scalarPullbackIso φ i).inv.app (dualizingComplex (ModuleCat.{u + 1} A) g) ≫
        (ordinaryFinitePullback B i).map
          (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) ≫
        (ProEtale.reductionEtaleChartRightIso B MB g i d e he
          (HasCompactification.compactification g)
          (rightDerivedUpperShriek (ModuleCat.{u + 1} B) g)
          (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) g)
          (ell ^ n) hB tB PB hS).hom.app (𝟙_ _) := by sorry

end AlgebraicGeometry.Etale
