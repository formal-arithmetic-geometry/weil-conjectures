/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.FiniteGeneralRingData

/-! # Coefficient transport of the direct smooth orientation 
Source: general-ring smooth purity, proof (1)-(3).
(blueprint: lem-sp-general-ring-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Scalar extension of the prime-power orientation agrees with the direct ordinary
orientation after the canonical unit comparison.

Source: general-ring smooth purity, proof (1) and (2), including the diagonal,
normalized Rees specialization and vector-integration comparisons
(blueprint: lem-sp-general-ring-orientation).

Proof: identify the bottom-extension level-n ring with Z/ell^n and use the unital
map to A. The free-line scalar comparison, fixed on scalar/root generators, gives t.
Apply reductionExceptional_isIso at the coefficient unit. Its counit equation and
its chart normalization identify this comparison with finiteGeneralRingReduction;
its two outer scalar-presentation and scalar-unit factors are isomorphisms.
The ordinary/pro-etale adjunction comparison is counit-preserving, and the
comparison-adjunction unit at the ordinary unit is invertible; applying the
ordinary exceptional functor and comparison gives the asserted invertible unit map.
Construct the direct ordinary orientation alpha from the smooth diagonal, its
actual Rees family, and the normal bundle integration adjunct. The diagonal is a
closed section of the smooth first projection and its conormal bundle has rank d,
so it supplies geometry also for d=0. Pullback and base-change coefficient mates
identify the diagonal factors. The t=1 uniqueness in dncCoefficientTransport
identifies Rees specialization. On vector-bundle charts coefficient extension
preserves the ordered affine counit and the Kummer-normalized projective-line trace.
Derived single full faithfulness and sheaf Hom gluing identify integration globally.
Thus alpha satisfies OrientationNormalized, and the three commuting squares give
the displayed equation with the scalar extension of diagonalDualizingObject.
For d=0 all ordered tensors and integration factors are identities. The zero ring
and empty schemes give the same equations in their zero categories; no flatness
of A over the prime ring is required. -/
theorem finiteGeneralRingOrientation
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : 1 ≤ n)
    (A : Type u) [CommRing A] [Finite A] (hA : ((ell ^ n : ℕ) : A) = 0) :
    let P := finiteGeneralRingPrimeSetting D ell hEll n hn
    let hAU := congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA
    ∃ e : P.Ring ≃+* ULift.{u} (ZMod P.diagonalExponent),
    ∃ t : Etale.FiniteSmoothPurity.CoefficientLineComparison
        (RingHom.ulift.{u + 1, u + 1, u, u} (finiteGeneralRingCoefficientMap P A hA e))
        P.diagonalExponent P.diagonalExponent P.diagonalExponent_annihilates hAU X,
    ∃ alpha : Etale.dualizingComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ≅
        Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) P.diagonalExponent hAU X d,
    ∃ geometry : Etale.FiniteRingSectionDeformation.Geometry d
        (pullback.fst f f) (pullback.diagonal f),
    ∃ hunit : IsIso (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f),
      IsIso (finiteGeneralRingReduction P (finiteGeneralRingCoefficientMap P A hA e) f) ∧
      finiteGeneralRingReduction P (finiteGeneralRingCoefficientMap P A hA e) f ≫
          @inv _ _ _ _ (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f) hunit ≫
          (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map alpha.hom =
        (finiteGeneralRingOrientationExtension P (finiteGeneralRingCoefficientMap P A hA e)
          hAU d f (Y ↘ Spec (.of D.k)) t).hom ∧
      Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A)
        P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level)
        hAU f d geometry (P.diagonalExponent_isUnit (f ≫ (Y ↘ Spec (.of D.k)))) alpha := by
  sorry

end AlgebraicGeometry.ProEtale
