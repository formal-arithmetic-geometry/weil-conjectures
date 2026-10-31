/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteGeneralRingData
import WeilConjectures.SecSmoothPurity.FiniteGeneralRingOrientationSupport
import WeilConjectures.SecSmoothPurity.FiniteGeneralRingOrientationAssembly
import WeilConjectures.SecSmoothPurity.FiniteGeneralRingSiteScalar
import WeilConjectures.AlgebraicGeometry.FiniteSmoothNormalizedExistence
import WeilConjectures.AlgebraicGeometry.DiagonalOrdinaryReesNormalization
import WeilConjectures.AlgebraicGeometry.FiniteNormalizedOrientationScalar
import WeilConjectures.SecSmoothPurity.FiniteSmoothDualizingScalar

/-! # Coefficient transport of the direct smooth orientation
Source: general-ring smooth purity, proof (1)-(3).
(blueprint: lem-sp-general-ring-orientation). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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

Proof: identify the bottom-extension integer ring with Z_ell and transport its
maximal-ideal power to (ell^n). The p-adic reduction map identifies the quotient
with Z/ell^n. The canonical root-generator scalar maps construct the common-level
coefficient-line comparison t. Construct alpha by the smooth diagonal factor,
normalized Rees specialization, inverse normal-section map and inverse bundle
integration adjunct. Extract the ordinary prime-power orientation underlying the
uniquely normalized diagonalDualizingObject. Its coordinate normalization gives
the same Rees normalization by diagonalOrdinaryReesNormalization. Apply the proved
normalizedOrientation_scalar and cancel the two orientation inverses to obtain
the ordinary coefficient square. The ordinary dualizing scalar map is invertible
by finite_smooth_dualizing_scalar. The comparison-adjunction units are invertible
at the degree-zero coefficient units, and hence so are their exceptional and
comparison images. Naturality of the exceptional coefficient mate and the
site/scalar mate gives scalarDualizingUnit_square. Paste this square with the
ordinary coefficient square and the specified prime-power comparison equation.
The resulting invertible composite is exactly the required exceptional reduction.
Naturality of finiteGeneralRingScalarIso identifies the right side with the
prescribed intrinsic scalar extension. No flatness of A over the prime ring is
used. For d=0 the construction uses the empty ordered tensor; empty schemes and
the zero ring satisfy the same categorical identities. -/
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
    ∃ alpha : Etale.dualizingComplex (ULift.{u + 1, u} A) f ≅
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
  classical
  let P := finiteGeneralRingPrimeSetting D ell hEll n hn
  let hAU := congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA
  obtain ⟨e⟩ := primeQuotientEquiv D ell hEll n hn
  let φ := finiteGeneralRingCoefficientMap P A hA e
  let ψ := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let hN := pow_pos P.coefficients.prime.out.pos P.level
  let hX := P.diagonalExponent_isUnit (f ≫ (Y ↘ Spec (.of D.k)))
  let hY := P.diagonalExponent_isUnit (Y ↘ Spec (.of D.k))
  obtain ⟨t⟩ := generalRingCoefficientLine ψ P.diagonalExponent hN
    P.diagonalExponent_annihilates hAU X hX
  obtain ⟨G, alpha, ha⟩ := Etale.FiniteSmoothPurity.generalRingNormalizedOrientation
    (ULift.{u + 1, u} A) P.diagonalExponent hN hAU f d hX
  obtain ⟨alphaR, hR, htheta⟩ :=
    (P.existsUnique_diagonalDualizingObject d f (Y ↘ Spec (.of D.k))).exists.choose_spec
  change P.diagonalDualizingObject d f (Y ↘ Spec (.of D.k)) = _ at htheta
  have hR' := P.diagonalOrdinaryReesNormalization rfl d f (Y ↘ Spec (.of D.k))
    G alphaR hR
  have : IsIso (Etale.ExceptionalCoefficients.dualizingScalarMap ψ f) :=
    (Etale.finite_smooth_dualizing_scalar ψ ell n hn
      P.diagonalExponent_annihilates hAU hY f d).1
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y
    (Etale.ordinaryFiniteUnit P.Coefficient Y) (P.diagonalUnitPlus Y)
  have := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y
    (Etale.ordinaryFiniteUnit (ULift.{u + 1, u} A) Y) ⟨0, inferInstance⟩
  have hunitR : IsIso (finiteGeneralRingDualizingUnitMap P.Coefficient f) := by
    unfold finiteGeneralRingDualizingUnitMap
    infer_instance
  have hunit : IsIso (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f) := by
    unfold finiteGeneralRingDualizingUnitMap
    infer_instance
  let : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
  let w : P.diagonalDualizing f ≅
      (Etale.FiniteSmoothPurity.exceptional P.Coefficient f).obj
        (finiteGeneralRingUnit P.Coefficient Y) :=
    (Etale.FiniteSmoothPurity.comparison P.Coefficient X).mapIso
      (((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient)
          (HasCompactification.compactification f))).rightAdjointUniq
        (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)).app
          ((Etale.FiniteSmoothPurity.origin P.Coefficient Y).obj
            (finiteGeneralRingUnit P.Coefficient Y)))
  have hv : (asIso (finiteGeneralRingDualizingUnitMap P.Coefficient f) ≪≫ w.symm).hom ≫
      (P.diagonalDualizingObject d f (Y ↘ Spec (.of D.k))).hom =
      (Etale.FiniteSmoothPurity.comparison P.Coefficient X).map alphaR.hom := by
    rw [htheta]
    simp only [w, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      asIso_hom]
    unfold finiteGeneralRingDualizingUnitMap
    dsimp only [Etale.FiniteSmoothPurity.comparison,
      WeilConjectures.PurityFiniteSetting.diagonalDualizingComparison,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.trans_hom, Iso.app_hom,
      Iso.app_inv, asIso_inv]
    simp only [Category.assoc, ← Functor.map_comp]
    erw [Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hc : Etale.ExceptionalCoefficients.dualizingScalarMap ψ f ≫ alpha.hom =
      (Etale.FiniteSmoothPurity.ordinaryScalar ψ X).map alphaR.hom ≫
        (t.tensorPower d).hom := by
    have h := Etale.FiniteSmoothPurity.normalizedOrientation_scalar ψ
      P.diagonalExponent P.diagonalExponent hN hN (dvd_refl _)
      P.diagonalExponent_annihilates hAU hY f d G hX hX alphaR alpha hR' ha t
    apply (cancel_epi
      ((Etale.FiniteSmoothPurity.ordinaryScalar ψ X).map alphaR.inv)).1
    rw [← Category.assoc, h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  let r := (Etale.FiniteSmoothPurity.proScalar ψ X).map w.hom ≫
    Etale.FiniteSmoothPurity.proCoefficientMap ψ f
      (finiteGeneralRingUnit P.Coefficient Y) ≫
    (Etale.FiniteSmoothPurity.exceptional (ULift.{u + 1, u} A) f).map
      (finiteGeneralRingScalarUnitIso ψ Y).hom
  have hassemble := assembleOrientation
    (Etale.FiniteSmoothPurity.comparison P.Coefficient X)
    (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X)
    (Etale.FiniteSmoothPurity.proScalar ψ X)
    (Etale.FiniteSmoothPurity.ordinaryScalar ψ X)
    (pbcComparisonReduction X ψ)
    (asIso (finiteGeneralRingDualizingUnitMap P.Coefficient f) ≪≫ w.symm)
    (asIso (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f))
    alphaR alpha (P.diagonalDualizingObject d f (Y ↘ Spec (.of D.k)))
    (t.tensorPower d) (Etale.ExceptionalCoefficients.dualizingScalarMap ψ f) r
    hv hc (by
      simp only [r, Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.map_comp,
        Category.assoc, Iso.map_inv_hom_id_assoc]
      exact scalarDualizingUnit_square ψ f)
  have : IsIso r := hassemble.1
  refine ⟨e, t, alpha, G, hunit, ?_, ?_, ha⟩
  · change IsIso ((finiteGeneralRingScalarIso φ X (P.diagonalDualizing f)).hom ≫ r)
    infer_instance
  · change ((finiteGeneralRingScalarIso φ X (P.diagonalDualizing f)).hom ≫ r) ≫
        inv (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f) ≫
        (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map alpha.hom =
      (finiteGeneralRingScalar φ X).map
          (P.diagonalDualizingObject d f (Y ↘ Spec (.of D.k))).hom ≫
        (finiteGeneralRingScalarIso φ X (P.diagonalTwist X d)).hom ≫
        (pbcComparisonReduction X ψ).hom.app (P.diagonalTwistEtale X d) ≫
        (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map
          (t.tensorPower d).hom
    have heq := hassemble.2
    dsimp only [asIso_inv] at heq
    simp only [Category.assoc]
    rw [heq, reassoc_of% (scalarPresentation_naturality φ X
      (P.diagonalDualizingObject d f (Y ↘ Spec (.of D.k))).hom).symm]

end AlgebraicGeometry.ProEtale
