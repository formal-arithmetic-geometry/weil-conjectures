/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingOrientationSupport
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingOrdinaryScalarUnit
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothDiagonalScalar
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrdinaryReesEquation
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteNormalizedOrientationScalar

/-! # Scalar compatibility of the normalized finite diagonal

Source: current general-ring smooth purity, paragraphs (1)--(2).
(blueprint: lem-sp-finite-scalar-diagonal-compatibility). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The scalar square for an already constructed, normalized ordinary orientation.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, paragraphs (1)--(2).
(blueprint: lem-sp-finite-scalar-diagonal-compatibility).

Proof: let alphaR be the ordinary orientation underlying the unique canonical
diagonal dualizing object, with its coordinate normalization. The finite-ring
section deformation of the diagonal gives a normalized comparison kappa, and the
Rees-to-cone-to-bundle isomorphism over X gives the pullback square; the
fixed-witness Rees equation then shows that alphaR is OrientationNormalized for
the given geometry G. The normalized-orientation scalar theorem, applied to
alphaR and the given normalized A-orientation alpha, gives the exceptional
coefficient square; cancelling the invertible maps alphaR, alpha and the line
comparison shows that the dualizing scalar map is invertible. The comparison
adjunction unit is invertible at the finite coefficient units, so both dualizing
unit maps are invertible, and uniqueness of right adjoints identifies the
canonical diagonal object with the comparison image of alphaR. Pasting the
ordinary scalar square with the scalar dualizing-unit square (assembleOrientation)
proves invertibility of the reduction and the displayed equation, after the
scalar presentation is replaced by the canonical one by naturality. Dimension
zero and the empty scheme need no separate argument; no data are chosen.
-/
theorem finiteScalarDiagonalCompatibility
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (A : Type u) [CommRing A] [Finite A]
    (hA : (P.diagonalExponent : A) = 0) (phi : P.Ring →+* A)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (t : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} phi)
      P.diagonalExponent P.diagonalExponent P.diagonalExponent_annihilates
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X)
    (G : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alpha : Etale.dualizingComplex (ULift.{u + 1, u} A) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) P.diagonalExponent
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X d)
    (hα : Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A)
      P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level)
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA)
      f d G (P.diagonalExponent_isUnit (f ≫ aY)) alpha) :
    ∃ hu : IsIso (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f),
      IsIso (finiteGeneralRingReduction P phi f) ∧
      finiteGeneralRingReduction P phi f ≫
        @inv _ _ _ _ (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f) hu ≫
        (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map alpha.hom =
      (finiteGeneralRingOrientationExtension P phi
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) d f aY t).hom := by
  classical
  let hAU := congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA
  let ψ := RingHom.ulift.{u + 1, u + 1, u, u} phi
  let hN := pow_pos P.coefficients.prime.out.pos P.level
  let hX := P.diagonalExponent_isUnit (f ≫ aY)
  let hY := P.diagonalExponent_isUnit aY
  obtain ⟨alphaR, hR, htheta⟩ :=
    (P.existsUnique_diagonalDualizingObject d f aY).exists.choose_spec
  change P.diagonalDualizingObject d f aY = _ at htheta
  have hR' : Etale.FiniteSmoothPurity.OrientationNormalized P.Coefficient
      P.diagonalExponent hN P.diagonalExponent_annihilates f d G hX alphaR := by
    let _ := G
    let hN : 0 < P.diagonalExponent :=
      pow_pos P.coefficients.prime.out.pos P.level
    let hX : IsUnit (P.diagonalExponent : Γ(X, ⊤)) :=
      P.diagonalExponent_isUnit (f ≫ aY)
    obtain ⟨κ, hκ, _⟩ :=
      AlgebraicGeometry.Etale.FiniteRingSectionDeformation.existsUnique_normalized
        P.diagonalExponent hN P.Coefficient P.diagonalExponent_annihilates hX d
        (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)
    let q := AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison
        (pullback.diagonal f) ≪≫
      AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coneBundleIso d
        (pullback.fst f f) (pullback.diagonal f)
    have hq : q.hom ≫ VectorBundleZeroSection.π X d
        (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) =
        Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f) := by
      dsimp [q]
      rw [Category.assoc,
        (AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coneBundleIso_spec d
          (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)).1,
        (AlgebraicGeometry.Etale.FiniteSmoothPurity.reesConeComparison_spec
          (pullback.diagonal f)).1]
      exact Scheme.Hom.purityNormalProjection_eq _ _ (pullback.diagonal_fst f)
    have sq : IsPullback q.hom
        (Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f))
        (VectorBundleZeroSection.π X d
          (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) (𝟙 X) :=
      IsPullback.of_horiz_isIso ⟨by simpa using hq⟩
    exact ⟨κ, hκ, sq, by
      exact P.diagonalOrdinaryReesEquation d f aY G alphaR κ hκ sq hR⟩
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
      (P.diagonalDualizingObject d f aY).hom =
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
      P.diagonalExponent_annihilates hAU hY f d G hX hX alphaR alpha hR' hα t
    apply (cancel_epi
      ((Etale.FiniteSmoothPurity.ordinaryScalar ψ X).map alphaR.inv)).1
    rw [← Category.assoc, h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have : IsIso (Etale.ExceptionalCoefficients.dualizingScalarMap ψ f) := by
    have : IsIso (Etale.ExceptionalCoefficients.dualizingScalarMap ψ f ≫ alpha.hom) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _ alpha.hom
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
    alphaR alpha (P.diagonalDualizingObject d f aY)
    (t.tensorPower d) (Etale.ExceptionalCoefficients.dualizingScalarMap ψ f) r
    hv hc (by
      simp only [r, Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.map_comp,
        Category.assoc, Iso.map_inv_hom_id_assoc]
      exact scalarDualizingUnit_square ψ f)
  have : IsIso r := hassemble.1
  refine ⟨hunit, ?_, ?_⟩
  · change IsIso ((finiteGeneralRingScalarIso phi X (P.diagonalDualizing f)).hom ≫ r)
    infer_instance
  · change ((finiteGeneralRingScalarIso phi X (P.diagonalDualizing f)).hom ≫ r) ≫
        inv (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f) ≫
        (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map alpha.hom =
      (finiteGeneralRingScalar phi X).map
          (P.diagonalDualizingObject d f aY).hom ≫
        (finiteGeneralRingScalarIso phi X (P.diagonalTwist X d)).hom ≫
        (pbcComparisonReduction X ψ).hom.app (P.diagonalTwistEtale X d) ≫
        (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map
          (t.tensorPower d).hom
    have heq := hassemble.2
    dsimp only [asIso_inv] at heq
    simp only [Category.assoc]
    rw [heq, reassoc_of% (scalarPresentation_naturality phi X
      (P.diagonalDualizingObject d f aY).hom).symm]


end AlgebraicGeometry.ProEtale
