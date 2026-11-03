/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
import all WeilConjectures.SmoothPurity.Supporting.DiagonalExchangeCube

/-! # Finite smooth orientation base change without a finite-field index

Source: current blueprint sk-prop-sp-purity-bc.proof.md, orientation paragraph
(blueprint: lem-pur-general-finite-orientation-base-change).
The argument is intrinsic to Noetherian schemes and their normalized orientations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
open Etale Etale.FiniteSmoothPurity
open scoped CategoryTheory.Functor

/-- Base change of the normalized finite orientation on Noetherian schemes.
Source: sk-prop-sp-purity-bc, orientation paragraph
(blueprint: lem-pur-general-finite-orientation-base-change).

Proof: cancel the invertible bundle integration adjunct in each supplied
normalization to express its orientation by the integrated diagonal specialization.
The diagonal exchange cube identifies the diagonal factors after pullback, while
base change for the normalized Rees specialization identifies the integrated factors.
Compose these two identities and cancel the target orientation. Every comparison is
an actual adjunction mate; the argument is independent of a base field and makes no
faithfulness assumption on general derived finite-level evaluation maps. -/
theorem finite_orientation_base_change_general
    (ell : ℕ) [Fact ell.Prime]
    (X Y Y' : Scheme.{u})
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Y']
    (f : X ⟶ Y) (v : Y' ⟶ Y) (d : ℕ)
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    [SmoothOfRelativeDimension d f]
    [IsNoetherian (pullback f v)]
    (n : ℕ) (hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (g : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (g' : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (pullback.snd f v) (pullback.snd f v))
      (pullback.diagonal (pullback.snd f v)))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(pullback f v, ⊤)))
    (alpha : Etale.dualizingComplex A f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X d)
    (alpha' : Etale.dualizingComplex A
        (pullback.snd f v) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f v) d)
    (_ha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f d g hX alpha)
    (_ha' : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA (pullback.snd f v)
      d g' hX' alpha') :
    (Etale.ordinaryFinitePullback A (pullback.fst f v)).map alpha.inv ≫
        Etale.dualizingComplexBaseChangeMap A
          (IsPullback.of_hasPullback f v) =
      (Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
        (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
          (pow_pos (Fact.out : ell.Prime).pos n) hA)
        (pullback.fst f v) hX d).hom ≫ alpha'.inv := by
  have _ := hn
  let := g
  let := g'
  let N := ell ^ n
  have hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
  have : HasInvertibleExponent A X := ⟨N, hN, hA, hX⟩
  have : HasInvertibleExponent A (pullback f v) := ⟨N, hN, hA, hX'⟩
  obtain ⟨κ, hκ, sq, heq⟩ := _ha
  obtain ⟨κ', hκ', sq', heq'⟩ := _ha'
  let ψ := integratedSpecialization A d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) sq N hN hA hX κ
  let ψ' := integratedSpecialization A d
    (pullback.fst (pullback.snd f v) (pullback.snd f v))
    (pullback.diagonal (pullback.snd f v))
    (pullback.diagonal_fst (pullback.snd f v)) sq' N hN hA hX' κ'
  have halpha : alpha.hom = finiteSmoothDiagonalFactor A f ≫ ψ := by
    let := normalSectionMap_isIso A d (pullback.fst f f)
      (pullback.diagonal f) (pullback.diagonal_fst f) sq N hN hA hX
    let := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA
      X hX d (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).2
    apply (cancel_mono (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
      N hN A hA X hX d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) ≫
      normalSectionMap A d (pullback.fst f f) (pullback.diagonal f)
        (pullback.diagonal_fst f) sq)).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq.symm
  have halpha' : alpha'.hom =
      finiteSmoothDiagonalFactor A (pullback.snd f v) ≫ ψ' := by
    let := normalSectionMap_isIso A d
      (pullback.fst (pullback.snd f v) (pullback.snd f v))
      (pullback.diagonal (pullback.snd f v))
      (pullback.diagonal_fst (pullback.snd f v)) sq' N hN hA hX'
    let := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA
      (pullback f v) hX' d
      (ConormalGradedAlgebra.piece (pullback.diagonal (pullback.snd f v)) 1)).2
    apply (cancel_mono (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
      N hN A hA (pullback f v) hX' d
      (ConormalGradedAlgebra.piece (pullback.diagonal (pullback.snd f v)) 1) ≫
      normalSectionMap A d
        (pullback.fst (pullback.snd f v) (pullback.snd f v))
        (pullback.diagonal (pullback.snd f v))
        (pullback.diagonal_fst (pullback.snd f v)) sq')).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq'.symm
  have hψ := integratedSpecialization_baseChange A N hN hA d
    (pullback.fst f f)
    (pullback.fst (pullback.snd f v) (pullback.snd f v))
    (pullback.diagonal f) (pullback.diagonal (pullback.snd f v))
    (pullback.diagonal_fst f)
    (pullback.diagonal_fst (pullback.snd f v))
    (pullback.fst f v) (diagonalCubeMap f v)
    (cube_projection_squares f v).1 (cube_diagonal f v)
    sq sq' hX hX' κ κ' hκ hκ'
  have hdiag := diagonal_factor_baseChange A f v d
  have hforward : dualizingComplexBaseChangeMap A
        (IsPullback.of_hasPullback f v) ≫ alpha'.hom =
      (ordinaryFinitePullback A (pullback.fst f v)).map alpha.hom ≫
        (vectorIntegrationBaseCoefficientPullback A N hA
          (PurityFiniteSetting.purityTwistTransport A N hN hA)
          (pullback.fst f v) hX d).hom := by
    rw [halpha, halpha', Functor.map_comp, ← Category.assoc, ← hdiag, Category.assoc]
    simpa only [Category.assoc, ψ, ψ', ordinaryFinitePullback, N] using congrArg (fun z ↦
      (ordinaryFinitePullback A (pullback.fst f v)).map
        (finiteSmoothDiagonalFactor A f) ≫ z) hψ.symm
  apply (cancel_mono alpha'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hforward, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
