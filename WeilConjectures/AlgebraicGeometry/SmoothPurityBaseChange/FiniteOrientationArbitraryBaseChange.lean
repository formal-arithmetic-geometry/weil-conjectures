/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import all WeilConjectures.SmoothPurity.Supporting.DiagonalExchangeCube
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization

/-! # Finite orientation for an arbitrary Noetherian Cartesian square
Source: purity-bc, Orientation paragraph, the diagonal and integrated-specialization cube
(blueprint: lem-pur-finite-orientation-arbitrary-base-change).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
open Etale Etale.FiniteSmoothPurity
open scoped CategoryTheory.Functor

/-- Diagonal exchange restricted to the diagonal, for the supplied Cartesian square.
Source: latest blueprint, base-change factors proof (1), diagonal compatibility
(blueprint: lem-pur-finite-orientation-arbitrary-base-change).
The two pastings of the projection cube agree; section-compositor coherence and
cancellation give the comparison of inverse diagonal restrictions. -/
private theorem diagonal_factor_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (v : Y' ⟶ Y) (a : X' ⟶ X) (f' : X' ⟶ Y')
    [IsSeparated f'] [QuasiCompact f'] [HasCompactification f']
    (sq : IsPullback a f' f v) (d : ℕ) [SmoothOfRelativeDimension d f]
    [SmoothOfRelativeDimension d f']
    [HasInvertibleExponent A X] [HasInvertibleExponent A X'] :
    let q := pullback.map f' f' f f a a v sq.w.symm sq.w.symm
    let sq₁ : IsPullback q (pullback.fst f' f') (pullback.fst f f) a :=
      IsPullback.paste_twist_right sq (IsPullback.of_hasPullback f f).flip f' a
        sq.w.symm (pullback.snd f' f') (pullback.fst f' f')
        (IsPullback.of_hasPullback f' f').flip (by simp [q]) (by simp [q])
    let hΔ : pullback.diagonal f' ≫ q = a ≫ pullback.diagonal f := by
      apply pullback.hom_ext <;> simp [q]
    (Etale.upperStar (ModuleCat.{u + 1} A)
      a).leftDerivedFunctor.map (finiteSmoothDiagonalFactor A f) ≫
        NoetherianSectionSpecialization.sectionMap A (pullback.fst f f)
          (pullback.fst f' f')
          a q sq₁
          (pullback.diagonal f) (pullback.diagonal f') hΔ =
      Etale.dualizingComplexBaseChangeMap A sq ≫
        finiteSmoothDiagonalFactor A f' := by
  dsimp only
  let q := pullback.map f' f' f f a a v sq.w.symm sq.w.symm
  have sq₁ : IsPullback q (pullback.fst f' f') (pullback.fst f f) a :=
    IsPullback.paste_twist_right sq (IsPullback.of_hasPullback f f).flip f' a
      sq.w.symm (pullback.snd f' f') (pullback.fst f' f')
      (IsPullback.of_hasPullback f' f').flip (by simp [q]) (by simp [q])
  have sq₂ : IsPullback q (pullback.snd f' f') (pullback.snd f f) a :=
    IsPullback.paste_twist_right sq (IsPullback.of_hasPullback f f) f' a
      sq.w.symm (pullback.fst f' f') (pullback.snd f' f')
      (IsPullback.of_hasPullback f' f') (by simp [q]) (by simp [q])
  have hΔ : pullback.diagonal f' ≫ q = a ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;> simp [q]
  have : HasInvertibleExponent A (pullback f f) :=
    HasInvertibleExponent.of_hom (show pullback f f ⟶ X from pullback.fst f f)
  have hIso {B C B' C' : Scheme.{u}} {g : B ⟶ C} {g' : B' ⟶ C'}
      {a : B' ⟶ B} {b : C' ⟶ C}
      [QuasiSeparatedSpace C] [HasInvertibleExponent A B]
      [HasCompactification g] [HasCompactification g'] [QuasiCompact g']
      [SmoothOfRelativeDimension d g] (sq : IsPullback a g' g b) :
      IsIso (Etale.dualizingComplexBaseChangeMap A sq) := by
    have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension A g d sq
    exact (Etale.isIso_dualizingComplexBaseChangeMap_iff A sq).2 inferInstance
  have := hIso (IsPullback.of_hasPullback f f).flip
  have := hIso
    (IsPullback.of_hasPullback f' f').flip
  have := hIso sq₁
  have := hIso sq
  let b := asIso (Etale.dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip)
  let b' := asIso (Etale.dualizingComplexBaseChangeMap A
    (IsPullback.of_hasPullback f' f').flip)
  let bp := asIso (Etale.dualizingComplexBaseChangeMap A sq₁)
  let e := asIso (Etale.dualizingComplexBaseChangeMap A sq)
  have hpaste := cube_dualizing_base_comp A (IsPullback.of_hasPullback f f).flip sq₁
  have hpaste' := cube_dualizing_base_comp_chosen A
    sq
    (IsPullback.of_hasPullback f' f').flip
    (q ≫ pullback.snd f f) (a ≫ f)
    sq₂.w sq.w
    (sq₁.paste_horiz (IsPullback.of_hasPullback f f).flip)
  have heq :
      (Etale.upperStar (ModuleCat.{u + 1} A)
        q).leftDerivedFunctor.map b.hom ≫ bp.hom =
      (diagonalCubePullbackIso A q (pullback.snd f f)
        (pullback.snd f' f')
        a sq₂.w).hom.app _ ≫
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (pullback.snd f' f')).leftDerivedFunctor.map e.hom ≫
        b'.hom := by
    have h := hpaste.symm.trans hpaste'
    apply (cancel_epi ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      q (pullback.snd f f)).hom.app _)).mp
    simpa only [diagonalCubePullbackIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.hom_inv_id_app_assoc, b, b', bp, e, asIso_hom] using h
  let k := (Etale.upperStar (ModuleCat.{u + 1} A)
    (pullback.diagonal f)).leftDerivedFunctor.mapIso b.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).app _
  let k' :=
    (Etale.upperStar (ModuleCat.{u + 1} A)
      (pullback.diagonal f')).leftDerivedFunctor.mapIso b'.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (pullback.diagonal f')
      (pullback.snd f' f')
      (pullback.diagonal_snd f')).app _
  have hk := cube_section_equation A
    a (pullback.snd f f)
    (pullback.snd f' f') q
    (pullback.diagonal f) (pullback.diagonal f') sq₂.w hΔ
    (pullback.diagonal_snd f) (pullback.diagonal_snd f')
    _ _ _ _ b b' bp e heq
  rw [← Category.assoc] at hk
  change _ ≫ k'.hom =
    (Etale.upperStar (ModuleCat.{u + 1} A)
      a).leftDerivedFunctor.map k.hom ≫ e.hom at hk
  have hsection :
      NoetherianSectionSpecialization.sectionMap A (pullback.fst f f)
        (pullback.fst f' f')
        a q sq₁
        (pullback.diagonal f) (pullback.diagonal f') hΔ ≫
          k'.hom =
      (Etale.upperStar (ModuleCat.{u + 1} A)
        a).leftDerivedFunctor.map k.hom ≫ e.hom := by
    simpa only [NoetherianSectionSpecialization.sectionMap, diagonalCubePullbackIso,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
      Category.assoc, bp, asIso_hom,
      sectionInvariant] using hk
  have hD : finiteSmoothDiagonalFactor A f = k.inv := rfl
  have hD' : finiteSmoothDiagonalFactor A f' = k'.inv := rfl
  rw [hD, hD']
  apply (cancel_mono k'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (Etale.upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.map k.inv ≫
    (_ ≫ k'.hom) = _
  rw [hsection, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The normalized inverse finite orientation commutes with a supplied Cartesian square,
without a finite-field presentation of its schemes.
Source: purity-bc, Orientation paragraph
(blueprint: lem-pur-finite-orientation-arbitrary-base-change).

Proof: use the Cartesian cube of diagonal projections and restrict exceptional exchange
along the diagonal. Counit pasting gives the comparison of finiteSmoothDiagonalFactor.
Unpack each normalized orientation; cancellation of the bundle integration adjunct and
normal-section isomorphism identifies it with this factor followed by integrated
specialization. Apply integratedSpecialization_baseChange to the diagonal cube. Compose
the resulting two squares and cancel the primed orientation to obtain the inverse
orientation formula. All inputs of this calculation are Noetherianity, the finite
coefficient exponent invertible on the schemes, and smoothness; no field is used. -/
theorem finite_orientation_arbitrary_base_change
    (ell : ℕ) [Fact ell.Prime]
    (X Y X' Y' : Scheme.{u})
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (f : X ⟶ Y) (v : Y' ⟶ Y) (u' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback u' f' f v) (d : ℕ)
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    [SmoothOfRelativeDimension d f]
    (n : ℕ) (_hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (g : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (g' : @Etale.FiniteRingSectionDeformation.Geometry
      (pullback f' f') X' d
      (pullback.fst f' f') (pullback.diagonal f')
      (@IsSeparated.isClosedImmersion_diagonal _ _ f'
        (MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance)))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(X', ⊤)))
    (alpha : Etale.dualizingComplex A f ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X d)
    (alpha' : @Etale.dualizingComplex A _ _ X' Y' f'
        (HasCompactification.of_isPullback sq) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X' d)
    (_ha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f d g hX alpha)
    (_ha' : @Etale.FiniteSmoothPurity.OrientationNormalized A _ _ (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA X' Y' _ f'
      (HasCompactification.of_isPullback sq)
      (MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance)
      (MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance)
      d g' hX' alpha') :
    (Etale.ordinaryFinitePullback A u').map alpha.inv ≫
        @Etale.dualizingComplexBaseChangeMap A _ _
          X Y X' Y' f v f' u' _
          (HasCompactification.of_isPullback sq)
          (MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance) sq =
      (Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
        (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
          (pow_pos (Fact.out : ell.Prime).pos n) hA)
        u' hX d).hom ≫ alpha'.inv := by
  have : IsSeparated f' :=
    MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have : HasCompactification f' := HasCompactification.of_isPullback sq
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d f' :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) sq inferInstance
  let := g
  let := g'
  let N := ell ^ n
  have hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
  have : HasInvertibleExponent A X := ⟨N, hN, hA, hX⟩
  have : HasInvertibleExponent A X' := ⟨N, hN, hA, hX'⟩
  obtain ⟨κ, hκ, normalSq, heq⟩ := _ha
  obtain ⟨κ', hκ', sq', heq'⟩ := _ha'
  let ψ := integratedSpecialization A d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) normalSq N hN hA hX κ
  let ψ' := integratedSpecialization A d
    (pullback.fst f' f')
    (pullback.diagonal f')
    (pullback.diagonal_fst f') sq' N hN hA hX' κ'
  have halpha : alpha.hom = finiteSmoothDiagonalFactor A f ≫ ψ := by
    let := normalSectionMap_isIso A d (pullback.fst f f)
      (pullback.diagonal f) (pullback.diagonal_fst f) normalSq N hN hA hX
    let := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA
      X hX d (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).2
    apply (cancel_mono (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
      N hN A hA X hX d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) ≫
      normalSectionMap A d (pullback.fst f f) (pullback.diagonal f)
        (pullback.diagonal_fst f) normalSq)).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq.symm
  have halpha' : alpha'.hom =
      finiteSmoothDiagonalFactor A f' ≫ ψ' := by
    let := normalSectionMap_isIso A d
      (pullback.fst f' f')
      (pullback.diagonal f')
      (pullback.diagonal_fst f') sq' N hN hA hX'
    let := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA
      X' hX' d
      (ConormalGradedAlgebra.piece (pullback.diagonal f') 1)).2
    apply (cancel_mono (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
      N hN A hA X' hX' d
      (ConormalGradedAlgebra.piece (pullback.diagonal f') 1) ≫
      normalSectionMap A d
        (pullback.fst f' f')
        (pullback.diagonal f')
        (pullback.diagonal_fst f') sq')).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq'.symm
  let q := pullback.map f' f' f f
    u' u' v sq.w.symm sq.w.symm
  have sq₁ : IsPullback q (pullback.fst f' f')
      (pullback.fst f f) u' :=
    IsPullback.paste_twist_right sq (IsPullback.of_hasPullback f f).flip
      f' u' sq.w.symm (pullback.snd f' f')
      (pullback.fst f' f') (IsPullback.of_hasPullback f' f').flip
      (by simp [q]) (by simp [q])
  have hΔ : pullback.diagonal f' ≫ q = u' ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;> simp [q]
  have hψ := integratedSpecialization_baseChange A N hN hA d
    (pullback.fst f f)
    (pullback.fst f' f')
    (pullback.diagonal f) (pullback.diagonal f')
    (pullback.diagonal_fst f)
    (pullback.diagonal_fst f')
    u' q
    sq₁ hΔ
    normalSq sq' hX hX' κ κ' hκ hκ'
  have hdiag := diagonal_factor_base_change A f v u' f' sq d
  have hforward : dualizingComplexBaseChangeMap A
        sq ≫ alpha'.hom =
      (ordinaryFinitePullback A u').map alpha.hom ≫
        (vectorIntegrationBaseCoefficientPullback A N hA
          (PurityFiniteSetting.purityTwistTransport A N hN hA)
          u' hX d).hom := by
    rw [halpha, halpha', Functor.map_comp, ← Category.assoc, ← hdiag, Category.assoc]
    simpa only [Category.assoc, ψ, ψ', ordinaryFinitePullback, N] using congrArg (fun z ↦
      (ordinaryFinitePullback A u').map
        (finiteSmoothDiagonalFactor A f) ≫ z) hψ.symm
  apply (cancel_mono alpha'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hforward, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]


end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
