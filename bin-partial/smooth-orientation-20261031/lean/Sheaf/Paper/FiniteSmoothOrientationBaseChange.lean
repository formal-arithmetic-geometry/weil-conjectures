/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.FiniteSmoothPurityMaps
public import Sheaf.Paper.VectorPurityNormalization
import Sheaf.Paper.FiniteSectionIntegratedSpecialization
import all Sheaf.Paper.DiagonalExchangeCube

/-! # Finite smooth orientation under base change

Source: latest blueprint, smooth-purity base-change factors, proof (1)
(blueprint: lem-sp-finite-normalized-orientation-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

open Etale Etale.FiniteSmoothPurity
open scoped CategoryTheory.Functor

private theorem diagonal_factor_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Y']
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (v : Y' ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f]
    [IsNoetherian (pullback f v)]
    [HasInvertibleExponent A X] [HasInvertibleExponent A (pullback f v)] :
    (Etale.upperStar (ModuleCat.{u + 1} A)
      (pullback.fst f v)).leftDerivedFunctor.map (finiteSmoothDiagonalFactor A f) ≫
        NoetherianSectionSpecialization.sectionMap A (pullback.fst f f)
          (pullback.fst (pullback.snd f v) (pullback.snd f v))
          (pullback.fst f v) (diagonalCubeMap f v) (cube_projection_squares f v).1
          (pullback.diagonal f) (pullback.diagonal (pullback.snd f v)) (cube_diagonal f v) =
      Etale.dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f v) ≫
        finiteSmoothDiagonalFactor A (pullback.snd f v) := by
  obtain ⟨sq₁, sq₂⟩ := cube_projection_squares f v
  have hΔ := cube_diagonal f v
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
    (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip
  have := hIso sq₁
  have := hIso (IsPullback.of_hasPullback f v)
  let b := asIso (Etale.dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip)
  let b' := asIso (Etale.dualizingComplexBaseChangeMap A
    (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip)
  let bp := asIso (Etale.dualizingComplexBaseChangeMap A sq₁)
  let e := asIso (Etale.dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f v))
  have hpaste := cube_dualizing_base_comp A (IsPullback.of_hasPullback f f).flip sq₁
  have hpaste' := cube_dualizing_base_comp_chosen A
    (IsPullback.of_hasPullback f v)
    (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip
    (diagonalCubeMap f v ≫ pullback.snd f f) (pullback.fst f v ≫ f)
    sq₂.w (pullback.condition (f := f) (g := v))
    (sq₁.paste_horiz (IsPullback.of_hasPullback f f).flip)
  have heq :
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (diagonalCubeMap f v)).leftDerivedFunctor.map b.hom ≫ bp.hom =
      (diagonalCubePullbackIso A (diagonalCubeMap f v) (pullback.snd f f)
        (pullback.snd (pullback.snd f v) (pullback.snd f v))
        (pullback.fst f v) sq₂.w).hom.app _ ≫
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (pullback.snd (pullback.snd f v) (pullback.snd f v))).leftDerivedFunctor.map e.hom ≫
        b'.hom := by
    have h := hpaste.symm.trans hpaste'
    apply (cancel_epi ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (diagonalCubeMap f v) (pullback.snd f f)).hom.app _)).mp
    simpa only [diagonalCubePullbackIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.hom_inv_id_app_assoc, b, b', bp, e, asIso_hom] using h
  let k := (Etale.upperStar (ModuleCat.{u + 1} A)
    (pullback.diagonal f)).leftDerivedFunctor.mapIso b.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).app _
  let k' :=
    (Etale.upperStar (ModuleCat.{u + 1} A)
      (pullback.diagonal (pullback.snd f v))).leftDerivedFunctor.mapIso b'.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (pullback.diagonal (pullback.snd f v))
      (pullback.snd (pullback.snd f v) (pullback.snd f v))
      (pullback.diagonal_snd (pullback.snd f v))).app _
  have hk := cube_section_equation A
    (pullback.fst f v) (pullback.snd f f)
    (pullback.snd (pullback.snd f v) (pullback.snd f v)) (diagonalCubeMap f v)
    (pullback.diagonal f) (pullback.diagonal (pullback.snd f v)) sq₂.w hΔ
    (pullback.diagonal_snd f) (pullback.diagonal_snd (pullback.snd f v))
    _ _ _ _ b b' bp e heq
  rw [← Category.assoc] at hk
  change _ ≫ k'.hom =
    (Etale.upperStar (ModuleCat.{u + 1} A)
      (pullback.fst f v)).leftDerivedFunctor.map k.hom ≫ e.hom at hk
  have hsection :
      NoetherianSectionSpecialization.sectionMap A (pullback.fst f f)
        (pullback.fst (pullback.snd f v) (pullback.snd f v))
        (pullback.fst f v) (diagonalCubeMap f v) (cube_projection_squares f v).1
        (pullback.diagonal f) (pullback.diagonal (pullback.snd f v)) (cube_diagonal f v) ≫
          k'.hom =
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (pullback.fst f v)).leftDerivedFunctor.map k.hom ≫ e.hom := by
    simpa only [NoetherianSectionSpecialization.sectionMap, diagonalCubePullbackIso,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
      Category.assoc, bp, asIso_hom,
      sectionInvariant] using hk
  have hD : finiteSmoothDiagonalFactor A f = k.inv := rfl
  have hD' : finiteSmoothDiagonalFactor A (pullback.snd f v) = k'.inv := rfl
  rw [hD, hD']
  apply (cancel_mono k'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (Etale.upperStar (ModuleCat.{u + 1} A) (pullback.fst f v)).leftDerivedFunctor.map k.inv ≫
    (_ ≫ k'.hom) = _
  rw [hsection, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The inverse diagonal orientation commutes with arbitrary change of base.
This is only the coefficient-line factor; it says nothing about tensor mates or gamma.
Source: latest blueprint sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, proof (1)
(blueprint: lem-sp-finite-normalized-orientation-base-change).

Proof: first work at R = Z/ell^n. The diagonal exchange cube identifies the
restriction of the projection exchange with the unit exceptional exchange.
The section DNC/integration base-change square identifies the pulled-back
normalized Rees specialization and the normal-bundle integration factor.
Compose these squares. The diagonal specialization of the integrated DNC
comparison is the specified diagonal orientation, so Pi_f' e_R = u*Pi_f.

For A, use the unital map R -> A. Finite general-ring purity identifies its
direct diagonal orientation with scalar extension of Pi_f. The mixed
coefficient/exceptional-exchange square and finite scalar orientation transport
then give Pi_f',A e_A = u*Pi_f,A. The supplied OrientationNormalized equations
fix the same arrows: uniqueness of the Rees comparison normalized at one
identifies the specialization, and cancellation of the invertible bundle
integration adjunct identifies alpha and alpha'. Geometry consists entirely
of proofs, so its supplied witnesses do not alter any arrow. These arguments
apply in the ordinary etale presentation; alternatively its bounded-below site
comparison is fully faithful on the smooth dualizing objects and Tate lines.
Compose with u*(alpha inverse) and alpha' inverse to obtain the displayed
inverse equation. Unit and root comparisons are the specified Kummer-normalized
ones. Zero rank uses empty tensor products and the unit comparison; empty
schemes and the zero coefficient ring give the same equations in zero categories.
No flatness of A over R, or of v, is needed. -/
theorem finite_orientation_base_change
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (X Y Y' : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    (f : X ⟶ Y) (v : Y' ⟶ Y) (d : ℕ)
    [IsSeparated f.left] [QuasiCompact f.left] [HasCompactification f.left]
    [SmoothOfRelativeDimension d f.left]
    [IsNoetherian (pullback f.left v.left)]
    (n : ℕ) (hn : 1 ≤ n) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ell ^ n : ℕ) : A) = 0)
    (g : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f.left f.left) (pullback.diagonal f.left))
    (g' : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
      (pullback.diagonal (pullback.snd f.left v.left)))
    (hX : IsUnit ((ell ^ n : ℕ) : Γ(X.left, ⊤)))
    (hX' : IsUnit ((ell ^ n : ℕ) : Γ(pullback f.left v.left, ⊤)))
    (alpha : Etale.dualizingComplex A f.left ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA X.left d)
    (alpha' : Etale.dualizingComplex A
        (pullback.snd f.left v.left) ≅
      Etale.FiniteSmoothPurity.line A (ell ^ n) hA (pullback f.left v.left) d)
    (_ha : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA f.left d g hX alpha)
    (_ha' : Etale.FiniteSmoothPurity.OrientationNormalized A (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hA (pullback.snd f.left v.left)
      d g' hX' alpha') :
    (Etale.ordinaryFinitePullback A (pullback.fst f.left v.left)).map alpha.inv ≫
        Etale.dualizingComplexBaseChangeMap A
          (IsPullback.of_hasPullback f.left v.left) =
      (Etale.vectorIntegrationBaseCoefficientPullback A (ell ^ n) hA
        (PurityFiniteSetting.purityTwistTransport A (ell ^ n)
          (pow_pos (Fact.out : ell.Prime).pos n) hA)
        (pullback.fst f.left v.left) hX d).hom ≫ alpha'.inv := by
  have _ := hn
  let := g
  let := g'
  have hY'loc : IsLocallyNoetherian Y'.left :=
    LocallyOfFiniteType.isLocallyNoetherian Y'.hom
  have hY'compact : CompactSpace Y'.left :=
    QuasiCompact.compactSpace_of_compactSpace Y'.hom
  have : IsNoetherian Y'.left := {}
  let N := ell ^ n
  have hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
  have : HasInvertibleExponent A X.left := ⟨N, hN, hA, hX⟩
  have : HasInvertibleExponent A (pullback f.left v.left) := ⟨N, hN, hA, hX'⟩
  obtain ⟨κ, hκ, sq, heq⟩ := _ha
  obtain ⟨κ', hκ', sq', heq'⟩ := _ha'
  let ψ := integratedSpecialization A d (pullback.fst f.left f.left)
    (pullback.diagonal f.left) (pullback.diagonal_fst f.left) sq N hN hA hX κ
  let ψ' := integratedSpecialization A d
    (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
    (pullback.diagonal (pullback.snd f.left v.left))
    (pullback.diagonal_fst (pullback.snd f.left v.left)) sq' N hN hA hX' κ'
  have halpha : alpha.hom = finiteSmoothDiagonalFactor A f.left ≫ ψ := by
    let := normalSectionMap_isIso A d (pullback.fst f.left f.left)
      (pullback.diagonal f.left) (pullback.diagonal_fst f.left) sq N hN hA hX
    let := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA
      X.left hX d (ConormalGradedAlgebra.piece (pullback.diagonal f.left) 1)).2
    apply (cancel_mono (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
      N hN A hA X.left hX d
      (ConormalGradedAlgebra.piece (pullback.diagonal f.left) 1) ≫
      normalSectionMap A d (pullback.fst f.left f.left) (pullback.diagonal f.left)
        (pullback.diagonal_fst f.left) sq)).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq.symm
  have halpha' : alpha'.hom =
      finiteSmoothDiagonalFactor A (pullback.snd f.left v.left) ≫ ψ' := by
    let := normalSectionMap_isIso A d
      (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
      (pullback.diagonal (pullback.snd f.left v.left))
      (pullback.diagonal_fst (pullback.snd f.left v.left)) sq' N hN hA hX'
    let := (Etale.FiniteRingSectionDeformation.bundleAdjoint_isIso N hN A hA
      (pullback f.left v.left) hX' d
      (ConormalGradedAlgebra.piece (pullback.diagonal (pullback.snd f.left v.left)) 1)).2
    apply (cancel_mono (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
      N hN A hA (pullback f.left v.left) hX' d
      (ConormalGradedAlgebra.piece (pullback.diagonal (pullback.snd f.left v.left)) 1) ≫
      normalSectionMap A d
        (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
        (pullback.diagonal (pullback.snd f.left v.left))
        (pullback.diagonal_fst (pullback.snd f.left v.left)) sq')).mp
    rw [Category.assoc, integratedSpecialization_normalization]
    exact heq'.symm
  have hψ := integratedSpecialization_baseChange A N hN hA d
    (pullback.fst f.left f.left)
    (pullback.fst (pullback.snd f.left v.left) (pullback.snd f.left v.left))
    (pullback.diagonal f.left) (pullback.diagonal (pullback.snd f.left v.left))
    (pullback.diagonal_fst f.left)
    (pullback.diagonal_fst (pullback.snd f.left v.left))
    (pullback.fst f.left v.left) (diagonalCubeMap f.left v.left)
    (cube_projection_squares f.left v.left).1 (cube_diagonal f.left v.left)
    sq sq' hX hX' κ κ' hκ hκ'
  have hdiag := diagonal_factor_baseChange A f.left v.left d
  have hforward : dualizingComplexBaseChangeMap A
        (IsPullback.of_hasPullback f.left v.left) ≫ alpha'.hom =
      (ordinaryFinitePullback A (pullback.fst f.left v.left)).map alpha.hom ≫
        (vectorIntegrationBaseCoefficientPullback A N hA
          (PurityFiniteSetting.purityTwistTransport A N hN hA)
          (pullback.fst f.left v.left) hX d).hom := by
    rw [halpha, halpha', Functor.map_comp, ← Category.assoc, ← hdiag, Category.assoc]
    simpa only [Category.assoc, ψ, ψ', ordinaryFinitePullback, N] using congrArg (fun z ↦
      (ordinaryFinitePullback A (pullback.fst f.left v.left)).map
        (finiteSmoothDiagonalFactor A f.left) ≫ z) hψ.symm
  apply (cancel_mono alpha'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hforward, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
