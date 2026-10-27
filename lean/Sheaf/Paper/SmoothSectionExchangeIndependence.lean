/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.NoetherianEtaleSectionSpecialization
import Sheaf.Paper.SmoothSectionAutomorphism
import all Sheaf.Paper.SectionExceptionalFibreCoherence
import all Sheaf.Paper.FiniteRingSectionDeformation

/-! # Independence of a smooth section comparison from its Cartesian ambient lift -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.NoetherianSectionSpecialization

/-- Cartesian lifts differ by an automorphism of the new pair. Its trivial action on
the section dualizing line and mate pasting identify the two section comparisons.
Source: sk-prop-sp-purity-bc, orientation factor; sk-thm-dnc, exceptional mate pasting.
(blueprint: lem-sp-smooth-section-exchange-independence). -/
theorem sectionMap_eq_of_cartesian
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y X' Y' : Scheme.{u}} [IsNoetherian Y] [IsNoetherian Y']
    (d : ℕ) (f : X ⟶ Y) (f' : X' ⟶ Y')
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    [IsSeparated f'] [QuasiCompact f'] [HasCompactification f']
    (s : Y ⟶ X) (s' : Y' ⟶ X') [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ f = 𝟙 Y) (hs' : s' ≫ f' = 𝟙 Y')
    (hY : IsUnit (N : Γ(Y, ⊤)))
    (b : Y' ⟶ Y) (v w : X' ⟶ X)
    (sqv : IsPullback v f' f b) (sqw : IsPullback w f' f b)
    (hv : s' ≫ v = b ≫ s) (hw : s' ≫ w = b ≫ s) :
    sectionMap A f f' b v sqv s s' hv = sectionMap A f f' b w sqw s s' hw := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : Smooth f' := SmoothOfRelativeDimension.smooth d f'
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType f'
  let P : ExceptionalSectionPair Y d :=
    { total := X, map := f, sect := s, section_map := hs }
  let P' : ExceptionalSectionPair Y' d :=
    { total := X', map := f', sect := s', section_map := hs' }
  let a : X' ≅ X' := sqw.isoPullback ≪≫ sqv.isoPullback.symm
  have hav : a.hom ≫ v = w := by
    simp only [a, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      sqv.isoPullback_inv_fst, sqw.isoPullback_hom_fst]
  have haf : a.hom ≫ f' = f' := by
    simp only [a, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      sqv.isoPullback_inv_snd, sqw.isoPullback_hom_snd]
  have has : s' ≫ a.hom = (𝟙 Y') ≫ s' := by
    rw [Category.id_comp]
    apply sqv.hom_ext
    · rw [Category.assoc, hav, hv, hw]
    · rw [Category.assoc, haf]
  have sqa : IsPullback a.hom f' f' (𝟙 Y') :=
    IsPullback.of_horiz_isIso ⟨haf.trans (Category.comp_id _).symm⟩
  let ev : ExceptionalSectionChange P P' b := ⟨v, sqv, hv⟩
  let ew : ExceptionalSectionChange P P' b := ⟨w, sqw, hw⟩
  let ea : ExceptionalSectionChange P' P' (𝟙 Y') := ⟨a.hom, sqa, has⟩
  have hinv (y : Y) : IsUnit (N : Y.presheaf.stalk y) := by
    simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y (by trivial)).hom
  have H := section_comparison_comp_at A N hN hA P P' P' hinv b (𝟙 Y') b
    (Category.id_comp b).symm ev ea ew hav.symm
  have hY' : IsUnit (N : Γ(Y', ⊤)) := by
    simpa only [map_natCast] using hY.map b.appTop.hom
  have ha := sectionMap_automorphism A N hN hA d f' s' hs' hY' a sqa has
  simp only [FiniteRingSectionDeformation.sectionExceptionalComparison_eq] at H
  change sectionMap A f f' b w sqw s s' hw =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 Y') b b
      (Category.id_comp b).symm).hom.app (sectionInvariant A f s) ≫
    (ordinaryFinitePullback A (𝟙 Y')).map (sectionMap A f f' b v sqv s s' hv) ≫
    sectionMap A f' f' (𝟙 Y') a.hom sqa s' s' has at H
  rw [ha] at H
  erw [(leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y').hom.naturality] at H
  simp only [Functor.id_map, ← Category.assoc,
    leftDerivedUpperStarComp_id_left_hom_app, Category.id_comp] at H
  exact H.symm

end AlgebraicGeometry.Etale.NoetherianSectionSpecialization
