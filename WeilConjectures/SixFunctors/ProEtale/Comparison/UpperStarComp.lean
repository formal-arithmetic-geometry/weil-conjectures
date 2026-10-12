/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

/-!
# The comparison of pullbacks is compatible with composition

The isomorphisms `σ_h : h^* ν^* ≅ ν^* h^*`
(`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`) comparing the pullbacks of
pro-étale and of étale sheaves along a morphism of schemes `h` are compatible with the
composition isomorphisms of pullbacks (`comparisonUpperStarCompUpperStarIso_comp`) and with the
identification of the two composites around a commutative square
(`comparisonUpperStarCompUpperStarIso_square`). Both follow by conjugation from the
corresponding compatibilities of the pushforward functors, which hold on sections.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Comp

variable {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The isomorphisms `f_* ν_* ≅ ν_* f_*` are compatible with the composition of
pushforwards. -/
lemma lowerStarCompComparisonLowerStarIso_comp_inv_app (G : Sheaf (ProEt.topology T) A) :
    (lowerStarCompComparisonLowerStarIso (h₁ ≫ h₂) A).inv.app G =
      (Etale.lowerStarComp A h₁ h₂).inv.app ((comparisonLowerStar A T).obj G) ≫
      (Etale.lowerStar A h₂).map ((lowerStarCompComparisonLowerStarIso h₁ A).inv.app G) ≫
      (lowerStarCompComparisonLowerStarIso h₂ A).inv.app ((ProEtale.lowerStar A h₁).obj G) ≫
      (comparisonLowerStar A R).map ((ProEtale.lowerStarComp A h₁ h₂).hom.app G) := by
  ext U : 3
  dsimp [lowerStarCompComparisonLowerStarIso, Etale.lowerStarComp, ProEtale.lowerStarComp,
    Etale.lowerStar, ProEtale.lowerStar, comparisonLowerStar]
  simp
  sorry

/-- Blueprint `lem-weil-pbc-comparison-pullback` (compatibility with composites): the comparison
`σ_{h₁ ≫ h₂}` is the composite of `σ_{h₂}` and `σ_{h₁}`, up to the composition isomorphisms of
the pullbacks. -/
lemma comparisonUpperStarCompUpperStarIso_comp :
    (comparisonUpperStarCompUpperStarIso A (h₁ ≫ h₂)).hom =
      Functor.whiskerLeft (comparisonUpperStar A R) (ProEtale.upperStarComp A h₁ h₂).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (comparisonUpperStarCompUpperStarIso A h₂).hom
        (ProEtale.upperStar A h₁) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Etale.upperStar A h₂) (comparisonUpperStarCompUpperStarIso A h₁).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.upperStarComp A h₁ h₂).inv (comparisonUpperStar A T) := by
  refine conjugateEquiv_paste_eq (Etale.upperStarLowerStarAdjunction A h₁)
    (Etale.upperStarLowerStarAdjunction A h₂) (Etale.upperStarLowerStarAdjunction A (h₁ ≫ h₂))
    (ProEtale.upperStarLowerStarAdjunction A h₁) (ProEtale.upperStarLowerStarAdjunction A h₂)
    (ProEtale.upperStarLowerStarAdjunction A (h₁ ≫ h₂)) (comparisonAdjunction A R)
    (comparisonAdjunction A S) (comparisonAdjunction A T) _ _ _ _ _ ?_
  have hσ : ∀ {Y X : Scheme.{u}} (g : Y ⟶ X),
      conjugateEquiv ((Etale.upperStarLowerStarAdjunction A g).comp (comparisonAdjunction A Y))
        ((comparisonAdjunction A X).comp (ProEtale.upperStarLowerStarAdjunction A g))
        (comparisonUpperStarCompUpperStarIso A g).hom =
        (lowerStarCompComparisonLowerStarIso g A).inv := fun g ↦
    congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply
      (lowerStarCompComparisonLowerStarIso g A).symm)
  have hE : conjugateEquiv (Etale.upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      ((Etale.upperStarLowerStarAdjunction A h₂).comp (Etale.upperStarLowerStarAdjunction A h₁))
      (Etale.upperStarComp A h₁ h₂).inv = (Etale.lowerStarComp A h₁ h₂).inv :=
    congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply
      (Etale.lowerStarComp A h₁ h₂).symm)
  have hP : conjugateEquiv
      ((ProEtale.upperStarLowerStarAdjunction A h₂).comp
        (ProEtale.upperStarLowerStarAdjunction A h₁))
      (ProEtale.upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      (ProEtale.upperStarComp A h₁ h₂).hom = (ProEtale.lowerStarComp A h₁ h₂).hom :=
    congrArg Iso.inv ((conjugateIsoEquiv _ _).apply_symm_apply
      (ProEtale.lowerStarComp A h₁ h₂).symm)
  rw [hσ, hσ, hσ, hE, hP]
  refine NatTrans.ext (funext fun G ↦ ?_)
  simpa using lowerStarCompComparisonLowerStarIso_comp_inv_app A h₁ h₂ G

/-- The componentwise form of `comparisonUpperStarCompUpperStarIso_comp`, for the inverses. -/
@[reassoc]
lemma comparisonUpperStarCompUpperStarIso_comp_inv_app (M : Sheaf R.smallEtaleTopology A) :
    (comparisonUpperStar A T).map ((Etale.upperStarComp A h₁ h₂).hom.app M) ≫
        (comparisonUpperStarCompUpperStarIso A h₁).inv.app ((Etale.upperStar A h₂).obj M) ≫
        (ProEtale.upperStar A h₁).map ((comparisonUpperStarCompUpperStarIso A h₂).inv.app M) =
      (comparisonUpperStarCompUpperStarIso A (h₁ ≫ h₂)).inv.app M ≫
        (ProEtale.upperStarComp A h₁ h₂).hom.app ((comparisonUpperStar A R).obj M) := by
  have h := NatTrans.congr_app (comparisonUpperStarCompUpperStarIso_comp A h₁ h₂) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at h
  rw [← cancel_epi ((comparisonUpperStarCompUpperStarIso A (h₁ ≫ h₂)).hom.app M),
    Iso.hom_inv_id_app_assoc, h]
  simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  simp [← Functor.map_comp]

end Comp

section Square

variable {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

/-- The componentwise form of `comparisonUpperStarCompUpperStarIso_comp` for the composition
isomorphism `Etale.upperStarComp` along a morphism `h₁₂` equal to `h₁ ≫ h₂`. -/
@[reassoc]
lemma comparisonUpperStarCompUpperStarIso_comp_inv_app' (h₁₂ : T ⟶ R)
    (hh₁₂ : h₁₂ = h₁ ≫ h₂) (M : Sheaf R.smallEtaleTopology A) :
    (comparisonUpperStar A T).map ((Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app M) ≫
        (comparisonUpperStarCompUpperStarIso A h₁).inv.app ((Etale.upperStar A h₂).obj M) ≫
        (ProEtale.upperStar A h₁).map ((comparisonUpperStarCompUpperStarIso A h₂).inv.app M) =
      (comparisonUpperStarCompUpperStarIso A h₁₂).inv.app M ≫
        eqToHom (by rw [hh₁₂]) ≫
        (ProEtale.upperStarComp A h₁ h₂).hom.app ((comparisonUpperStar A R).obj M) := by
  subst hh₁₂
  simpa using comparisonUpperStarCompUpperStarIso_comp_inv_app A h₁ h₂ M

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Blueprint `lem-weil-pbc-comparison-pullback` (compatibility with the cartesian
identification): around a commutative square, the comparisons `σ` of the four sides are
compatible with the identifications `g^* f'^* ≅ f^* g'^*` of the pullbacks of étale
(`AlgebraicGeometry.Etale.squareUpperStarIso`) and of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.upperStarCompIso`). -/
lemma comparisonUpperStarCompUpperStarIso_square (sq : CommSq g' f' f g)
    (M : Sheaf Y.smallEtaleTopology A) :
    (comparisonUpperStar A X').map ((Etale.squareUpperStarIso A sq).hom.app M) ≫
        (comparisonUpperStarCompUpperStarIso A g').inv.app ((Etale.upperStar A f).obj M) ≫
        (ProEtale.upperStar A g').map ((comparisonUpperStarCompUpperStarIso A f).inv.app M) =
      (comparisonUpperStarCompUpperStarIso A f').inv.app ((Etale.upperStar A g).obj M) ≫
        (ProEtale.upperStar A f').map ((comparisonUpperStarCompUpperStarIso A g).inv.app M) ≫
        (ProEtale.upperStarCompIso A sq.w.symm).hom.app ((comparisonUpperStar A Y).obj M) := by
  have h₁ := comparisonUpperStarCompUpperStarIso_comp_inv_app' A g' f (g' ≫ f) rfl M
  have h₂ := comparisonUpperStarCompUpperStarIso_comp_inv_app' A f' g (g' ≫ f) sq.w M
  simp only [Etale.squareUpperStarIso, ProEtale.upperStarCompIso, ProEtale.upperStarCongr,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    eqToIso.hom, eqToHom_app]
  rw [h₁, ← cancel_epi ((comparisonUpperStar A X').map
    ((Etale.upperStarComp A f' g (g' ≫ f) sq.w).hom.app M)), ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Category.id_comp, reassoc_of% h₂]
  simp

end Square

end AlgebraicGeometry.ProEtale
