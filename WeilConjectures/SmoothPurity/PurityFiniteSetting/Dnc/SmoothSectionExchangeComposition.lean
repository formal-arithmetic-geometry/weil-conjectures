/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncComparisons
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Composition of smooth section exchanges

The comparison is the specified counit-defined smooth base-change map, pulled back
by the section, with its canonical inverse-image compositors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.Dnc

/-- Section exchange respects composition of Cartesian squares.
Source: blueprint latest, sec-smooth-purity/sk-thm-dnc, Gluing; composition of the
counit-defined exceptional exchanges.
(blueprint: lem-pur-smooth-section-exchange-composition).

Proof: the compact-support exchange respects pasted squares. Taking mates and
applying the coefficient-unit composition equation gives the dualizing base-change
composition equation. Pull it back along the final section. Naturality of the
inverse-image compositors and their associativity identify its prefix with the
two successive section-square comparisons; the adjacent inverse compositors cancel.
-/
theorem section_baseChange_comp (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' B B' B'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian B] [IsNoetherian B'] [IsNoetherian B'']
    (d : ℕ) (f : X ⟶ B) (f' : X' ⟶ B') (f'' : X'' ⟶ B'')
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    [HasInvertibleExponent A X] [HasInvertibleExponent A X']
    {a : X' ⟶ X} {a' : X'' ⟶ X'} {b : B' ⟶ B} {b' : B'' ⟶ B'}
    (sq : IsPullback a f' f b) (sq' : IsPullback a' f'' f' b')
    (s : B ⟶ X) (s' : B' ⟶ X') (s'' : B'' ⟶ X'')
    (hs : s' ≫ a = b ≫ s) (hs' : s'' ≫ a' = b' ≫ s') :
    sectionBaseChange A d f (sq'.paste_horiz sq) s s''
        (by rw [← Category.assoc, hs', Category.assoc, hs, ← Category.assoc]) =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b' b).app _ ≪≫
        (Etale.upperStar (ModuleCat.{u + 1} A) b').leftDerivedFunctor.mapIso
          (sectionBaseChange A d f sq s s' hs) ≪≫
        sectionBaseChange A d f' sq' s' s'' hs' := by
  have hd := Etale.dualizing_base_comp A sq sq'
  have hp := Etale.section_pullback_comp A b b' s s' s'' a a' hs.symm hs'.symm
    (by rw [Category.assoc, ← hs, ← Category.assoc, ← hs', Category.assoc])
    (Etale.dualizingComplex A f)
  apply Iso.ext
  dsimp only [sectionBaseChange, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, asIso_hom, Iso.app_inv]
  rw [hd]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [Etale.sectionCoherencePullbackIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc] at hp
  erw [reassoc_of% hp]
  have hn := ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b' s').symm ≪≫
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s'' a' (b' ≫ s') hs'.symm).hom.naturality
      (Etale.dualizingComplexBaseChangeMap A sq)
  simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc] at hn
  change _ = _ at hn
  erw [← reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc]
  unfold Etale.sectionInvariant
  rfl

/-- Over a fixed base, section exchange is functorial after the identity pullback
comparison. Source: composition and unit coherence of the same section exchange
(blueprint: lem-pur-smooth-section-exchange-composition). -/
theorem section_baseChange_comp_over_id (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' B : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X''] [IsNoetherian B]
    (d : ℕ) (f : X ⟶ B) (f' : X' ⟶ B) (f'' : X'' ⟶ B)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    [HasInvertibleExponent A X] [HasInvertibleExponent A X']
    {a : X' ⟶ X} {a' : X'' ⟶ X'}
    (sq : IsPullback a f' f (𝟙 B)) (sq' : IsPullback a' f'' f' (𝟙 B))
    (s : B ⟶ X) (s' : B ⟶ X') (s'' : B ⟶ X'')
    (hs : s' ≫ a = s) (hs' : s'' ≫ a' = s') :
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).symm.app
      (Etale.sectionInvariant A f s) ≪≫
      sectionBaseChange A d f
        (show IsPullback (a' ≫ a) f'' f (𝟙 B) from
          by simpa only [Category.id_comp] using sq'.paste_horiz sq) s s''
        (by rw [← Category.assoc, hs', hs, Category.id_comp]) =
      ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).symm.app
      (Etale.sectionInvariant A f s) ≪≫
        sectionBaseChange A d f sq s s' (hs.trans (Category.id_comp _).symm)) ≪≫
      ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).symm.app
        (Etale.sectionInvariant A f' s') ≪≫
        sectionBaseChange A d f' sq' s' s'' (hs'.trans (Category.id_comp _).symm)) := by
  have he := section_baseChange_comp A d f f' f'' sq sq' s s' s''
    (hs.trans (Category.id_comp _).symm) (hs'.trans (Category.id_comp _).symm)
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  have heh :
      (sectionBaseChange A d f
        (show IsPullback (a' ≫ a) f'' f (𝟙 B) from
          by simpa only [Category.id_comp] using sq'.paste_horiz sq) s s''
        (by rw [← Category.assoc, hs', hs, Category.id_comp])).hom =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (𝟙 B) (𝟙 B) (𝟙 B) (Category.id_comp _).symm).hom.app
          (Etale.sectionInvariant A f s) ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 B)).leftDerivedFunctor.map
          (sectionBaseChange A d f sq s s'
            (hs.trans (Category.id_comp _).symm)).hom ≫
        (sectionBaseChange A d f' sq' s' s''
          (hs'.trans (Category.id_comp _).symm)).hom := by
    exact congrArg Iso.hom he
  refine (congrArg (fun z ↦
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).inv.app
      (Etale.sectionInvariant A f s) ≫ z) heh).trans ?_
  clear he heh
  have hu := Etale.leftDerivedUpperStarComp_id_left_hom_app
    (ModuleCat.{u + 1} A) (𝟙 B) (Etale.sectionInvariant A f s)
  have hc := congrArg (fun z ↦ z ≫
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).inv.app
      ((Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 B)).leftDerivedFunctor.obj
        (Etale.sectionInvariant A f s))) hu
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at hc
  erw [Category.comp_id] at hc
  have hn := (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).inv.naturality
    (sectionBaseChange A d f sq s s' (hs.trans (Category.id_comp _).symm)).hom
  simp only [Functor.id_map] at hn
  erw [hc, ← reassoc_of% hn]

/-- The identity section square gives the inverse-image identity comparison.
Source: the composition law and cancellation of isomorphisms
(blueprint: lem-pur-smooth-section-exchange-composition). -/
theorem section_baseChange_id (A : Type (u + 1)) [CommRing A] [Finite A]
    {X B : Scheme.{u}} [IsNoetherian X] [IsNoetherian B]
    (d : ℕ) (f : X ⟶ B) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [SmoothOfRelativeDimension d f]
    [HasInvertibleExponent A X] (s : B ⟶ X) :
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).symm.app
      (Etale.sectionInvariant A f s) ≪≫
      sectionBaseChange A d f (IsPullback.id_horiz f) s s
        (by rw [Category.comp_id, Category.id_comp]) = Iso.refl _ := by
  let e : Etale.sectionInvariant A f s ≅ Etale.sectionInvariant A f s :=
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).symm.app
      (Etale.sectionInvariant A f s) ≪≫
    sectionBaseChange A d f (IsPullback.id_horiz f) s s
      (by rw [Category.comp_id, Category.id_comp])
  have h : e = e ≪≫ e := by
    exact
      section_baseChange_comp_over_id A d f f f (IsPullback.id_horiz f)
        (IsPullback.id_horiz f) s s s (Category.comp_id s) (Category.comp_id s)
  have hh := congrArg (fun z ↦ e.symm ≪≫ z) h
  have hh' : e = Iso.refl (Etale.sectionInvariant A f s) := by
    simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using hh.symm
  change e = Iso.refl (Etale.sectionInvariant A f s)
  exact hh'

/-- Equal arrows give the same section comparison, with its source identification.
Source: proof irrelevance for Cartesian squares and functorial pullback.
(blueprint: lem-pur-smooth-section-exchange-composition).
-/
theorem section_baseChange_congr (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' B B' : Scheme.{u}} (d : ℕ) (f : X ⟶ B) (f' : X' ⟶ B')
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    [SmoothOfRelativeDimension d f] [HasInvertibleExponent A X]
    {a a' : X' ⟶ X} {b b' : B' ⟶ B}
    (sq : IsPullback a f' f b) (sq' : IsPullback a' f' f b')
    (s : B ⟶ X) (s' : B' ⟶ X')
    (hs : s' ≫ a = b ≫ s) (hs' : s' ≫ a' = b' ≫ s)
    (ha : a = a') (hb : b = b') :
    sectionBaseChange A d f sq s s' hs =
      eqToIso (congrArg (fun j ↦
        (Etale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj
          (Etale.sectionInvariant A f s)) hb) ≪≫
        sectionBaseChange A d f sq' s s' hs' := by
  subst a'
  subst b'
  simp only [eqToIso_refl, Iso.refl_trans]

/-- Pasting after an identity-base comparison absorbs the identity pullback constraint.
Source: section exchange pasting and inverse-image unit coherence.
(blueprint: lem-pur-smooth-section-exchange-composition).
-/
theorem section_baseChange_comp_right_id (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' B B' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian B] [IsNoetherian B']
    (d : ℕ) (f : X ⟶ B) (f' : X' ⟶ B) (f'' : X'' ⟶ B')
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    [HasInvertibleExponent A X] [HasInvertibleExponent A X']
    {a : X' ⟶ X} {a' : X'' ⟶ X'} {b : B' ⟶ B}
    (sq : IsPullback a f' f (𝟙 B)) (sq' : IsPullback a' f'' f' b)
    (s : B ⟶ X) (s' : B ⟶ X') (s'' : B' ⟶ X'')
    (hs : s' ≫ a = s) (hs' : s'' ≫ a' = b ≫ s') :
    sectionBaseChange A d f
        (show IsPullback (a' ≫ a) f'' f b from
          by simpa only [Category.comp_id] using sq'.paste_horiz sq) s s''
        (by rw [← Category.assoc, hs', Category.assoc, hs]) =
      (Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.mapIso
        ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).symm.app
          (Etale.sectionInvariant A f s) ≪≫
          sectionBaseChange A d f sq s s' (hs.trans (Category.id_comp _).symm)) ≪≫
        sectionBaseChange A d f' sq' s' s'' hs' := by
  have he := section_baseChange_comp A d f f' f'' sq sq' s s' s''
    (hs.trans (Category.id_comp _).symm) hs'
  apply Iso.ext
  have heh :
      (sectionBaseChange A d f
        (show IsPullback (a' ≫ a) f'' f b from
          by simpa only [Category.comp_id] using sq'.paste_horiz sq) s s''
        (by rw [← Category.assoc, hs', Category.assoc, hs])).hom =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b (𝟙 B) b
        (Category.comp_id b).symm).hom.app (Etale.sectionInvariant A f s) ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
          (sectionBaseChange A d f sq s s' (hs.trans (Category.id_comp _).symm)).hom ≫
        (sectionBaseChange A d f' sq' s' s'' hs').hom := congrArg Iso.hom he
  have hu := Etale.leftDerivedUpperStarComp_id_right_hom_app
    (ModuleCat.{u + 1} A) b (Etale.sectionInvariant A f s)
  have hc := congrArg (fun z ↦ z ≫
    (Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
      ((Etale.leftDerivedUpperStarId
        (ModuleCat.{u + 1} A) B).inv.app (Etale.sectionInvariant A f s))) hu
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Category.id_comp] at hc
  simp only [CategoryTheory.Functor.map_id] at hc
  have hc' :
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b (𝟙 B) b
        (Category.comp_id b).symm).hom.app (Etale.sectionInvariant A f s) =
      (Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
        ((Etale.leftDerivedUpperStarId
          (ModuleCat.{u + 1} A) B).inv.app (Etale.sectionInvariant A f s)) :=
    (Category.comp_id _).symm.trans hc
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc] at heh ⊢
  erw [heh, hc']

/-- Pasting before an identity-base comparison absorbs the identity pullback constraint.
Source: section exchange pasting and inverse-image unit coherence.
(blueprint: lem-pur-smooth-section-exchange-composition).
-/
theorem section_baseChange_comp_left_id (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' B B' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian B] [IsNoetherian B']
    (d : ℕ) (f : X ⟶ B) (f' : X' ⟶ B') (f'' : X'' ⟶ B')
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
    [HasInvertibleExponent A X] [HasInvertibleExponent A X']
    {a : X' ⟶ X} {a' : X'' ⟶ X'} {b : B' ⟶ B}
    (sq : IsPullback a f' f b) (sq' : IsPullback a' f'' f' (𝟙 B'))
    (s : B ⟶ X) (s' : B' ⟶ X') (s'' : B' ⟶ X'')
    (hs : s' ≫ a = b ≫ s) (hs' : s'' ≫ a' = s') :
    sectionBaseChange A d f
        (show IsPullback (a' ≫ a) f'' f b from
          by simpa only [Category.id_comp] using sq'.paste_horiz sq) s s''
        (by rw [← Category.assoc, hs', hs]) =
      sectionBaseChange A d f sq s s' hs ≪≫
        ((Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B').symm.app
          (Etale.sectionInvariant A f' s') ≪≫
          sectionBaseChange A d f' sq' s' s'' (hs'.trans (Category.id_comp _).symm)) := by
  have he := section_baseChange_comp A d f f' f'' sq sq' s s' s'' hs
    (hs'.trans (Category.id_comp _).symm)
  apply Iso.ext
  have heh :
      (sectionBaseChange A d f
        (show IsPullback (a' ≫ a) f'' f b from
          by simpa only [Category.id_comp] using sq'.paste_horiz sq) s s''
        (by rw [← Category.assoc, hs', hs])).hom =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 B') b b
        (Category.id_comp b).symm).hom.app (Etale.sectionInvariant A f s) ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 B')).leftDerivedFunctor.map
          (sectionBaseChange A d f sq s s' hs).hom ≫
        (sectionBaseChange A d f' sq' s' s''
          (hs'.trans (Category.id_comp _).symm)).hom := congrArg Iso.hom he
  have hu := Etale.leftDerivedUpperStarComp_id_left_hom_app
    (ModuleCat.{u + 1} A) b (Etale.sectionInvariant A f s)
  have hc := congrArg (fun z ↦ z ≫
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B').inv.app
      ((Etale.upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj
        (Etale.sectionInvariant A f s))) hu
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at hc
  erw [Category.comp_id] at hc
  have hn := (Etale.leftDerivedUpperStarId
    (ModuleCat.{u + 1} A) B').inv.naturality (sectionBaseChange A d f sq s s' hs).hom
  simp only [Functor.id_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom] at heh ⊢
  erw [heh, hc, ← reassoc_of% hn]

end WeilConjectures.PurityFiniteSetting.Dnc
