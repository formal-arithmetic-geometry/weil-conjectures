/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.CondensedQbarComparisons
import Sheaf.Paper.CondensedQbarPullbackCube
import Sheaf.Paper.CondensedQbarExchangeRightAdjunct

/-! # The exchange equality for condensed finite-to-Qbar coefficient change -/

@[expose] public section

-- Keep resolution constructions out of implicit instance matching.
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

private theorem lifted_naturality
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (PC : ObjectProperty C) (PD : ObjectProperty D)
    (PE : ObjectProperty E) (PF : ObjectProperty F)
    {l : C ⥤ D} {tD : D ⥤ F} {tC : C ⥤ E} {l' : E ⥤ F}
    (hl : ∀ K : PC.FullSubcategory, PD (l.obj K.obj))
    (htD : ∀ K : PD.FullSubcategory, PF (tD.obj K.obj))
    (htC : ∀ K : PC.FullSubcategory, PE (tC.obj K.obj))
    (hl' : ∀ K : PE.FullSubcategory, PF (l'.obj K.obj))
    (α : l ⋙ tD ≅ tC ⋙ l')
    {K M : PC.FullSubcategory} (v : K ⟶ M) :
    (PF.lift (PD.ι ⋙ tD) htD).map ((PD.lift (PC.ι ⋙ l) hl).map v) ≫
        (PF.isoMk (α.app M.obj)).hom =
      (PF.isoMk (α.app K.obj)).hom ≫
        (PF.lift (PE.ι ⋙ l') hl').map ((PE.lift (PC.ι ⋙ tC) htC).map v) := by
  exact ObjectProperty.hom_ext _ (α.hom.naturality v.hom)

private theorem path_exchange {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ A₁₀ A₁₁ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    {e : A₂ ⟶ A₅} {h : A₅ ⟶ A₄} {z : A₁ ⟶ A₆} {j : A₆ ⟶ A₅}
    {p : A₆ ⟶ A₇} {t : A₇ ⟶ A₄} {q : A₀ ⟶ A₈} {w : A₈ ⟶ A₉}
    {s : A₉ ⟶ A₇} {v : A₉ ⟶ A₁₀} {u : A₁₀ ⟶ A₄}
    {x : A₈ ⟶ A₁₁} {y : A₁₁ ⟶ A₁₀}
    (h₁ : c ≫ d = e ≫ h) (h₂ : b ≫ e = z ≫ j)
    (h₃ : j ≫ h = p ≫ t) (h₄ : a ≫ z ≫ p = q ≫ w ≫ s)
    (h₅ : s ≫ t = v ≫ u) (h₆ : w ≫ v = x ≫ y) :
    a ≫ b ≫ c ≫ d = q ≫ x ≫ y ≫ u := by
  rw [h₁, ← Category.assoc b e h, h₂, Category.assoc z j h, h₃]
  rw [← Category.assoc z p t, ← Category.assoc a (z ≫ p) t, h₄]
  simp only [Category.assoc]
  rw [h₅, ← Category.assoc w v u, h₆, Category.assoc]

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

section Edge

variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

private theorem pull_hom_naturality {K M : PadicSubfieldConstructible U ℓ E}
    (v : K ⟶ M) :
    (constructibleToPadicAlgCl T ℓ E).map
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k h).map v) ≫
      (constructibleToQbarPullIso ℓ k E h M).hom =
    (constructibleToQbarPullIso ℓ k E h K).hom ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k h).map
        ((constructibleToPadicAlgCl U ℓ E).map v) := by
  exact lifted_naturality _ _ _ _
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ k h K.obj K.property)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj T ℓ E K.obj K.property)
    (fun K ↦ boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj U ℓ E K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ k h K.obj K.property)
    (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h) v

end Edge

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

attribute [local irreducible] constructibleToQbarPullIso constructibleToQbarPushHom
  boundedConstructibleUpperStar boundedConstructibleLowerStar constructibleToPadicAlgCl
  boundedConstructibleUpperStarLowerStarAdjunction

set_option backward.isDefEq.respectTransparency true in
attribute [-instance] catToReflQuiver in
/-- Normalization of the left side of coefficient exchange under the pullback adjunction.
Source: ModuleObject/Colimit/TwoColimit.lean, final transport paragraph;
ChangeOfCoefficients.lean, derivedPullIso and derivedPushHom;
Mathlib/CategoryTheory/Adjunction/Mates.lean
(blueprint: lem-weil-pbc-qbar-condensed-exchange-left-adjunct).

Proof in words. Expand the left adjunct using functoriality. The adjunct of the Omega base-change
map is its square comparison followed by pullback of the counit: this follows by expanding
the mate, then applying naturality and the triangle identity. Move the push comparison for f
through the square by naturality. Its adjunct is inverse alpha_f followed by scalar extension
of the E counit, since pushHomOfComapIso is the mate of inverse pullIsoOfComapIso; the
iterated mate/conjugation identity proves this assertion. Coefficient pullback comparisons
commute with the specified square comparison: restriction of scalars commutes strictly with
pushforward, these comparisons respect pushforward composition after forgetting module
actions, and localization uniqueness gives the corresponding right-derived coherence.
Conjugating gives coherence for the specified derived pullback composition maps, hence for
the square maps obtained from them and sq.w. Restrict along the fully faithful constructible
inclusions. Substitute this cube identity, use naturality of alpha_g' on the E counit, and
use the E base-change adjunct identity in reverse. Functoriality combines the E base-change
map and its counit, giving exactly the displayed middle expression. Only pullback
comparisons are inverted. No properness or Cartesianity is required. -/
theorem constructibleToQbar_exchange_left_adjunct
    (sq : CommSq g' f' f g) (K : PadicSubfieldConstructible X ℓ E) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').map
      (constructibleToQbarSourceHom ℓ k E f g K ≫
        (boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ k sq).app
          ((constructibleToPadicAlgCl X ℓ E).obj K)) ≫
      (boundedConstructibleUpperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ k f').counit.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').obj
            ((constructibleToPadicAlgCl X ℓ E).obj K)) =
    (constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj
          ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f).obj K))).inv ≫
      (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k f').map
            ((boundedConstructibleBaseChange
              (Profinite.continuousMapRingObj E) ℓ k sq).app K) ≫
          (boundedConstructibleUpperStarLowerStarAdjunction
            (Profinite.continuousMapRingObj E) ℓ k f').counit.app
              ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').obj K)) ≫
      (constructibleToQbarPullIso ℓ k E g' K).hom := by
  have hc := constructibleToQbar_pullback_cube ℓ k E f g f' g' sq
    ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f).obj K)
  have hz := (boundedConstructiblePullbackSquareComparison
    (Profinite.padicAlgClRingObj ℓ) ℓ k sq).hom.naturality
      (constructibleToQbarPushHom ℓ k E f K)
  have hδ := constructibleToQbar_push_counit ℓ k E f K
  have hβ := boundedConstructibleBaseChange_adjunct
    (Profinite.continuousMapRingObj E) ℓ k sq K
  have hβ' := boundedConstructibleBaseChange_adjunct
    (Profinite.padicAlgClRingObj ℓ) ℓ k sq ((constructibleToPadicAlgCl X ℓ E).obj K)
  have hah := pull_hom_naturality ℓ k E g'
    ((boundedConstructibleUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj E) ℓ k f).counit.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hz
  simp only [Functor.comp_obj, Functor.id_obj] at hah
  have hmδ := (boundedConstructibleUpperStar
    (Profinite.padicAlgClRingObj ℓ) ℓ k g').congr_map hδ
  have hmβ := (constructibleToPadicAlgCl X' ℓ E).congr_map hβ
  simp only [Functor.map_comp] at hmδ hmβ
  have hp := path_exchange hβ' hz hmδ hc.symm hah.symm hmβ.symm
  simpa only [constructibleToQbarSourceHom, Functor.map_comp, Category.assoc] using hp

end AlgebraicGeometry.ProEtale.CondensedRing
