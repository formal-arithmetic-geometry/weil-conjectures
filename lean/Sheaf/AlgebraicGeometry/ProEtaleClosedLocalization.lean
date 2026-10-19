/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

/-!
# Closed-site operations under weakly etale localization

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-open-closed-triangle`,
node `lem-exc-closed-localization`, order 1846 (blueprint: lem-exc-closed-localization).

We use constant-coefficient module sheaves, as in the source's site convention.
The first comparison is normalized on every section by the canonical map of fibre
products. The two final equations express compatibility with the closed adjunction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Restriction commutes with closed direct image and closed inverse image, preserving
the unit and counit. Here `pullback i W.hom` is `Z_W`, with projections `v_Z` and `i_W`.
The section formula fixes the direct-image identification; together with the unit and
counit formulas it fixes the inverse-image identification as its adjoint comparison.

Source: Weil conjectures blueprint, smooth purity, order 1846
(blueprint: lem-exc-closed-localization).

Proof:
1. Take `alpha` to be the existing localization restriction base-change map for
   the flipped pullback square. It is invertible by weakly etale base change, and
   its definition gives exactly the required formula on sections.
2. Conjugate `squareLowerStarIso` under the two composite adjunctions to construct
   `beta.inv`. The iterated-mates identity and the known mate of the restriction
   base-change map show that the mate of `beta.inv` is `alpha.hom`.
3. Apply the unit and counit identities for mates. Postcompose the unit identity
   with the direct image of `beta.hom`, and precompose the counit identity with
   the inverse image of `alpha.inv`. Functoriality and the inverse laws of the
   two isomorphisms give the displayed compatibility equations.

The base-change map and its mate are constructed in
`WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale`; the categorical
identities are in `Mathlib.CategoryTheory.Adjunction.Mates`. -/
theorem proEtale_closed_localization {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (W : X.ProEt) (Λ : Type (u + 1)) [CommRing Λ] :
    ∃ alpha : lowerStar (ModuleCat.{u + 1} Λ) i ⋙
          localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop ≅
        localizationRestriction (ModuleCat.{u + 1} Λ)
            (pullback.fst i W.hom) inferInstance ⋙
          lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom),
      ∃ beta : upperStar (ModuleCat.{u + 1} Λ) i ⋙
            localizationRestriction (ModuleCat.{u + 1} Λ)
              (pullback.fst i W.hom) inferInstance ≅
          localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop ⋙
            upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom),
        (∀ (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) (T : W.left.ProEt),
          (alpha.hom.app G).hom.app (op T) =
            G.obj.map (((MorphismProperty.Over.pullbackMapComparison W.prop
              (inferInstance : WeaklyEtale (pullback.fst i W.hom))
              (IsPullback.of_hasPullback i W.hom).flip.toCommSq).app T).op)) ∧
        (∀ F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ),
          (localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop).map
              ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app F) ≫
            alpha.hom.app ((upperStar (ModuleCat.{u + 1} Λ) i).obj F) ≫
            (lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map
              (beta.hom.app F) =
            (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (pullback.snd i W.hom)).unit.app
                ((localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop).obj F)) ∧
        (∀ G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ),
          (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map
              (alpha.inv.app G) ≫
            beta.inv.app ((lowerStar (ModuleCat.{u + 1} Λ) i).obj G) ≫
            (localizationRestriction (ModuleCat.{u + 1} Λ)
                (pullback.fst i W.hom) inferInstance).map
              ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit.app G) =
            (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (pullback.snd i W.hom)).counit.app
                ((localizationRestriction (ModuleCat.{u + 1} Λ)
                  (pullback.fst i W.hom) inferInstance).obj G)) := by
  let sq := (IsPullback.of_hasPullback i W.hom).flip
  generalize hadj : upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i = adj
  generalize hadj' : upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.snd i W.hom) = adj'
  generalize hloc : localizationRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} Λ) W.hom W.prop = loc
  generalize hloc' : localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst i W.hom) inferInstance = loc'
  have := isIso_localizationRestrictionBaseChangeMap_of_isPullback
    (ModuleCat.{u + 1} Λ) sq
  generalize halpha : asIso
    (localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) = alpha
  generalize hbeta : ((conjugateIsoEquiv (adj.comp loc') (loc.comp adj')).symm
    (squareLowerStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq)).symm = beta
  have hc : conjugateEquiv (adj.comp loc') (loc.comp adj') beta.inv =
      (squareLowerStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom := by
    rw [← hbeta]
    exact (conjugateEquiv (adj.comp loc') (loc.comp adj')).apply_symm_apply
      (squareLowerStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
  have hs : (mateEquiv loc' loc
        (TwoSquare.mk _ _ _ _ alpha.hom)).natTrans =
      (squareLowerStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom := by
    rw [← hloc, ← hloc', ← halpha]
    exact mateEquiv_localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq
  have hm : mateEquiv adj adj' (TwoSquare.mk _ _ _ _ beta.inv) =
      TwoSquare.mk _ _ _ _ alpha.hom := by
    apply (mateEquiv loc' loc).injective
    apply TwoSquare.ext
    rw [iterated_mateEquiv_conjugateEquiv]
    intro G
    exact congrArg (fun η ↦ η.app G) (hc.trans hs.symm)
  have hm' := congrArg TwoSquare.natTrans hm
  refine ⟨alpha, beta, ?_, ?_, ?_⟩
  · intro G T
    rw [← halpha]
    rfl
  · intro F
    have h := unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ beta.inv) F
    change _ ≫ ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ beta.inv)).natTrans).app _ =
      _ at h
    rw [hm'] at h
    rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp]
    change adj'.unit.app ((localizationRestriction (ModuleCat.{u + 1} Λ)
      W.hom W.prop).obj F) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map
        (beta.inv.app F ≫ beta.hom.app F) =
      adj'.unit.app ((localizationRestriction (ModuleCat.{u + 1} Λ)
        W.hom W.prop).obj F)
    rw [beta.inv_hom_id_app]
    have hmap :
        (lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map
            (𝟙 ((localizationRestriction (ModuleCat.{u + 1} Λ)
              W.hom W.prop ⋙ upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).obj F)) =
          𝟙 ((lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).obj
            ((localizationRestriction (ModuleCat.{u + 1} Λ)
              W.hom W.prop ⋙ upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).obj F)) :=
      (lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map_id _
    rw [hmap]
    exact Category.comp_id _
  · intro G
    have h := mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ beta.inv) G
    change (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map
        (((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ beta.inv)).natTrans).app G) ≫ _ =
      _ at h
    rw [hm'] at h
    rw [← h, ← Category.assoc, ← Functor.map_comp]
    change (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map
        (alpha.inv.app G ≫ alpha.hom.app G) ≫
      adj'.counit.app ((localizationRestriction (ModuleCat.{u + 1} Λ)
        (pullback.fst i W.hom) inferInstance).obj G) =
      adj'.counit.app ((localizationRestriction (ModuleCat.{u + 1} Λ)
        (pullback.fst i W.hom) inferInstance).obj G)
    rw [alpha.inv_hom_id_app]
    have hmap :
        (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map
            (𝟙 ((localizationRestriction (ModuleCat.{u + 1} Λ)
              (pullback.fst i W.hom) inferInstance ⋙
                lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).obj G)) =
          𝟙 ((upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).obj
            ((localizationRestriction (ModuleCat.{u + 1} Λ)
              (pullback.fst i W.hom) inferInstance ⋙
                lowerStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).obj G)) :=
      (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd i W.hom)).map_id _
    rw [hmap]
    exact Category.id_comp _

end AlgebraicGeometry.ProEtale
