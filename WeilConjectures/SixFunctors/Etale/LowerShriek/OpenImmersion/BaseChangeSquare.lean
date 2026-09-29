/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!

# Base change for the extension by zero along a cartesian square

Consider a commutative square of schemes

```
U' --j'--> Z'
|          |
g'         g''
|          |
U  --j-->  Z
```

with `j` and `j'` open immersions, i.e. `g' ≫ j = j' ≫ g''`. This file constructs the
canonical base change map

`j'_! ∘ g'^* ⟶ g''^* ∘ j_!`

on sheaves for the small étale sites, and proves that it is an isomorphism when the square
is cartesian. The case where `g'` is the identity is
`AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChange`, and the proof follows
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange`.

The map is the conjugate, under `j_! ⋙ g''^* ⊣ g''_* ⋙ j^*` and `g'^* ⋙ j'_! ⊣ j'^* ⋙ g'_*`,
of the base change map `Etale.baseChangeMap A sq.flip : g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of the
flipped square. It exists for every commutative square and runs against the direction of
the exchange map `Ex_!`, which is defined as its inverse once the square is cartesian.

To prove invertibility, we compute both `g''_* ⋙ j^*` and `j'^* ⋙ g'_*` as composition with
functors of small étale sites: `Over.map j ⋙ Over.pullback g''` sends `T ⟶ U` to
`T ×_Z Z' ⟶ Z'`, and `Over.pullback g' ⋙ Over.map j'` sends it to `T ×_U U' ⟶ Z'`. The
canonical comparison `T ×_U U' ⟶ T ×_Z Z'` is an isomorphism when the square is cartesian.
`AlgebraicGeometry.Etale.baseChangeMap_flip_eq` identifies the base change map with the map
induced by this comparison. Both are mates, under `j'^* ⊣ j'_*` and `j^* ⊣ j_*`, of the
square isomorphism `j'_* ⋙ g''_* ≅ g'_* ⋙ j_*` of pushforwards.

## Main definitions

- `AlgebraicGeometry.Etale.overPullbackMapComparison`: the comparison
  `Over.pullback g' ⋙ Over.map j' ⟶ Over.map j ⋙ Over.pullback g''` of functors of small
  étale sites.
- `AlgebraicGeometry.Etale.openImmersionRestrictionBaseChangeSquare`: the induced map
  `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*`, with pullbacks along open immersions computed as
  restrictions.
- `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`: the base change map
  `g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*`.

## Main results

- `AlgebraicGeometry.Etale.isIso_overPullbackMapComparison`: the comparison of site
  functors is an isomorphism for a cartesian square.
- `AlgebraicGeometry.Etale.baseChangeMap_flip_eq`: the base change map of the flipped
  square is the map induced by the comparison of site functors.
- `AlgebraicGeometry.Etale.isIso_baseChangeMap_flip_of_isPullback`: for a cartesian square
  the base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` is an isomorphism.
- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`: **base change for
  the extension by zero**: for a cartesian square, `j'_! g'^* ⟶ g''^* j_!` is an
  isomorphism.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme MorphismProperty

open Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

section Site

/-- The component at `b : U.Etale` of the comparison of site functors: the canonical
morphism `b ×_U U' ⟶ b ×_Z Z'` over `Z'`. -/
noncomputable def Etale.overPullbackMapComparisonApp (sq : CommSq g' j' j g'') (b : U.Etale) :
    (MorphismProperty.Over.pullback @Etale ⊤ g' ⋙
      MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : @Etale _ _ j')).obj b ⟶
    (MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : @Etale _ _ j) ⋙
      MorphismProperty.Over.pullback @Etale ⊤ g'').obj b :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst b.hom g') (pullback.snd b.hom g' ≫ j')
      (by
        simp only [MorphismProperty.Over.map_obj_hom]
        rw [← Category.assoc, pullback.condition, Category.assoc, sq.w, Category.assoc]))
    (by simp) trivial

@[simp]
lemma Etale.overPullbackMapComparisonApp_left (sq : CommSq g' j' j g'') (b : U.Etale) :
    (Etale.overPullbackMapComparisonApp sq b).left =
      pullback.lift (pullback.fst b.hom g') (pullback.snd b.hom g' ≫ j')
        (by
          simp only [MorphismProperty.Over.map_obj_hom]
          rw [← Category.assoc, pullback.condition, Category.assoc, sq.w, Category.assoc]) :=
  rfl

/-- The comparison `Over.pullback g' ⋙ Over.map j' ⟶ Over.map j ⋙ Over.pullback g''` of
functors of small étale sites, sending `T ⟶ U` étale to the canonical morphism
`T ×_U U' ⟶ T ×_Z Z'` over `Z'`. -/
noncomputable def Etale.overPullbackMapComparison (sq : CommSq g' j' j g'') :
    MorphismProperty.Over.pullback @Etale ⊤ g' ⋙
        MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : @Etale _ _ j') ⟶
      MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : @Etale _ _ j) ⋙
        MorphismProperty.Over.pullback @Etale ⊤ g'' where
  app b := Etale.overPullbackMapComparisonApp sq b
  naturality b b' f := by
    ext
    apply pullback.hom_ext <;> simp

/-- If the square is cartesian, the comparison of site functors is an isomorphism: for
`T ⟶ U` étale, pasting the cartesian square of `T ×_U U'` with the given one identifies
`T ×_U U'` with `T ×_Z Z'`. -/
lemma Etale.isIso_overPullbackMapComparison (hsq : IsPullback g' j' j g'') :
    IsIso (Etale.overPullbackMapComparison hsq.toCommSq) := by
  have (b : U.Etale) : IsIso ((Etale.overPullbackMapComparison hsq.toCommSq).app b) := by
    have h : IsPullback (pullback.fst b.hom g') (pullback.snd b.hom g' ≫ j')
        ((MorphismProperty.Over.map (P := @Etale) ⊤
          (inferInstance : @Etale _ _ j)).obj b).hom g'' := by
      rw [MorphismProperty.Over.map_obj_hom]
      exact (IsPullback.of_hasPullback b.hom g').paste_vert hsq
    have heq : ((Etale.overPullbackMapComparison hsq.toCommSq).app b).left = h.isoPullback.hom := by
      apply pullback.hom_ext <;> simp [Etale.overPullbackMapComparison]
    have : IsIso ((MorphismProperty.Over.forget @Etale ⊤ Z' ⋙ CategoryTheory.Over.forget Z').map
        ((Etale.overPullbackMapComparison hsq.toCommSq).app b)) := by
      change IsIso ((Etale.overPullbackMapComparison hsq.toCommSq).app b).left
      rw [heq]
      infer_instance
    exact isIso_of_reflects_iso _
      (MorphismProperty.Over.forget @Etale ⊤ Z' ⋙ CategoryTheory.Over.forget Z')
  exact NatIso.isIso_of_isIso_app _

end Site

section Sheaf

/-- The composite of base change with the localization functor along an étale morphism is
continuous for the small étale topologies. -/
instance Etale.isContinuous_overPullback_comp_overMap {V U W : Scheme.{u}} (g : W ⟶ U)
    {f : W ⟶ V} (hf : @Etale _ _ f) :
    (MorphismProperty.Over.pullback @Etale ⊤ g ⋙
        MorphismProperty.Over.map (P := @Etale) ⊤ hf).IsContinuous
      (U.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale) :=
  Functor.isContinuous_comp _ _ _ (W.smallGrothendieckTopology @Etale) _

/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` on étale sheaves, with the pullbacks
along the open immersions computed as restrictions along the localization functors. All
functors involved are composition with functors of small étale sites, and the map is the one
induced by `AlgebraicGeometry.Etale.overPullbackMapComparison`. -/
noncomputable def Etale.openImmersionRestrictionBaseChangeSquare (sq : CommSq g' j' j g'') :
    (g'')_*[A] ⋙ Etale.openImmersionRestriction A j ⟶
      Etale.openImmersionRestriction A j' ⋙ (g')_*[A] :=
  Functor.sheafPushforwardContinuousNatTrans (Etale.overPullbackMapComparison sq) A
    (U.smallGrothendieckTopology @Etale) (Z'.smallGrothendieckTopology @Etale)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- If the square is cartesian, the base change map on restrictions is an isomorphism,
being induced by an isomorphism of site functors. -/
lemma Etale.isIso_openImmersionRestrictionBaseChangeSquare (hsq : IsPullback g' j' j g'') :
    IsIso (Etale.openImmersionRestrictionBaseChangeSquare A hsq.toCommSq) := by
  have := Etale.isIso_overPullbackMapComparison hsq
  have : IsIso (Functor.sheafPushforwardContinuousIso
      (asIso (Etale.overPullbackMapComparison hsq.toCommSq)) A
      (U.smallGrothendieckTopology @Etale) (Z'.smallGrothendieckTopology @Etale)).inv :=
    inferInstance
  exact this

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of the flipped square agrees with the map
`Etale.openImmersionRestrictionBaseChangeSquare` induced by the comparison of site functors.

Both are mates, under `j'^* ⊣ j'_*` and `j^* ⊣ j_*`, of natural transformations
`j'_* ⋙ g''_* ⟶ g'_* ⋙ j_*`, and `CategoryTheory.mateEquiv` is a bijection. For the base
change map this mate is the square isomorphism `Etale.squareLowerStarIso`
(`Etale.mateEquiv_baseChangeSquare`). For the site description it is computed on the small
étale sites, where all functors and both adjunctions come from functors of sites. -/
lemma Etale.baseChangeMap_flip_eq (sq : CommSq g' j' j g'') :
    Etale.baseChangeMap A sq.flip =
      Functor.whiskerLeft (g'')_*[A] (Etale.upperStarIsoOpenImmersionRestriction A j).hom ≫
        Etale.openImmersionRestrictionBaseChangeSquare A sq ≫
        Functor.whiskerRight (Etale.upperStarIsoOpenImmersionRestriction A j').inv (g')_*[A] := by
  have hsite : (mateEquiv (Etale.openImmersionRestrictionLowerStarAdjunction A j')
      (Etale.openImmersionRestrictionLowerStarAdjunction A j)
      (TwoSquare.mk ((g'')_*[A]) (Etale.openImmersionRestriction A j')
        (Etale.openImmersionRestriction A j) ((g')_*[A])
        (Etale.openImmersionRestrictionBaseChangeSquare A sq))).natTrans =
      (Etale.squareLowerStarIso A sq.flip).hom := by
    ext F b
    obtain ⟨b⟩ := b
    simp only [mateEquiv, Equiv.coe_fn_mk, Etale.openImmersionRestrictionLowerStarAdjunction,
      Etale.openImmersionRestrictionBaseChangeSquare, Etale.squareLowerStarIso, Etale.lowerStarComp,
      Etale.localizationRestrictionLowerStarAdjunction]
    simp only [Functor.comp_obj, Functor.id_obj, Adjunction.sheafPushforwardContinuous,
      Adjunction.whiskerLeft, Functor.whiskeringLeft_obj_obj, Adjunction.op_unit,
      Adjunction.op_counit, Functor.sheafPushforwardContinuousNatTrans, ObjectProperty.ι_obj,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.leftUnitor_hom_app, comp_id, id_comp,
      ObjectProperty.FullSubcategory.comp_hom, assoc, Functor.leftUnitor_inv_app,
      Functor.op_obj, NatTrans.op_app, MorphismProperty.Over.mapPullbackAdj_counit_app,
      Etale.lowerStar_map_hom_app, MorphismProperty.Over.mapPullbackAdj_unit_app,
      MorphismProperty.Over.pullback_obj_hom,
      Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv, Iso.trans_hom,
      Iso.symm_hom, Functor.sheafPushforwardContinuousComp'_inv_app_hom_app]
    change F.obj.map _ ≫ F.obj.map _ ≫ 𝟙 _ ≫ F.obj.map _ = _
    rw [Category.id_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op, Functor.op_map]
    ext
    simp only [MorphismProperty.Comma.comp_left, MorphismProperty.Over.pullback_map_left,
      MorphismProperty.Over.homMk_hom, overPullbackMapComparison,
      overPullbackMapComparisonApp_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp
    · simp
  have hB : (mateEquiv (Etale.upperStarLowerStarAdjunction A j')
      (Etale.upperStarLowerStarAdjunction A j)
      (TwoSquare.mk ((g'')_*[A]) ((j')^*[A]) ((j)^*[A]) ((g')_*[A])
        (Functor.whiskerLeft (g'')_*[A] (Etale.upperStarIsoOpenImmersionRestriction A j).hom ≫
          Etale.openImmersionRestrictionBaseChangeSquare A sq ≫
          Functor.whiskerRight (Etale.upperStarIsoOpenImmersionRestriction A j').inv
            (g')_*[A]))).natTrans =
      (Etale.squareLowerStarIso A sq.flip).hom := by
    have h1 : TwoSquare.mk ((g'')_*[A]) ((j')^*[A]) ((j)^*[A]) ((g')_*[A])
        (Functor.whiskerLeft (g'')_*[A] (Etale.upperStarIsoOpenImmersionRestriction A j).hom ≫
          Etale.openImmersionRestrictionBaseChangeSquare A sq ≫
          Functor.whiskerRight (Etale.upperStarIsoOpenImmersionRestriction A j').inv
            (g')_*[A]) =
        ((TwoSquare.mk ((g'')_*[A]) (Etale.openImmersionRestriction A j')
          (Etale.openImmersionRestriction A j) ((g')_*[A])
          (Etale.openImmersionRestrictionBaseChangeSquare A sq)).whiskerRight
            (Etale.upperStarIsoOpenImmersionRestriction A j).hom).whiskerLeft
          (Etale.upperStarIsoOpenImmersionRestriction A j').inv := by
      ext F
      simp
    rw [h1, conjugateEquiv_mateEquiv_vcomp _
        (Etale.openImmersionRestrictionLowerStarAdjunction A j') _,
      mateEquiv_conjugateEquiv_vcomp _
        (Etale.openImmersionRestrictionLowerStarAdjunction A j) _]
    simp only [Etale.upperStarIsoOpenImmersionRestriction,
      Etale.upperStarIsoLocalizationRestriction,
      Etale.openImmersionRestrictionLowerStarAdjunction] at hsite ⊢
    rw [conjugateEquiv_leftAdjointUniq_inv, conjugateEquiv_leftAdjointUniq_hom]
    ext F
    simp [hsite]
  exact (mateEquiv (Etale.upperStarLowerStarAdjunction A j')
    (Etale.upperStarLowerStarAdjunction A j)).injective
    ((Etale.mateEquiv_baseChangeSquare A sq.flip).trans hB.symm)

/-- If the square is cartesian, the base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of the
flipped square is an isomorphism: by `AlgebraicGeometry.Etale.baseChangeMap_flip_eq` it is
induced by an isomorphism of site functors. -/
lemma Etale.isIso_baseChangeMap_flip_of_isPullback (hsq : IsPullback g' j' j g'') :
    IsIso (Etale.baseChangeMap A hsq.toCommSq.flip) := by
  have := Etale.isIso_openImmersionRestrictionBaseChangeSquare A hsq
  rw [Etale.baseChangeMap_flip_eq A hsq.toCommSq]
  infer_instance

/-- The base change map for the extension by zero: for a commutative square `g' ≫ j = j' ≫ g''` of
schemes with `j` and `j'` open immersions, the canonical natural transformation
`g'^* ⋙ j'_! ⟶ j_! ⋙ g''^*`, i.e. `j'_! g'^* ⟶ g''^* j_!`. It is the conjugate of the base
change map `Etale.baseChangeMap A sq.flip : g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` under the adjunctions
`j_! ⋙ g''^* ⊣ g''_* ⋙ j^*` and `g'^* ⋙ j'_! ⊣ j'^* ⋙ g'_*`.

This map exists for every commutative square, and it runs *against* the direction of the
exchange map `Ex_!`: the latter is defined through its inverse, which exists when the square
is cartesian (`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`). -/
noncomputable def Etale.openImmersionLowerShriekBaseChangeMap (sq : CommSq g' j' j g'') :
    (g')^*[A] ⋙ (j')_!open[A] ⟶ (j)_!open[A] ⋙ (g'')^*[A] :=
  (conjugateEquiv ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).comp
      (Etale.upperStarLowerStarAdjunction A g''))
    ((Etale.upperStarLowerStarAdjunction A g').comp
      (Etale.openImmersionLowerShriekUpperStarAdjunction A j'))).symm
    (Etale.baseChangeMap A sq.flip)

/-- **Base change for the extension by zero along a cartesian square**: if the square
`g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions is cartesian, the base change map
`j'_! g'^* ⟶ g''^* j_!` is an isomorphism, being the conjugate of the isomorphism
`Etale.baseChangeMap A hsq.toCommSq.flip`. -/
lemma Etale.isIso_openImmersionLowerShriekBaseChangeMap (hsq : IsPullback g' j' j g'') :
    IsIso (Etale.openImmersionLowerShriekBaseChangeMap A hsq.toCommSq) := by
  have := Etale.isIso_baseChangeMap_flip_of_isPullback A hsq
  exact conjugateEquiv_symm_iso _ _ _

end Sheaf

end AlgebraicGeometry
