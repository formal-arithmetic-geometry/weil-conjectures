/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# Base change for a composite square on unbounded derived categories

Source: Stacks Project, Tag 0EZS, lemma-base-change-compose, and Tag 0E47
(blueprint: sbc-lem-base-change-composition).

Abelian sheaves are encoded as sheaves of modules over `ULift ℤ`, canonically equivalent
to abelian groups in the coefficient universe. No boundedness or torsion is assumed.
-/

@[expose] public section

universe u v

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Pasting

variable (A : Type v) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [HasSmallSiteSheafify A]
  {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X}
  {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}

omit [HasSmallSiteSheafify A] in
open scoped TwoSquare in
/-- **Horizontal pasting of the square isomorphisms**: the square isomorphism of two squares
pasted horizontally is the horizontal composite of the two square isomorphisms, modulo the
composition isomorphisms of the pullbacks along the horizontal maps. -/
private lemma unbounded_derivedSquareUpperStarIso_paste_horiz_hom (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    (derivedSquareUpperStarIso A sq).hom =
      Functor.whiskerRight (leftDerivedUpperStarComp A h g).hom L((f'')^*[A]) ≫
        (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq₁).hom ≫ₕ
          TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq₂).hom).natTrans ≫
        Functor.whiskerLeft L((f)^*[A]) (leftDerivedUpperStarComp A g'' g').inv := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, TwoSquare.hComp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app_assoc
      A f'' h g (g'' ≫ f')
    (h ≫ g) ((g'' ≫ g') ≫ f) sq₂.w rfl (by rw [Category.assoc, sq₁.w, Category.assoc]),
    leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app_assoc
      A g'' f' g (g'' ≫ f')
    (g' ≫ f) ((g'' ≫ g') ≫ f) rfl sq₁.w (by rw [Category.assoc, sq₁.w, Category.assoc]),
    map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app
      A g'' g' f (g'' ≫ g') (g' ≫ f)
    ((g'' ≫ g') ≫ f) rfl rfl rfl, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

omit [HasSmallSiteSheafify A] in
open scoped TwoSquare in
/-- **Horizontal pasting of the base change squares**, in the language of `TwoSquare`: the
base change square of two squares pasted horizontally is the vertical composite (in the sense
of `CategoryTheory.TwoSquare.vComp`: the mates correspondence exchanges the two directions)
of the two base change squares, whiskered by the composition isomorphisms of the pullbacks
along the horizontal maps. -/
private lemma unbounded_derivedBaseChangeSquare_paste_horiz (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    derivedBaseChangeSquare A sq =
      ((derivedBaseChangeSquare A sq₁ ≫ᵥ derivedBaseChangeSquare A sq₂).whiskerRight
        (leftDerivedUpperStarComp A h g).hom).whiskerLeft
        (leftDerivedUpperStarComp A g'' g').inv := by
  have h1 : TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom =
      ((TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq₁).hom ≫ₕ
        TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq₂).hom).whiskerTop
          (leftDerivedUpperStarComp A h g).hom).whiskerBottom
          (leftDerivedUpperStarComp A g'' g').inv := by
    refine TwoSquare.ext _ _ fun F => ?_
    have := NatTrans.congr_app (unbounded_derivedSquareUpperStarIso_paste_horiz_hom A sq₁ sq₂ sq) F
    simpa only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using this
  rw [derivedBaseChangeSquare, h1, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp]

omit [HasSmallSiteSheafify A] in
/-- **Horizontal pasting of the base change maps**, component form: for two squares pasted
horizontally and a sheaf `F` on `X`, the base change map of the pasted square is the
composite `(h ≫ g)^* f_* F ≅ h^* g^* f_* F ⟶ h^* f'_* g'^* F ⟶ f''_* g''^* g'^* F ≅
f''_* (g'' ≫ g')^* F` of the base change maps of the two squares, modulo the composition
isomorphisms of the pullbacks along the horizontal maps. -/
private lemma unbounded_derivedBaseChangeMap_paste_horiz_app (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g))
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedBaseChangeMap A sq).app F =
      (leftDerivedUpperStarComp A h g).hom.app ((R((f)_*[A])).obj F) ≫
        L((h)^*[A]).map ((derivedBaseChangeMap A sq₁).app F) ≫
        (derivedBaseChangeMap A sq₂).app ((L((g')^*[A])).obj F) ≫
        R((f'')_*[A]).map ((leftDerivedUpperStarComp A g'' g').inv.app F) := by
  have := NatTrans.congr_app (unbounded_derivedBaseChangeSquare_paste_horiz A sq₁ sq₂ sq) F
  simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    Functor.comp_obj, Category.assoc] at this
  simp only [derivedBaseChangeMap]
  exact this

end Pasting

/-- Source: Stacks Project, Tag 0EZS (blueprint: sbc-lem-base-change-composition).
For the tower of Cartesian squares, invertibility of the two exchange components implies
invertibility for the outer rectangle, on the full unbounded derived category.

Proof: Paste the Cartesian squares. The inverse-image composition comparisons identify the
outer square comparison with the pasted comparisons. This equality holds termwise on
complexes and descends through localization, since inverse image is exact. Mate pasting and
mate whiskering identify the outer exchange with inverse image of the lower exchange,
followed by the upper exchange and the canonical composition isomorphisms on both ends.
Functors preserve inverses, so every factor is invertible and so is their composite. -/
theorem isIso_derivedBaseChangeMap_app_of_cartesian_tower
    {W Z X Y S T : Scheme.{u}} {j : Z ⟶ W} {k : Z ⟶ Y} {i : W ⟶ X}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (lower : ChosenCartesianSquare h e f g) (upper : ChosenCartesianSquare j k i h)
    (K : DerivedCategoryModule (ULift.{u + 1} ℤ) T)
    (hLower : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      lower.toCommSq.flip).app K))
    (hUpper : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      upper.toCommSq.flip).app
        ((L((e)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)])).obj K))) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (upper.toCommSq.flip.horiz_comp lower.toCommSq.flip)).app K) := by
  have := hLower
  have := hUpper
  rw [unbounded_derivedBaseChangeMap_paste_horiz_app
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) lower.toCommSq.flip upper.toCommSq.flip
    (upper.toCommSq.flip.horiz_comp lower.toCommSq.flip)]
  infer_instance

/-- Source: Stacks Project, Tag 0EZS (blueprint: sbc-lem-base-change-composition).
The independent degreewise assertion for an abelian sheaf and a single nonnegative degree.
The degreewise maps are cohomology of the unbounded exchange on sheaves in degree zero,
as in sbc-def-base-change-map; no invertibility in any other degree is assumed.

Proof: Apply degree-q cohomology to the mate-pasting equality from the preceding argument.
Exact inverse image preserves kernels, images and their quotient, hence commutes naturally
with cohomology, also on derived roofs. The single-complex comparison identifies pullback
of F[0] with (e inverse-image F)[0]. The two middle factors are therefore inverse image of
the lower degree-q map and the upper degree-q map. The outside factors are cohomology of
composition isomorphisms. All four are invertible under the two stated degree-q hypotheses;
the reverse product of their inverses is the inverse of the outer degree-q map. -/
theorem isIso_homology_derivedBaseChangeMap_of_cartesian_tower
    {W Z X Y S T : Scheme.{u}} {j : Z ⟶ W} {k : Z ⟶ Y} {i : W ⟶ X}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (lower : ChosenCartesianSquare h e f g) (upper : ChosenCartesianSquare j k i h)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (q : ℕ)
    (hLower : IsIso ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        lower.toCommSq.flip).app ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))
    (hUpper : IsIso ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        upper.toCommSq.flip).app ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) e).obj F))))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        (upper.toCommSq.flip.horiz_comp lower.toCommSq.flip)).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  let A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
  let K := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let β := (derivedBaseChangeMap A lower.toCommSq.flip).app K
  let τ := derivedBaseChangeMap A upper.toCommSq.flip
  let H := _root_.DerivedCategory.homologyFunctor
    (Sheaf W.smallEtaleTopology A) (q : ℤ)
  have := hLower
  have := hUpper
  have hβ : IsIso (H.map ((L((i)^*[A])).map β)) := by
    apply (NatIso.isIso_map_iff (leftDerivedUpperStarHomologyFunctorIso A i (q : ℤ)) β).mp
    change IsIso ((upperStar A i).map
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).map β))
    infer_instance
  have hτ : IsIso (H.map (τ.app ((L((e)^*[A])).obj K))) := by
    let c := (singleFunctorCompLeftDerivedUpperStarIso A e).app F
    have heq : τ.app ((L((e)^*[A])).obj K) =
        (R((h)_*[A]) ⋙ L((i)^*[A])).map c.hom ≫
          τ.app ((_root_.DerivedCategory.singleFunctor _ 0).obj ((upperStar A e).obj F)) ≫
          (L((k)^*[A]) ⋙ R((j)_*[A])).map c.inv := by
      have hn := τ.naturality c.hom
      dsimp only [Functor.comp_obj] at hn
      rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
      simp only [Iso.hom_inv_id, CategoryTheory.Functor.map_id]
      exact (CategoryTheory.Category.comp_id _).symm
    rw [heq, H.map_comp, H.map_comp]
    infer_instance
  change IsIso (H.map ((derivedBaseChangeMap A
    (upper.toCommSq.flip.horiz_comp lower.toCommSq.flip)).app K))
  rw [unbounded_derivedBaseChangeMap_paste_horiz_app A lower.toCommSq.flip
    upper.toCommSq.flip (upper.toCommSq.flip.horiz_comp lower.toCommSq.flip)]
  simp only [Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Etale
