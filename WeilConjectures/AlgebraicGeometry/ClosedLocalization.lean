/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ClosedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestrictionSupplement

import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Closed-site operations under weakly etale localization

Source: blueprint, sec-proetale-coefficients, sk-prop-sf-open-closed-triangle,
node lem-exc-closed-localization, order 1135 (blueprint: lem-exc-closed-localization).

The operations are the published pro-etale ones: the direct-image square isomorphism
`AlgebraicGeometry.ProEtale.squareLowerStarIso`, its mate the base change map
`AlgebraicGeometry.ProEtale.baseChangeMap`, and the identification
`AlgebraicGeometry.ProEtale.upperStarSquareIso` of the two composites of inverse images
through the diagonal (the blueprint's `lean` declarations). No operation is redefined here.

## Main statements

- `AlgebraicGeometry.ProEtale.closed_localization`: the node's statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u' u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private noncomputable def closed_restrictionPresheafIso {X : Scheme.{u}} (W : X.ProEt)
    (D : Type u') [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D] :
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ⋙
        sheafToPresheaf (ProEt.topology W.left) D ≅
      sheafToPresheaf (ProEt.topology X) D ⋙ (proEtaleBaseChange W.hom).op.lan := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom
    W.prop trivial).op.whiskerLeft D
  let b := (proEtaleBaseChange W.hom).op.lanAdjunction D
  exact Functor.isoWhiskerLeft (sheafToPresheaf (ProEt.topology X) D)
    (a.leftAdjointUniq b)

private theorem closed_restrictionPresheafIso_coprojection {X : Scheme.{u}} (W : X.ProEt)
    (D : Type u') [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : Sheaf (ProEt.topology X) D) (U : W.left.ProEt) :
    ((closed_restrictionPresheafIso W D).hom.app G).app (op U) =
      ((proEtaleBaseChange W.hom).op.leftKanExtensionUnit G.obj).app
          (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) ≫
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj).map
          (proEtaleObjectInverseImageIndexPoint W U).hom.op := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    W.hom W.prop trivial).op.whiskerLeft D
  let b := (proEtaleBaseChange W.hom).op.lanAdjunction D
  have h : (a.leftAdjointUniq b).hom.app G.obj =
      (a.homEquiv _ _).symm (b.unit.app G.obj) := by
    apply (a.homEquiv _ _).injective
    exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a b G.obj).trans
      (Equiv.apply_symm_apply _ _).symm
  change ((a.leftAdjointUniq b).hom.app G.obj).app (op U) = _
  rw [h, Adjunction.homEquiv_counit]
  simp only [a, b, NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, Adjunction.whiskerLeft_counit_app_app,
    Functor.lanAdjunction_unit]
  rfl

private theorem closed_restrictionLan_isSheaf {X : Scheme.{u}} (W : X.ProEt)
    (D : Type u') [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : Sheaf (ProEt.topology X) D) :
    Presheaf.IsSheaf (ProEt.topology W.left)
      (((proEtaleBaseChange W.hom).op.lan).obj G.obj) :=
  (Presheaf.isSheaf_of_iso_iff ((closed_restrictionPresheafIso W D).app G)).mp
    ((AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop).obj G).property

private noncomputable def closed_restrictionComparison {X : Scheme.{u}} (W : X.ProEt)
    (D : Type u') [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology W.left) D] :
    ProEtaleObjectRestrictionComparison W D := by
  let p := closed_restrictionPresheafIso W D
  have hq (G : Sheaf (ProEt.topology X) D) :
      IsIso (toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)) :=
    isIso_toSheafify _ (closed_restrictionLan_isSheaf W D G)
  let e : AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ≅
      proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D :=
    NatIso.ofComponents (fun G ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (p.app G ≪≫ asIso (toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)))) (by
      intro G H f
      apply Sheaf.hom_ext
      change _ ≫ (p.hom.app H ≫ toSheafify _ _) =
        (p.hom.app G ≫ toSheafify _ _) ≫ _
      have hp := p.hom.naturality f
      change ((AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop).map
        f).hom ≫ p.hom.app H = p.hom.app G ≫
          ((proEtaleBaseChange W.hom).op.lan).map f.hom at hp
      rw [← Category.assoc, hp, Category.assoc]
      have hfmap :
          ((proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D).map f).hom =
          sheafifyMap (ProEt.topology W.left)
            (((proEtaleBaseChange W.hom).op.lan).map f.hom) := by
        rfl
      rw [hfmap]
      rw [Category.assoc]
      congr 1
      exact toSheafify_naturality (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).map f.hom))
  exact
    { presheafIso := p
      coprojection := closed_restrictionPresheafIso_coprojection W D
      sheafification_isIso := hq
      sheafIso := e.symm
      sheafIso_inv := fun _ ↦ rfl }


/-- For a chosen cartesian square `g' ≫ w = w' ≫ g` of schemes with `w` weakly etale and
`g` arbitrary (for instance a closed immersion), with pro-etale sheaves valued in a
Grothendieck abelian category `A`: `w'` is weakly etale; the inverse images along `w` and
`w'` are the restrictions to the slices over `W` and `W'` (the comparison data of
`ProEtaleObjectRestrictionComparison` in the coefficient category `A`); the base change map
`w^* g_* ⟶ g'_* w'^*` is an isomorphism; under `w'^* ⊣ w'_*` and `w^* ⊣ w_*` it corresponds
to the identification `g_* w'_* ≅ w_* g'_*` of direct images along the two composites; and
the identification `w^* g'^* ≅ g^* w'^*` of the composites of inverse images through the
diagonal is conjugate, under the composite adjunctions, to that identification of direct
images, i.e. compatible with their units and counits.
Source: blueprint, sec-proetale-coefficients, sk-prop-sf-open-closed-triangle,
node lem-exc-closed-localization, order 1135 (blueprint: lem-exc-closed-localization).

Proof (the node's steps):
1. By the slice identification [lem-weil-pbc-proetale-restriction-injectives] and the
   inverse-image formula [lem-sfb-proetale-object-inverse-image-restriction], the inverse
   image along the weakly etale `w` is restriction to the slice over `W`,
   `(w^*F)(T) = F(T → W → X)`, and likewise for `w'` (weakly etale by base change). The
   base change map is `ε_w ∘ w^* c ∘ w^* g_* η_{w'}`, where `c : g_* w'_* ≅ w_* g'_*` is the
   identification along the equal composites `g ∘ w' = w ∘ g'` of the square
   [def-weil-pbc-cartesian-square], by the direct-image formula `(u_*G)(V) = G(U ×_V V)` of
   [def-weil-pbc-proetale-operations]. Sectionwise, at `G` and `T → W`, it is restriction of
   sections of `G` along `W' ×_W T → Z ×_X T`, which the chosen identification
   `W' ≅ W ×_X Z` makes the canonical isomorphism; so it is bijective for every `T` and `G`,
   and the base change map is an isomorphism (this is
   `AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback`, applied to the pullback
   square given by `isoPullback`, `hom_fst` and `hom_snd`).
2. By construction the base change map is the mate of `c`; the inverse of the mate bijection
   sends it to `w_* g'_* ε_{w'} ∘ w_* β ∘ η_w`, which is `c` by the triangle identities and
   naturality of `c` [def-weil-pbc-cartesian-square, def-weil-pbc-proetale-operations].
3. Composite adjunctions and uniqueness of left adjoints give `(g ∘ w')^* ≅ w'^* g^*` and
   `(w ∘ g')^* ≅ g'^* w^*` (`upperStarComp`, the conjugates of `lowerStarComp`); with the
   diagonal `d = g ∘ w' = w ∘ g'` this gives `w'^* g^* ≅ d^* ≅ g'^* w^*`. Conjugation is
   compatible with composition of isomorphisms and adjunctions (`conjugateEquiv_comp`), and
   the conjugate of the congruence along `d` is the congruence of direct images, so the
   conjugate of this identification is `c`: it is compatible with the units and counits
   [def-weil-pbc-proetale-operations, def-weil-pbc-cartesian-square]. For `g` a closed
   immersion this is the commutation of restriction to `W` with the closed direct image. -/
theorem closed_localization
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {W' Z W X : Scheme.{u}}
    (w' : W' ⟶ Z) (g' : W' ⟶ W) (w : W ⟶ X) (g : Z ⟶ X)
    (sq : ChosenCartesianSquare g' w' w g) [WeaklyEtale w] :
    ∃ (hw' : WeaklyEtale w'),
      Nonempty (ProEtaleObjectRestrictionComparison (@ProEt.mk _ W w inferInstance) A) ∧
      Nonempty (ProEtaleObjectRestrictionComparison (@ProEt.mk _ W' w' hw') A) ∧
      IsIso (ProEtale.baseChangeMap A sq.toCommSq) ∧
      (mateEquiv (upperStarLowerStarAdjunction A w') (upperStarLowerStarAdjunction A w)
          (TwoSquare.mk _ _ _ _ (ProEtale.baseChangeMap A sq.toCommSq))).natTrans =
        (ProEtale.squareLowerStarIso A sq.toCommSq).hom ∧
      conjugateIsoEquiv
          ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A w'))
          ((upperStarLowerStarAdjunction A w).comp (upperStarLowerStarAdjunction A g'))
          (ProEtale.upperStarSquareIso A sq.toCommSq) =
        ProEtale.squareLowerStarIso A sq.toCommSq := by
  have hsq : IsPullback g' w' w g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have hw' : WeaklyEtale w' := by
    rw [← sq.hom_snd]
    infer_instance
  refine ⟨hw', ⟨closed_restrictionComparison (@ProEt.mk _ W w inferInstance) A⟩,
    ⟨closed_restrictionComparison (@ProEt.mk _ W' w' hw') A⟩,
    isIso_baseChangeMap_of_isPullback A hsq, ?_, ?_⟩
  · exact congrArg TwoSquare.natTrans
      ((mateEquiv (upperStarLowerStarAdjunction A w')
        (upperStarLowerStarAdjunction A w)).apply_symm_apply
          (TwoSquare.mk _ _ _ _ (squareLowerStarIso A sq.toCommSq).hom))
  · apply Iso.ext
    change conjugateEquiv
      ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A w'))
      ((upperStarLowerStarAdjunction A w).comp (upperStarLowerStarAdjunction A g'))
      ((upperStarComp A g' w).inv ≫ (upperStarCongr A sq.w).hom ≫
        (upperStarComp A w' g).hom) = _
    rw [← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (g' ≫ w)),
      ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (w' ≫ g))]
    rw [conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarComp_inv]
    have hc := conjugateEquiv_upperStarCongr_inv A sq.w.symm
    change conjugateEquiv _ _ (upperStarCongr A sq.w).hom =
      (lowerStarCongr A sq.w.symm).hom at hc
    rw [hc]
    simp only [squareLowerStarIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]

end AlgebraicGeometry.ProEtale
