/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange

/-!
# Proper coincidence of the exchange maps

In a compact support formalism, for a proper `f` and its trivial compactification `(𝟙 X, f)`,
the compactly supported direct image is the pushforward, `F.shriek (𝟙 X, f) = (𝟙 X)_! ⋙ f_* ≅ f_*`
(`CompactSupportFormalism.shriekOfIsProperIso`), and under this identification the
compact-support exchange map `Ex_!` of a cartesian square is the base change map `Ex_*` of the
pushforwards (`CompactSupportFormalism.shriekBaseChange_ofIsProper`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TwoSquare

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

/-- For a proper `f`, the compactly supported direct image along the trivial compactification
`(𝟙 X, f)` is the pushforward: `F.shriek (𝟙 X, f) = (𝟙 X)_! ⋙ f_* ≅ f_*`. -/
noncomputable def shriekOfIsProperIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    F.shriek (Compactification.ofIsProper f) ≅ F.pf f :=
  Functor.isoWhiskerRight (F.shId X) (F.pf f) ≪≫ Functor.leftUnitor _

variable [F.HasBaseChange] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
  {g' : X' ⟶ X}

/-- Blueprint `cor-cbc-proper-coincidence`: Proper morphisms: compact supports equal direct image

For a cartesian square `g' ≫ f = f' ≫ g` with `f` (hence `f'`) proper, and the trivial
compactifications `(𝟙 X, f)`, `(𝟙 X', f')` lying over each other along `g'`, the compact-support
exchange map `Ex_! : g^* Rf_! ⟶ Rf'_! g'^*` (`def-cbc-exchange-map`) is the base change map
`Ex_* : g^* f_* ⟶ f'_* g'^*` of the pushforwards, under the identifications
`Rf_! = (𝟙 X)_! ⋙ f_* ≅ f_*` and `Rf'_! ≅ f'_*` (`shriekOfIsProperIso`). Consequently
compact-support base change specializes to proper base change for proper `f`. -/
lemma shriekBaseChange_ofIsProper (sq : IsPullback g' f' f g) [IsProper f] [IsProper f']
    (hi : IsPullback g' (Compactification.ofIsProper f').i (Compactification.ofIsProper f).i g') :
    (F.shriekBaseChange (Compactification.ofIsProper f) (Compactification.ofIsProper f') g'
        hi sq).natTrans ≫
        Functor.whiskerLeft (F.pb g') (F.shriekOfIsProperIso f').hom =
      Functor.whiskerRight (F.shriekOfIsProperIso f).hom (F.pb g) ≫
        (F.pfBaseChange g' f' f g sq.w).natTrans := by
  have := HasBaseChange.isIso_baseChange (F := F) hi
  have key : inv (F.baseChange g' (Compactification.ofIsProper f').i
      (Compactification.ofIsProper f).i g' hi.w).natTrans =
      Functor.whiskerRight (F.shId X).hom (F.pb g') ≫ (Functor.leftUnitor _).hom ≫
        (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (F.pb g') (F.shId X').inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    erw [F.baseChange_id_vert g' hi.w]
    ext M
    simp only [Functor.comp_obj, NatTrans.comp_app, whiskerRight_app, Functor.id_obj,
      whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id, Category.id_comp,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Category.assoc, NatTrans.id_app]
    rw [← Functor.map_comp_assoc]
    erw [Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rfl
  ext K
  have hk := congrArg (fun t ↦ t.app K) key
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app] at hk
  simp only [shriekBaseChange, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_obj,
    shriekOfIsProperIso, Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.leftUnitor_hom_app]
  erw [hk]
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  change (F.pfBaseChange g' f' f g sq.w).natTrans.app ((F.sh (𝟙 X)).obj K) ≫
      (F.pf f').map ((F.pb g').map ((F.shId X).hom.app K)) ≫
      (F.pf f').map ((F.shId X').inv.app ((F.pb g').obj K)) ≫
      (F.pf f').map ((F.shId X').hom.app ((F.pb g').obj K)) ≫ 𝟙 _ =
    (F.pb g).map ((F.pf f).map ((F.shId X).hom.app K)) ≫ (F.pb g).map (𝟙 _) ≫
      (F.pfBaseChange g' f' f g sq.w).natTrans.app K
  rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp (F.pf f'), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact ((F.pfBaseChange g' f' f g sq.w).natTrans.naturality ((F.shId X).hom.app K)).symm

end AlgebraicGeometry.CompactSupportFormalism
