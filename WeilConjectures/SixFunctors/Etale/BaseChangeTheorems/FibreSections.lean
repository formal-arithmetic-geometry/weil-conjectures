/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal

/-!
# Stalks of a direct image and sections over the geometric fibre

Let `f : X ⟶ Y` be a morphism of schemes, `ȳ : Spec Ω ⟶ Y` a geometric point and
`X_ȳ = X ×_Y Spec Ω` the geometric fibre, with projection `a : X_ȳ ⟶ X`. For an abelian étale
sheaf `F` on `X`, a germ at `ȳ` of a section of `f_* F` is represented by a section `s` of `F`
over `X ×_Y V` for a pointed étale neighbourhood `(V, v)` of `ȳ`; restricting `s` along
`X_ȳ ⟶ X ×_Y V` defines the comparison map
`AlgebraicGeometry.Etale.stalkToFibreSections : (f_* F)_ȳ ⟶ Γ(X_ȳ, a^* F)`.

For `f` proper and `Ω` algebraically closed this map is bijective
(`AlgebraicGeometry.Etale.bijective_stalkToFibreSections_of_isProper`): the stalk is the colimit
of the sections over the `X ×_Y V`, which is the group of sections over `X ×_Y S_(ȳ)` for the
strict localization `S_(ȳ)` (continuity of sections at inverse limits), which is the group of
sections over the closed geometric fibre (the degree-zero comparison over the strictly henselian
local ring of `S_(ȳ)`), which is the group of sections over `X_ȳ` (invariance of sections under
extension of algebraically closed base fields).

## Main definitions

- `AlgebraicGeometry.Etale.stalkToFibreSections`: the comparison map.

## Main statements

- `AlgebraicGeometry.Etale.bijective_stalkToFibreSections_of_isProper`: it is bijective for
  proper `f` and algebraically closed `Ω`.

## References

- Stacks Project, Lemma 59.91.4, <https://stacks.math.columbia.edu/tag/0A3S>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

variable {X Y Xy : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) (a : Xy ⟶ X) (b : Xy ⟶ Spec (.of Ω)) (hab : a ≫ f = b ≫ y)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The morphism from the fibre `X_y` to the base change `V ×_Y X` given by a lift `v` of the
geometric point `y` to the étale `Y`-scheme `V`. -/
noncomputable def fibreToPullback (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    Xy ⟶ pullback V.hom f :=
  pullback.lift (b ≫ v.left) a (by
    rw [Category.assoc, show v.left ≫ V.hom = y from CategoryTheory.Over.w v, hab])

@[reassoc (attr := simp)]
lemma fibreToPullback_snd (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    fibreToPullback f y a b hab V v ≫ pullback.snd V.hom f = a :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma fibreToPullback_fst (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    fibreToPullback f y a b hab V v ≫ pullback.fst V.hom f = b ≫ v.left :=
  pullback.lift_fst _ _ _

/-- The restriction of a section of `F` over `V ×_Y X` to the fibre `X_y`, along the morphism
`AlgebraicGeometry.Etale.fibreToPullback` given by a lift `v` of `y` to `V`, as a morphism of
abelian groups. -/
noncomputable def fibreRestriction (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V) :
    ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op V) ⟶
      ((a)^*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Xy))) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app F).hom.app
      (op (f.Etale.obj V)) ≫
    ((a)^*[AddCommGrpCat.{u + 1}].obj F).obj.map (homToPullback a
      (V := Scheme.Etale.mk (𝟙 Xy)) (U := f.Etale.obj V) (fibreToPullback f y a b hab V v)
      ((fibreToPullback_snd f y a b hab V v).trans (Category.id_comp a).symm)).op

lemma fibreRestriction_apply (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
    (s : ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op V)) :
    fibreRestriction f y a b hab F V v s =
      pullSection a F (V := Scheme.Etale.mk (𝟙 Xy)) (U := f.Etale.obj V)
        (fibreToPullback f y a b hab V v)
        ((fibreToPullback_snd f y a b hab V v).trans (Category.id_comp a).symm) s :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The restriction to the fibre is compatible with the restriction maps of the direct image. -/
lemma fibreRestriction_map {V W : Y.Etale} (φ : V ⟶ W) (v : (pointSmallEtale y).fiber.obj V)
    (s : ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op W)) :
    fibreRestriction f y a b hab F V v (((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.map φ.op s) =
      fibreRestriction f y a b hab F W ((pointSmallEtale y).fiber.map φ v) s := by
  rw [fibreRestriction_apply, fibreRestriction_apply]
  change pullSection a F _ _ (F.obj.map (f.Etale.map φ).op s) = _
  rw [← pullSection_comp]
  exact pullSection_congr _ _ _ (by apply pullback.hom_ext <;> simp [Scheme.Hom.Etale] <;> rfl) _

lemma fibreRestriction_comp {V W : Y.Etale} (φ : V ⟶ W) (v : (pointSmallEtale y).fiber.obj V) :
    ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.map φ.op ≫ fibreRestriction f y a b hab F V v =
      fibreRestriction f y a b hab F W ((pointSmallEtale y).fiber.map φ v) := by
  ext s
  exact (ConcreteCategory.comp_apply _ _ _).trans (fibreRestriction_map f y a b hab F φ v s)

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison map** `(f_* F)_y ⟶ Γ(X_y, a^* F)` from the stalk of the direct image at a
geometric point to the sections over the geometric fibre: a germ represented by a section of
`F` over `V ×_Y X` is sent to its restriction to the fibre. -/
noncomputable def stalkToFibreSections :
    (pointSmallEtale y).presheafFiber.obj ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj ⟶
      ((a)^*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Xy))) :=
  (pointSmallEtale y).presheafFiberDesc (fibreRestriction f y a b hab F)
    (fun _ _ φ v ↦ fibreRestriction_comp f y a b hab F φ v)

lemma toPresheafFiber_stalkToFibreSections (V : Y.Etale) (v : (pointSmallEtale y).fiber.obj V)
    (s : ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op V)) :
    stalkToFibreSections f y a b hab F
        ((pointSmallEtale y).toPresheafFiber V v ((f)_*[AddCommGrpCat.{u + 1}].obj F).obj s) =
      fibreRestriction f y a b hab F V v s := by
  rw [← ConcreteCategory.comp_apply, stalkToFibreSections,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _
      (fun _ _ φ v ↦ fibreRestriction_comp f y a b hab F φ v)]

end AlgebraicGeometry.Etale
