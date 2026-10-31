/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Normalization of moduli groupoids on scheme charts

Source: Pikaart--de Jong (1995), §§2.3.4--2.3.7; Stacks, Tag 035H
(blueprint: def-sfb-moduli-chart-normalization).

The chart condition uses the actual relative integral-closure construction and its
canonical map from the cover. Compatibility with that map fixes the descent arrows;
local isomorphism of finite covers alone would not do so. All generic components are
retained. For a normal finite cover of a dense open of a normal Noetherian chart,
relative normalization is integral closure in the product of its generic fields.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃ v₄ w₄

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The comparison functor of a specified 2-commutative square, retaining its specified
isomorphism and all arrows. Source: Stacks 003R
(blueprint: def-sfb-moduli-chart-normalization). -/
def moduliTwoFiberLift {S : AlgebraicGeometry.Scheme.{u}}
    {W : BasedCategory.{v₁, w₁} (Over S)} {F : BasedCategory.{v₂, w₂} (Over S)}
    {G : BasedCategory.{v₃, w₃} (Over S)} {H : BasedCategory.{v₄, w₄} (Over S)}
    {f : BasedFunctor F H} {g : BasedFunctor G H}
    (p : BasedFunctor W F) (q : BasedFunctor W G) (e : p.comp f ≅ q.comp g) :
    BasedFunctor W (moduliTwoFiberProduct f g) where
  obj x := ⟨⟨p.obj x, q.obj x, e.hom.toNatTrans.app x⟩,
    ⟨inferInstance, by
      rw [BasedFunctor.w_obj]
      exact e.hom.isHomLift' x⟩⟩
  map a := ObjectProperty.homMk
    { left := p.map a
      right := q.map a
      w := e.hom.toNatTrans.naturality a }
  map_id x := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact p.map_id x
    · exact q.map_id x
  map_comp b c := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact p.map_comp b c
    · exact q.map_comp b c
  w := p.w

/-- Base change of a map on the right factor, including the chosen 2-isomorphism.
Source: Stacks 003R, functoriality of 2-fibre products
(blueprint: def-sfb-moduli-chart-normalization). -/
def moduliTwoFiberMapRight {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {N : BasedCategory.{v₃, w₃} (Over S)} {H : BasedCategory.{v₄, w₄} (Over S)}
    (t : BasedFunctor F H) {v : BasedFunctor G H} {a : BasedFunctor N H}
    (i : BasedFunctor G N) (e : i.comp a ≅ v) :
    BasedFunctor (moduliTwoFiberProduct t v) (moduliTwoFiberProduct t a) where
  obj x := ⟨⟨x.obj.left, i.obj x.obj.right,
    x.obj.hom ≫ e.inv.toNatTrans.app x.obj.right⟩,
    ⟨by
      have : IsIso x.obj.hom := x.property.1
      infer_instance, by
      have := e.inv.isHomLift' x.obj.right
      have := x.property.2
      exact IsHomLift.comp_lift_id_right' H.p (𝟙 (F.p.obj x.obj.left))
        x.obj.hom (G.p.obj x.obj.right) (e.inv.toNatTrans.app x.obj.right)⟩⟩
  map b := ObjectProperty.homMk
    { left := b.hom.left
      right := i.map b.hom.right
      w := by
        dsimp
        rw [← Category.assoc, b.hom.w, Category.assoc,
          e.inv.toNatTrans.naturality b.hom.right]
        exact (Category.assoc _ _ _).symm }
  map_id x := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · exact i.map_id _
  map_comp b c := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · rfl
    · exact i.map_comp _ _
  w := rfl

/-- A scheme presentation of a 2-base change with its actual projection to the test
scheme. Source: Stacks 003R and Pikaart--de Jong §2.3.4
(blueprint: def-sfb-moduli-chart-normalization). -/
def IsSchemeModuliBaseChange {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {f : BasedFunctor F G} {T E : Over S}
    {t : BasedFunctor (discreteModuli (yoneda.obj T)) G}
    (e : BasedFunctor (discreteModuli (yoneda.obj E)) (moduliTwoFiberProduct t f))
    (p : E ⟶ T) : Prop :=
  e.toFunctor.IsEquivalence ∧
    Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst t f))
      (discreteModuliMap (yoneda.map p)))

/-- A representable étale map of moduli groupoids, tested on all scheme base changes.
Source: Stacks 025Y and the atlas convention of Pikaart--de Jong §1.1
(blueprint: def-sfb-moduli-chart-normalization). -/
def IsEtaleModuliMap {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
    ∃ (Z : AlgebraicGeometry.AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange f T t Z p ∧ SpaceMapIsEtale Z T p

end CategoryTheory

namespace AlgebraicGeometry.Over

/-- Relative normalization lifted to the category of schemes over the fixed base.
Source: Stacks 035H (blueprint: def-sfb-moduli-chart-normalization). -/
def normalization {S : Scheme.{u}} {E T : CategoryTheory.Over S} (p : E ⟶ T)
    [QuasiCompact p.left] [QuasiSeparated p.left] : CategoryTheory.Over S :=
  CategoryTheory.Over.mk (p.left.fromNormalization ≫ T.hom)

/-- The actual integral morphism from relative normalization, over the fixed base.
Source: Stacks 035H (blueprint: def-sfb-moduli-chart-normalization). -/
def fromNormalization {S : Scheme.{u}} {E T : CategoryTheory.Over S} (p : E ⟶ T)
    [QuasiCompact p.left] [QuasiSeparated p.left] : normalization p ⟶ T :=
  CategoryTheory.Over.homMk p.left.fromNormalization

/-- The actual dominant map into relative normalization, over the fixed base.
Source: Stacks 035H (blueprint: def-sfb-moduli-chart-normalization). -/
def toNormalization {S : Scheme.{u}} {E T : CategoryTheory.Over S} (p : E ⟶ T)
    [QuasiCompact p.left] [QuasiSeparated p.left] : E ⟶ normalization p :=
  CategoryTheory.Over.homMk p.left.toNormalization (by
    change p.left.toNormalization ≫ (p.left.fromNormalization ≫ T.hom) = E.hom
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
      CategoryTheory.Over.w p])

end AlgebraicGeometry.Over

namespace CategoryTheory

/-- Normalization in a cover, characterized on every normal finite-type étale chart
by relative integral closure and its specified dominant map. The final 2-isomorphism
identifies the chart comparison on the whole cover, fixing its descent arrows.
Here normality means that every local ring is an integrally closed domain.
Source: Pikaart--de Jong §§2.3.4--2.3.7 and Stacks 035H
(blueprint: def-sfb-moduli-chart-normalization). -/
def IsModuliChartNormalization {S : AlgebraicGeometry.Scheme.{u}}
    {V : BasedCategory.{v₁, w₁} (Over S)} {N : BasedCategory.{v₂, w₂} (Over S)}
    {X : BasedCategory.{v₃, w₃} (Over S)}
    (v : BasedFunctor V X) (a : BasedFunctor N X) (i : BasedFunctor V N)
    (e : i.comp a ≅ v) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X),
    (∀ x : T.left, IsDomain (T.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (T.left.presheaf.stalk x)) →
    AlgebraicGeometry.LocallyOfFiniteType T.hom → AlgebraicGeometry.QuasiCompact T.hom →
    IsEtaleModuliMap t →
    ∃ (E : Over S) (p : E ⟶ T) (_ : AlgebraicGeometry.QuasiCompact p.left)
        (_ : AlgebraicGeometry.QuasiSeparated p.left)
        (c : BasedFunctor (discreteModuli (yoneda.obj E)) (moduliTwoFiberProduct t v)),
      IsSchemeModuliBaseChange c p ∧
      ∃ d : BasedFunctor (discreteModuli (yoneda.obj (AlgebraicGeometry.Over.normalization p)))
          (moduliTwoFiberProduct t a),
        IsSchemeModuliBaseChange d (AlgebraicGeometry.Over.fromNormalization p) ∧
        Nonempty (ModuliTwoIso
          ((discreteModuliMap (yoneda.map (AlgebraicGeometry.Over.toNormalization p))).comp d)
          (c.comp (moduliTwoFiberMapRight t i e)))

end CategoryTheory
