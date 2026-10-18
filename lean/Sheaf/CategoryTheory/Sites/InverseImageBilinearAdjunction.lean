/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# Bilinear adjunction for inverse images of sites

Source: Stacks Project, Tag 03EL, lemma-tensor-product-pullback, third equality;
Sites, Section 00YR and Proposition 00YV(2)
(blueprint: lem-sfb-site-inverse-image-bilinear-adjunction).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v w u₁ v₁ u₂ v₂

namespace CategoryTheory

/-- A morphism of underlying sheaves of sets that is separately additive on sections.

The `natural` field is naturality of a map from the sectionwise product; it does
not require additivity for the abelian group structure on that product.
Source: Stacks Project, Tag 03EL, definition before lemma-tensor-product-pullback
(blueprint: lem-sfb-site-inverse-image-bilinear-adjunction). -/
structure SiteBilinearMap {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F G H : Sheaf J AddCommGrpCat.{w}) where
  /-- The sectionwise two-variable map. -/
  app : ∀ U : C, F.obj.obj (Opposite.op U) → G.obj.obj (Opposite.op U) →
    H.obj.obj (Opposite.op U)
  /-- Compatibility with restriction of sections. -/
  natural : ∀ {U V : C} (f : U ⟶ V) (x : F.obj.obj (Opposite.op V))
    (y : G.obj.obj (Opposite.op V)),
    app U (F.obj.map f.op x) (G.obj.map f.op y) = H.obj.map f.op (app V x y)
  /-- Additivity in the first variable. -/
  add_left : ∀ (U : C) (x₁ x₂ : F.obj.obj (Opposite.op U)) (y : G.obj.obj (Opposite.op U)),
    app U (x₁ + x₂) y = app U x₁ y + app U x₂ y
  /-- Additivity in the second variable. -/
  add_right : ∀ (U : C) (x : F.obj.obj (Opposite.op U)) (y₁ y₂ : G.obj.obj (Opposite.op U)),
    app U x (y₁ + y₂) = app U x y₁ + app U x y₂

/-- The sectionwise unit of the canonical site inverse-image/direct-image adjunction.

Source: Stacks Project, Sites, Section 00YR and Proposition 00YV(2)
(blueprint: lem-sfb-site-inverse-image-bilinear-adjunction). -/
noncomputable def siteAdjunctionUnitSection
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
    (F : Sheaf J AddCommGrpCat.{w}) (U : C) :
    F.obj.obj (Opposite.op U) →
      ((u.sheafPullback AddCommGrpCat.{w} J K).obj F).obj.obj
        (Opposite.op (u.obj U)) :=
  fun x ↦ ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom.app
    (Opposite.op U) x

/-- The two-unit formula is a natural bijection on separately additive sheaf maps.

The precoverages satisfy the recorded site axioms. `hcover` and `hpullback` are
Stacks continuity; `IsContinuous` is the induced sheaf-preservation property used
by Mathlib's interface. Finite limits are preserved on sheaves of sets. Values
lie in the common universe containing both sites, with no equality imposed on
their object and morphism universes. The last clause expresses naturality: whenever
`β₀ = h ∘ β₁ ∘ (L a × L c)` on sections, the same equation holds after transposition,
with `a`, `c` and `R h`. Sectionwise equality determines these underlying sheaf maps.

Source: Stacks Project, Tag 03EL, third equality in lemma-tensor-product-pullback
(blueprint: lem-sfb-site-inverse-image-bilinear-adjunction).

Proof:
1. The size convention def-weil-size-convention supplies the common value universe.
   By def-weil-pbc-sites-and-cohomology, R is restriction and preserves finite
   products. Identify abelian sheaves with commutative group objects using
   lem-weil-pbc-sheaf-algebraic-structures-objects. Lift L ⊣ R using
   lem-weil-pbc-adjunction-lifts-abelian-group-objects: its multiplication is
   L(+) after the inverse product comparison, and unit and counit are additive.
2. For underlying set maps use the ordinary adjunction after the product
   comparison λ : L(F × G) ≅ LF × LG. The forward map is R(βλ)η, and the
   inverse is ε L(b)λ⁻¹. Naturality of η with both projections identifies the
   forward map with R(β) after the two units and the inverse R-product comparison.
3. The two units are additive, so the forward map preserves separate additivity
   by expanding β(η(x + x'), η(y)) and β(η(x), η(y + y')).
4. Express the two additivity laws for b as equalities of maps from F × F × G
   and F × G × G. Apply L and identify all products by λ. Comparing projections
   shows λ L⟨q,r⟩ = ⟨Lq,Lr⟩; the resulting identities are the two additivity
   laws of L(b)λ⁻¹. Preservation of zero and negatives follows by cancellation.
5. Postcompose with the additive counit. Both directions are now separately
   additive and are inverse by counit naturality and the two triangle identities.
6. For a, c and h, functoriality of R and unit naturality give the displayed
   naturality equality, contravariantly in F,G and covariantly in H. -/
theorem site_inverse_image_bilinear_adjunction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (u : C ⥤ D)
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map u ∈ K (u.obj X))
    (hpullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) u)
    [u.IsContinuous J.toGrothendieck K.toGrothendieck]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
      J.toGrothendieck K.toGrothendieck).IsRightAdjoint]
    [PreservesFiniteLimits
      (u.sheafPullback (Type (max u₁ v₁ u₂ v₂ w)) J.toGrothendieck K.toGrothendieck)] :
    ∃ e : ∀ (F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (H : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}),
        SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G) H →
        SiteBilinearMap F G
          ((u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj H),
      (∀ (F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (H : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}),
        Function.Bijective (e F G H)) ∧
      (∀ (F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (H : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w})
        (β : SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G) H)
        (U : C) (x : F.obj.obj (Opposite.op U)) (y : G.obj.obj (Opposite.op U)),
        (e F G H β).app U x y = β.app (u.obj U)
          (siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u F U x)
          (siteAdjunctionUnitSection J.toGrothendieck K.toGrothendieck u G U y)) ∧
      (∀ {F₀ F₁ G₀ G₁ : Sheaf J.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}}
        {H₀ H₁ : Sheaf K.toGrothendieck AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}}
        (a : F₀ ⟶ F₁) (c : G₀ ⟶ G₁) (h : H₀ ⟶ H₁)
        (β₁ : SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F₁)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G₁) H₀)
        (β₀ : SiteBilinearMap
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F₀)
          ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G₀) H₁),
        (∀ (V : D)
          (x : ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj F₀).obj.obj (Opposite.op V))
          (y : ((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
            J.toGrothendieck K.toGrothendieck).obj G₀).obj.obj (Opposite.op V)),
          β₀.app V x y = h.hom.app (Opposite.op V)
            (β₁.app V
              (((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
                J.toGrothendieck K.toGrothendieck).map a).hom.app (Opposite.op V) x)
              (((u.sheafPullback AddCommGrpCat.{max u₁ v₁ u₂ v₂ w}
                J.toGrothendieck K.toGrothendieck).map c).hom.app (Opposite.op V) y))) →
        ∀ (U : C) (x : F₀.obj.obj (Opposite.op U)) (y : G₀.obj.obj (Opposite.op U)),
          (e F₀ G₀ H₁ β₀).app U x y = h.hom.app (Opposite.op (u.obj U))
            ((e F₁ G₁ H₀ β₁).app U
              (a.hom.app (Opposite.op U) x) (c.hom.app (Opposite.op U) y))) := by
  sorry

end CategoryTheory
