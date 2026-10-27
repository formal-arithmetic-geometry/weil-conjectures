/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.AlgebraicGeometry.SpaceSquareZeroStalkData

/-! # Extensions with a fixed base-ideal map and their kernel pushouts

Source: Stacks Project, Deformation Theory, setup of Tag 0D3Q
(blueprint: def-sfb-space-fixed-ideal-extensions).

The map from the inverse-image ideal is encoded, by scalar extension adjunction,
as an O_X-linear map f^*J → F. Pushout is specified by its full universal property
among extensions, including arbitrary target kernels, with its natural arrows.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- Algebra maps with the specified map on kernels and identity on the quotient.
Source: Stacks, Tag 0D3Q (blueprint: def-sfb-space-fixed-ideal-extensions). -/
def SpaceExtensionMap {f : X ⟶ B} {F G : X.Modules} (u : F ⟶ G)
    (E : SpaceSquareZeroExtension f F) (D : SpaceSquareZeroExtension f G) :=
  {a : E.algebra.obj ⟶ D.algebra.obj //
    a ≫ D.quotient = E.quotient ∧
    (∀ (U : X.EtaleSite) (m : F.val.obj (op U)),
      a.app (op U) (E.inclusion U m) = D.inclusion U (u.val.app (op U) m)) ∧
    ∀ (U : X.EtaleSite) (V : B.EtaleSite) (b : U.obj.left ⟶ V.obj.left)
      (hb : U.obj.hom ≫ f.hom.hom = yoneda.map b ≫ V.obj.hom),
      E.base.app U V b hb ≫ a.app (op U) = D.base.app U V b hb}

/-- Identity of an extension. Source: Stacks, Tag 0D3Q
(blueprint: def-sfb-space-fixed-ideal-extensions). -/
def SpaceExtensionMap.id {f : X ⟶ B} {F : X.Modules}
    (E : SpaceSquareZeroExtension f F) : SpaceExtensionMap (𝟙 F) E E :=
  ⟨𝟙 _, by
    refine ⟨Category.id_comp _, ?_, ?_⟩
    · intro U m; rfl
    · intro U V b hb; exact Category.comp_id _⟩

/-- Composition over the composite coefficient map. Source: Stacks, Tag 0D3Q
(blueprint: def-sfb-space-fixed-ideal-extensions). -/
def SpaceExtensionMap.comp {f : X ⟶ B} {F G H : X.Modules}
    {u : F ⟶ G} {v : G ⟶ H}
    {E : SpaceSquareZeroExtension f F} {D : SpaceSquareZeroExtension f G}
    {L : SpaceSquareZeroExtension f H}
    (a : SpaceExtensionMap u E D) (b : SpaceExtensionMap v D L) :
    SpaceExtensionMap (u ≫ v) E L :=
  ⟨a.val ≫ b.val, by
    refine ⟨?_, ?_, ?_⟩
    · rw [Category.assoc, b.property.1, a.property.1]
    · intro U m
      change b.val.app (op U) (a.val.app (op U) _) = _
      rw [a.property.2.1, b.property.2.1]
      rfl
    · intro U V c hc
      change E.base.app U V c hc ≫ (a.val.app (op U) ≫ b.val.app (op U)) = _
      rw [← Category.assoc, a.property.2.2, b.property.2.2]⟩

/-- The category of extensions with fixed kernel, with actual algebra maps.
Source: Stacks, Tag 0D3Q (blueprint: def-sfb-space-fixed-ideal-extensions). -/
@[reducible] instance spaceSquareZeroExtensionCategory (f : X ⟶ B) (F : X.Modules) :
    Category (SpaceSquareZeroExtension f F) where
  Hom E D := SpaceExtensionMap (𝟙 F) E D
  id E := SpaceExtensionMap.id E
  comp a b := ⟨a.val ≫ b.val, by
    have h := (SpaceExtensionMap.comp a b).property
    simpa only [SpaceExtensionMap.comp, Category.id_comp] using h⟩
  id_comp a := Subtype.ext (Category.id_comp a.val)
  comp_id a := Subtype.ext (Category.comp_id a.val)
  assoc a b c := Subtype.ext (Category.assoc a.val b.val c.val)

/-- The fixed-base-ideal condition on an extension. On a compatible pair of charts,
its base action sends j to the inclusion of c(1 ⊗ j). The quantified chart map
`a` is precisely the composite with the normalized reduction arrow.
Source: Stacks, Tag 0D3Q (blueprint: def-sfb-space-fixed-ideal-extensions). -/
def HasBaseIdealMap {i : B ⟶ B'} (T : ThickeningSiteModel i)
    (J : SquareZeroIdeal T) (f : X ⟶ B) {F : X.Modules}
    (c : (moduleTensorPullback f).obj J.obj ⟶ F)
    (E : SpaceSquareZeroExtension (f ≫ i) F) : Prop :=
  ∀ (V : B.EtaleSite) (q : ModuleChart f V)
    (a : q.left.obj.left ⟶ (T.equivalence.inverse.obj V).obj.left)
    (ha : q.left.obj.hom ≫ (f ≫ i).hom.hom =
      yoneda.map a ≫ (T.equivalence.inverse.obj V).obj.hom),
    a = q.hom.left ≫ T.reduction.app V →
    ∀ j : J.obj.val.obj (op V),
      E.base.app q.left (T.equivalence.inverse.obj V) a ha (J.inclusion V j) =
        E.inclusion q.left (c.val.app (op q.left) (moduleTensorSection f J.obj V q 1 j))

/-- The full category of extensions inducing the specified base-ideal map.
Source: Stacks, Tag 0D3Q (blueprint: def-sfb-space-fixed-ideal-extensions). -/
abbrev FixedIdealExtensions {i : B ⟶ B'} (T : ThickeningSiteModel i)
    (J : SquareZeroIdeal T) (f : X ⟶ B) {F : X.Modules}
    (c : (moduleTensorPullback f).obj J.obj ⟶ F) :=
  ObjectProperty.FullSubcategory (HasBaseIdealMap T J f c)

/-- A functor is kernel pushout when its natural arrows are universal for maps to
extensions with every target kernel. This determines it up to unique natural
isomorphism preserving the arrows, rather than selecting an arbitrary functor.
Source: Stacks, Tag 0D3Q (blueprint: def-sfb-space-fixed-ideal-extensions). -/
structure IsKernelPushout {i : B ⟶ B'} {T : ThickeningSiteModel i}
    {J : SquareZeroIdeal T} {f : X ⟶ B} {F G : X.Modules}
    {c : (moduleTensorPullback f).obj J.obj ⟶ F} (u : F ⟶ G)
    (P : FixedIdealExtensions T J f c ⥤ FixedIdealExtensions T J f (c ≫ u)) where
  arrow (E : FixedIdealExtensions T J f c) : SpaceExtensionMap u E.obj (P.obj E).obj
  naturality {E D : FixedIdealExtensions T J f c} (a : E ⟶ D) :
    a.hom.val ≫ (arrow D).val = (arrow E).val ≫ (P.map a).hom.val
  universal (E : FixedIdealExtensions T J f c) (H : X.Modules)
    (L : SpaceSquareZeroExtension (f ≫ i) H) (v : G ⟶ H)
    (a : SpaceExtensionMap (u ≫ v) E.obj L) :
    ∃! b : SpaceExtensionMap v (P.obj E).obj L, (arrow E).val ≫ b.val = a.val

end AlgebraicGeometry.AlgebraicSpace
