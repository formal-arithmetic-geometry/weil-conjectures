/-
Copyright (c) 2026 Wei Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Yang
-/
import Mathlib

/-!
# The lower shriek for localized (slice) sites

Let `(C, J)` be a Grothendieck site and let `f : V ⟶ U` be a morphism in `C`. Postcomposition
with `f` induces the functor `Over.map f : Over V ⥤ Over U` between the slice categories, which
is both continuous and cocontinuous for the induced slice topologies `J.over V` and `J.over U`
(these instances are provided by mathlib in `Mathlib/CategoryTheory/Sites/Over.lean`).

Composition with `(Over.map f).op` is the *restriction* (inverse image along the localization
morphism) functor

`j_f^* : Sheaf (J.over U) A ⥤ Sheaf (J.over V) A`,

which mathlib provides as `J.overMapPullback A f`; objectwise it is given by
`(j_f^* G)(T → V) = G(T → V → U)`.

In this file we construct its **left adjoint**, the *lower shriek*

`j_{f!} : Sheaf (J.over V) A ⥤ Sheaf (J.over U) A`,

explicitly as the composite

`j_{f!} = (sheafification for J.over U) ∘ (left Kan extension along (Over.map f).op) ∘ (forget)`,

reusing mathlib's `Functor.sheafPullbackConstruction.sheafPullback`, and we record the adjunction
`j_{f!} ⊣ j_f^*`.

## Direction conventions

Beware that in the site-theoretic naming scheme of mathlib the functor `j_{f!}` is a "pullback of
sheaves" along the continuous functor `Over.map f` (it points in the *same* direction as
`Over.map f`), while the restriction `j_f^*` is the "pushforward" `sheafPushforwardContinuous`
(composition with `(Over.map f).op`, pointing *backwards*). Geometrically, however, `j_{f!}` is
an extension and `j_f^*` a restriction; we therefore expose them under the neutral names
`localizationLowerShriek` and `localizationRestriction`.

At the level of the sheaf topos `E = Sh(C, J)`, writing `Ũ`, `Ṽ` for the sheafified
representables of `U`, `V`, the category `Sheaf (J.over U) A` is a site-level presentation of
the slice topos `E/Ũ`, and `j_{f!}` presents the forward composition functor
`Σ_f̃ : E/Ṽ ⟶ E/Ũ`, `(T → Ṽ) ↦ (T → Ṽ → Ũ)`, left adjoint to the base change `f̃^*`.
(The equivalence `Sheaf (J.over U) A ≌ E/Ũ` is not yet available in mathlib; nothing in this
file depends on it.)

## Main definitions

- `CategoryTheory.localizationLowerShriekPresheaf`: the presheaf-level lower shriek, i.e. the
  left Kan extension functor along `(Over.map f).op`.
- `CategoryTheory.localizationLowerShriekPresheafAdjunction`: the presheaf-level adjunction
  `Lan ⊣ (- ∘ (Over.map f).op)`.
- `CategoryTheory.GrothendieckTopology.localizationRestriction`: the restriction functor
  `j_f^*`, definitionally `J.overMapPullback A f`.
- `CategoryTheory.GrothendieckTopology.localizationLowerShriek`: the sheaf-level lower shriek
  `j_{f!}`, i.e. left Kan extension followed by sheafification.
- `CategoryTheory.GrothendieckTopology.localizationLowerShriekAdjunction`: the adjunction
  `j_{f!} ⊣ j_f^*`.
- `CategoryTheory.GrothendieckTopology.localizationLowerShriekIsoSheafPullback`: comparison
  with the abstract (chosen) left adjoint `(Over.map f).sheafPullback A _ _` from mathlib.

The open (mono) case — full faithfulness, the unit isomorphism `𝟭 ≅ j_f^* ∘ j_{f!}` and the
extension-by-zero formulas — is treated in
`WeilConjectures.CategoryTheory.Sites.LocalizationLowerShriekOpen`.

## References

- [SGA 4, III.5, IV.5.1-5.4 and IV.11.3.1] for localization of sites and topoi.
- https://stacks.math.columbia.edu/tag/03CD (localization of sites),
  https://stacks.math.columbia.edu/tag/03EZ.
-/

universe v' v u' u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory

variable (A : Type u') [Category.{v'} A]

section Presheaf

variable {C : Type u} [Category.{v} C] {V U : C} (f : V ⟶ U)
variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasLeftKanExtension P]

/-- The presheaf-level lower shriek along a morphism `f : V ⟶ U`: the left Kan extension
functor along `(Over.map f).op : (Over V)ᵒᵖ ⥤ (Over U)ᵒᵖ`. This is the functor denoted
`j_{f,!}^{pre}` in the literature on localization of sites.

The existence hypothesis `[∀ P, (Over.map f).op.HasLeftKanExtension P]` is satisfied e.g. as
soon as `A` has colimits of the relevant size, see the `example`s at the end of this file. -/
noncomputable def localizationLowerShriekPresheaf :
    ((Over V)ᵒᵖ ⥤ A) ⥤ ((Over U)ᵒᵖ ⥤ A) :=
  (Over.map f).op.lan

/-- The presheaf-level adjunction `j_{f,!}^{pre} ⊣ (- ∘ (Over.map f).op)`: the left Kan
extension along `(Over.map f).op` is left adjoint to the restriction of presheaves given by
precomposition with `(Over.map f).op`. -/
noncomputable def localizationLowerShriekPresheafAdjunction :
    localizationLowerShriekPresheaf A f ⊣
      (Functor.whiskeringLeft (Over V)ᵒᵖ (Over U)ᵒᵖ A).obj (Over.map f).op :=
  (Over.map f).op.lanAdjunction A

end Presheaf

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {V U : C} (f : V ⟶ U)

/-- The restriction (inverse image) functor `j_f^* : Sheaf (J.over U) A ⥤ Sheaf (J.over V) A`
along the localization morphism induced by `f : V ⟶ U`. It is given by composition with
`(Over.map f).op`, i.e. objectwise by `(j_f^* G)(T → V) = G(T → V → U)`; see
`localizationRestriction_obj_val_obj`.

This is definitionally mathlib's `J.overMapPullback A f`; we expose it under a geometrically
neutral name to avoid confusion with the lower shriek, which in mathlib's site-theoretic
terminology is a "sheaf pullback" along the continuous functor `Over.map f`. -/
abbrev localizationRestriction : Sheaf (J.over U) A ⥤ Sheaf (J.over V) A :=
  J.overMapPullback A f

/-- Objectwise description of the restriction functor: the sections of `j_f^* G` over
`(T → V) : Over V` are the sections of `G` over the composite `(T → V → U) : Over U`. -/
@[simp]
lemma localizationRestriction_obj_val_obj (G : Sheaf (J.over U) A) (b : Over V) :
    ((J.localizationRestriction A f).obj G).obj.obj (op b) =
      G.obj.obj (op ((Over.map f).obj b)) :=
  rfl

/-- The morphism action of the restriction functor is (the whiskering of) the original
morphism action. -/
@[simp]
lemma localizationRestriction_map_hom_app {G G' : Sheaf (J.over U) A} (φ : G ⟶ G')
    (b : Over V) :
    (((J.localizationRestriction A f).map φ).hom).app (op b) =
      φ.hom.app (op ((Over.map f).obj b)) :=
  rfl

variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasLeftKanExtension P]
variable [HasWeakSheafify (J.over U) A]

/-- The lower shriek `j_{f!} : Sheaf (J.over V) A ⥤ Sheaf (J.over U) A` along the localization
morphism induced by `f : V ⟶ U`, constructed explicitly as

`(forget to presheaves) ⋙ (left Kan extension along (Over.map f).op) ⋙ (sheafification)`.

It is left adjoint to the restriction `j_f^* = J.localizationRestriction A f`, see
`localizationLowerShriekAdjunction`; the underlying composite is mathlib's
`Functor.sheafPullbackConstruction.sheafPullback` for the continuous functor `Over.map f`
(a "pullback of sheaves" in site-theoretic terminology, an extension functor geometrically).

For a *monomorphism* `f` this is the "extension by zero" functor; see
`WeilConjectures.CategoryTheory.Sites.LocalizationLowerShriekOpen`. -/
noncomputable def localizationLowerShriek : Sheaf (J.over V) A ⥤ Sheaf (J.over U) A :=
  Functor.sheafPullbackConstruction.sheafPullback (Over.map f) A (J.over V) (J.over U)

/-- The lower shriek is, by definition, the left Kan extension on presheaves followed by
sheafification. -/
lemma localizationLowerShriek_eq :
    J.localizationLowerShriek A f =
      sheafToPresheaf (J.over V) A ⋙ localizationLowerShriekPresheaf A f ⋙
        presheafToSheaf (J.over U) A :=
  rfl

/-- The adjunction `j_{f!} ⊣ j_f^*` between the lower shriek and the restriction functor of
sheaves on localized sites: for `F : Sheaf (J.over V) A` and `G : Sheaf (J.over U) A` it
provides the natural hom-set equivalence

`Hom (j_{f!} F) G ≃ Hom F (j_f^* G)`.

The unit and counit are available as `(J.localizationLowerShriekAdjunction A f).unit` and
`(J.localizationLowerShriekAdjunction A f).counit`; the triangle identities are mathlib's
simp lemmas `Adjunction.left_triangle_components` and `Adjunction.right_triangle_components`. -/
noncomputable def localizationLowerShriekAdjunction :
    J.localizationLowerShriek A f ⊣ J.localizationRestriction A f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.map f) A
    (J.over V) (J.over U)

/-- The unit `𝟭 ⟶ j_{f!} ⋙ j_f^*` of the lower shriek adjunction. -/
noncomputable abbrev localizationLowerShriekUnit :
    𝟭 (Sheaf (J.over V) A) ⟶
      J.localizationLowerShriek A f ⋙ J.localizationRestriction A f :=
  (J.localizationLowerShriekAdjunction A f).unit

/-- The counit `j_f^* ⋙ j_{f!} ⟶ 𝟭` of the lower shriek adjunction. -/
noncomputable abbrev localizationLowerShriekCounit :
    J.localizationRestriction A f ⋙ J.localizationLowerShriek A f ⟶
      𝟭 (Sheaf (J.over U) A) :=
  (J.localizationLowerShriekAdjunction A f).counit

instance : (J.localizationLowerShriek A f).IsLeftAdjoint :=
  (J.localizationLowerShriekAdjunction A f).isLeftAdjoint

instance : (J.localizationRestriction A f).IsRightAdjoint :=
  (J.localizationLowerShriekAdjunction A f).isRightAdjoint

/-- The explicitly constructed lower shriek is isomorphic to the abstract chosen left adjoint
`(Over.map f).sheafPullback A (J.over V) (J.over U)` of the restriction functor provided by
mathlib. -/
noncomputable def localizationLowerShriekIsoSheafPullback :
    (Over.map f).sheafPullback A (J.over V) (J.over U) ≅ J.localizationLowerShriek A f :=
  Functor.sheafPullbackConstruction.sheafPullbackIso (Over.map f) A (J.over V) (J.over U)

section

variable {A J f}

/-- The hom-set equivalence of the lower shriek adjunction, stated explicitly:
`Hom (j_{f!} F) G ≃ Hom F (j_f^* G)`. -/
noncomputable abbrev localizationLowerShriekHomEquiv (F : Sheaf (J.over V) A)
    (G : Sheaf (J.over U) A) :
    ((J.localizationLowerShriek A f).obj F ⟶ G) ≃
      (F ⟶ (J.localizationRestriction A f).obj G) :=
  (J.localizationLowerShriekAdjunction A f).homEquiv F G

end

end GrothendieckTopology

section Examples

/- The existence hypotheses for the lower shriek are satisfied whenever the coefficient
category has colimits of the appropriate size (e.g. `A = Type (max u v)`, any Grothendieck
abelian category, `ModuleCat R`, ...), together with (weak) sheafification for the slice
topology. -/

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type u') [Category.{v'} A]
variable {V U : C} (f : V ⟶ U)

set_option synthInstance.maxHeartbeats 80000 in
example [HasColimitsOfSize.{v, max u v} A] (P : (Over V)ᵒᵖ ⥤ A) :
    (Over.map f).op.HasPointwiseLeftKanExtension P :=
  inferInstance

set_option synthInstance.maxHeartbeats 80000 in
noncomputable example [HasColimitsOfSize.{v, max u v} A] [HasWeakSheafify (J.over U) A] :
    Sheaf (J.over V) A ⥤ Sheaf (J.over U) A :=
  J.localizationLowerShriek A f

end Examples

end CategoryTheory
