/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The monoidal category structure on sheaves is closed

If `A` is a closed symmetric monoidal category with suitable limits and `J` is a
Grothendieck topology with `HasWeakSheafify J A`, the category of presheaves `Cᵒᵖ ⥤ A`
is closed symmetric monoidal, sheafification `presheafToSheaf J A` is monoidal for the
localized monoidal structure `Sheaf.monoidalCategory`, and `sheafToPresheaf J A` is fully
faithful. Day's reflection theorem (`Monoidal.Reflective.monoidalClosed`) then shows that
the localized monoidal structure on `Sheaf J A` is closed.

Moreover, the internal hom of sheaves can be computed so that its underlying presheaf
is the internal hom (enriched hom) in the category of presheaves: the enriched hom
`functorEnrichedHom A F.obj G.obj` of the underlying presheaves is a sheaf whenever `G`
is (`Presheaf.isSheaf_functorEnrichedHom`), and the resulting sheaf is isomorphic to the
abstract internal hom `(ihom F).obj G` given by Day's reflection theorem.

## Main definitions

- `CategoryTheory.Sheaf.monoidalClosed`: the monoidal category structure on `Sheaf J A`
  obtained in `Sheaf.monoidalCategory` is closed.
- `CategoryTheory.Sheaf.internalHom`: the sheaf of internal homs from `F` to `G`, whose
  underlying presheaf is the internal hom of the underlying presheaves.
- `CategoryTheory.Sheaf.ihomIsoInternalHomFunctor`: the internal hom functor `ihom F`
  given by the closed structure `Sheaf.monoidalClosed` is isomorphic to the functor
  `G ↦ Sheaf.internalHom F G`.

Like `Sheaf.monoidalCategory` itself, `Sheaf.monoidalClosed` is not made a global instance.
-/

@[expose] public section

universe v₁ v₃ u₁ u₃

namespace CategoryTheory.Sheaf

open Enriched.FunctorCategory MonoidalClosed MonoidalClosed.FunctorCategory

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A] [SymmetricCategory A]
  [MonoidalClosed A] [HasWeakSheafify J A]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

attribute [local instance] monoidalCategory

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is closed, by Day's reflection theorem applied to the reflective adjunction
`sheafificationAdjunction J A`. -/
@[implicit_reducible]
noncomputable def monoidalClosed : MonoidalClosed (Sheaf J A) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J A)

attribute [local instance] monoidalClosed

variable {J A}

/-- The internal hom of sheaves `F` and `G`: the sheaf whose underlying presheaf is the
internal hom (enriched hom) `functorEnrichedHom A F.obj G.obj` of the underlying
presheaves, which is a sheaf because `G` is. It is isomorphic to the abstract internal
hom `(ihom F).obj G` given by the closed structure `Sheaf.monoidalClosed`, see
`Sheaf.ihomObjIsoInternalHom`. -/
noncomputable def internalHom (F G : Sheaf J A) : Sheaf J A :=
  ⟨functorEnrichedHom A F.obj G.obj, Presheaf.isSheaf_functorEnrichedHom _ _ G.property⟩

omit [SymmetricCategory A] [HasWeakSheafify J A] [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂] in
/-- The underlying presheaf of `Sheaf.internalHom F G` is the internal hom (enriched hom)
of the underlying presheaves. -/
@[simp]
lemma internalHom_obj (F G : Sheaf J A) :
    (internalHom F G).obj = functorEnrichedHom A F.obj G.obj :=
  rfl

/-- The internal hom of sheaves `Sheaf.internalHom F G`, as a functor in `G`. -/
noncomputable def internalHomFunctor (F : Sheaf J A) : Sheaf J A ⥤ Sheaf J A where
  obj G := internalHom F G
  map g := ObjectProperty.homMk ((ihom F.obj).map g.hom)
  map_id G := ObjectProperty.hom_ext _ ((ihom F.obj).map_id G.obj)
  map_comp f g := ObjectProperty.hom_ext _ ((ihom F.obj).map_comp f.hom g.hom)

omit [SymmetricCategory A] [HasWeakSheafify J A] in
@[simp]
lemma internalHomFunctor_obj (F G : Sheaf J A) :
    (internalHomFunctor F).obj G = internalHom F G :=
  rfl

omit [SymmetricCategory A] [HasWeakSheafify J A] in
@[simp]
lemma internalHomFunctor_map_hom (F : Sheaf J A) {G₁ G₂ : Sheaf J A} (g : G₁ ⟶ G₂) :
    ((internalHomFunctor F).map g).hom = (ihom F.obj).map g.hom :=
  rfl

/-- The internal hom functor `ihom F` on sheaves given by the closed structure
`Sheaf.monoidalClosed` is isomorphic to `Sheaf.internalHomFunctor F`, whose values have
as underlying presheaves the internal homs of the underlying presheaves. The isomorphism
at `G` is the counit of the sheafification adjunction at `Sheaf.internalHom F G`. -/
noncomputable def ihomIsoInternalHomFunctor (F : Sheaf J A) :
    ihom F ≅ internalHomFunctor F :=
  NatIso.ofComponents
    (fun G ↦ asIso ((sheafificationAdjunction J A).counit.app (internalHom F G)))
    (fun g ↦ (sheafificationAdjunction J A).counit.naturality ((internalHomFunctor F).map g))

/-- The abstract internal hom `(ihom F).obj G` of sheaves given by the closed structure
`Sheaf.monoidalClosed` is isomorphic to `Sheaf.internalHom F G`, whose underlying
presheaf is the internal hom of the underlying presheaves. -/
noncomputable def ihomObjIsoInternalHom (F G : Sheaf J A) :
    (ihom F).obj G ≅ internalHom F G :=
  (ihomIsoInternalHomFunctor F).app G

end CategoryTheory.Sheaf
