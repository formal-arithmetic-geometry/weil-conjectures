/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal properties of categories of sheaves

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

Moreover, let `F : C ⥤ D` be a functor which is continuous with respect to Grothendieck
topologies `J` on `C` and `K` on `D`, and let `A` be a monoidal category such that the
monoidal category structures on `Sheaf J A` and `Sheaf K A` obtained by localization
(`CategoryTheory.Sheaf.monoidalCategory`) are available.

We show:

- `CategoryTheory.sheafToPresheafLaxMonoidal`: the inclusion `sheafToPresheaf J A` of
  sheaves into presheaves is lax monoidal, being the right adjoint of the monoidal
  sheafification functor `presheafToSheaf J A`.
- `CategoryTheory.Functor.sheafPushforwardContinuousLaxMonoidal`: the pushforward functor
  `F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` is lax monoidal.

For the latter, observe that the pushforward is isomorphic to the composite
`sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ presheafToSheaf J A`
(`CategoryTheory.Functor.sheafPushforwardContinuousIsoCompPresheafToSheaf`): composing with
`presheafToSheaf J A` loses nothing because the underlying presheaf of the pushforward of a
sheaf is already a sheaf. In this composite, the middle precomposition functor is monoidal
for the pointwise monoidal structures on the presheaf categories, and the two outer functors
are lax monoidal, so the lax monoidal structure is obtained by transport along the
isomorphism.

When `A` is moreover braided and the sheaf categories carry the braided structure
`Sheaf.braidedCategory`, these lax monoidal structures preserve the braidings:

- `CategoryTheory.sheafToPresheafLaxBraided`: the inclusion of sheaves into presheaves is
  lax braided, being the right adjoint of the braided sheafification functor.
- `CategoryTheory.Functor.sheafPushforwardContinuousLaxBraided`: the pushforward functor
  is lax braided, by transporting the lax braided structure of the composite above along
  the same isomorphism.

Since a symmetric monoidal functor is by definition a braided functor between symmetric
monoidal categories, this also covers the symmetric case.

The dual statements for the pullback functor `F.sheafPullback A J K` (an oplax monoidal
structure, which is strong under suitable hypotheses) are the subject of future work.

Finally, the constant sheaf functor `constantSheaf J A : A ⥤ Sheaf J A` is monoidal: it
is the composition of the constant presheaf functor (monoidal for the pointwise monoidal
structure on presheaves, see `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory`)
with the sheafification functor `presheafToSheaf J A` (monoidal by the monoidal
localization theory, see `Mathlib.CategoryTheory.Sites.Monoidal`).
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

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

namespace CategoryTheory

open MonoidalCategory GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A]

attribute [local instance] Sheaf.monoidalCategory

section

variable [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

/-- The inclusion of sheaves into presheaves is lax monoidal with respect to the
monoidal category structure on sheaves obtained by localization, as the right adjoint
of the monoidal functor `presheafToSheaf J A`. -/
noncomputable instance sheafToPresheafLaxMonoidal :
    (sheafToPresheaf J A).LaxMonoidal :=
  (sheafificationAdjunction J A).rightAdjointLaxMonoidal

end

namespace Functor

variable [F.IsContinuous J K]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

/-- The pushforward of sheaves along a continuous functor is isomorphic to the composite
of the inclusion into presheaves, the precomposition with `F.op` and the sheafification:
since the underlying presheaf of the pushforward of a sheaf is a sheaf, the final
sheafification loses nothing. -/
noncomputable def sheafPushforwardContinuousIsoCompPresheafToSheaf :
    (sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op) ⋙ presheafToSheaf J A ≅
      F.sheafPushforwardContinuous A J K :=
  isoWhiskerRight (F.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
      (presheafToSheaf J A) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (asIso (sheafificationAdjunction J A).counit) ≪≫
    Functor.rightUnitor _

/-- The pushforward of sheaves along a continuous functor is lax monoidal with respect
to the monoidal category structures on sheaves obtained by localization. -/
noncomputable instance sheafPushforwardContinuousLaxMonoidal :
    (F.sheafPushforwardContinuous A J K).LaxMonoidal :=
  Functor.LaxMonoidal.transport
    (F.sheafPushforwardContinuousIsoCompPresheafToSheaf J K A)

end Functor

section

variable [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

noncomputable instance : (constantSheaf J A).Monoidal :=
  inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).Monoidal

end

section BraidedCategory

variable [BraidedCategory A]

attribute [local instance] Sheaf.braidedCategory

section

variable [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

/-- The inclusion of sheaves into presheaves is lax braided with respect to the braided
category structure on sheaves obtained by localization, as the right adjoint of the
braided functor `presheafToSheaf J A`. -/
noncomputable instance sheafToPresheafLaxBraided :
    (sheafToPresheaf J A).LaxBraided :=
  (sheafificationAdjunction J A).rightAdjointLaxBraided

end

namespace Functor

variable [F.IsContinuous J K]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

/-- The pushforward of sheaves along a continuous functor is lax braided with respect to
the braided category structures on sheaves obtained by localization: its lax monoidal
structure is transported along an isomorphism from a composite of three lax braided
functors. Since a symmetric monoidal functor is by definition a braided functor between
symmetric monoidal categories, this also covers the symmetric case. -/
noncomputable instance sheafPushforwardContinuousLaxBraided :
    (F.sheafPushforwardContinuous A J K).LaxBraided :=
  letI := Functor.LaxMonoidal.transport_isMonoidal_hom
    (F.sheafPushforwardContinuousIsoCompPresheafToSheaf J K A)
  Functor.LaxBraided.ofNatIso (F.sheafPushforwardContinuousIsoCompPresheafToSheaf J K A)

end Functor

end BraidedCategory

end CategoryTheory
