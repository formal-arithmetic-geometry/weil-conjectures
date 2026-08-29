/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal structures on the pushforward and pullback of sheaves

Let `F : C ⥤ D` be a functor which is continuous with respect to Grothendieck topologies
`J` on `C` and `K` on `D`, and let `A` be a monoidal category such that the monoidal
category structures on `Sheaf J A` and `Sheaf K A` obtained by localization
(`CategoryTheory.Sheaf.monoidalCategory`) are available.

We show:

- `CategoryTheory.sheafToPresheafLaxMonoidal`: the inclusion `sheafToPresheaf J A` of
  sheaves into presheaves is lax monoidal, being the right adjoint of the monoidal
  sheafification functor `presheafToSheaf J A`.
- `CategoryTheory.Functor.sheafPushforwardContinuousLaxMonoidal`: the pushforward functor
  `F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` is lax monoidal.
- `CategoryTheory.Functor.sheafPullbackOplaxMonoidal`: the pullback functor
  `F.sheafPullback A J K : Sheaf J A ⥤ Sheaf K A` is oplax monoidal, being the left
  adjoint of the lax monoidal pushforward functor.
- `CategoryTheory.Functor.sheafAdjunctionContinuousIsMonoidal`: the adjunction
  `F.sheafAdjunctionContinuous A J K` between pullback and pushforward of sheaves is
  compatible with these (op)lax monoidal structures. This gives access to the
  compatibility lemmas of `CategoryTheory.Adjunction.IsMonoidal`, which express the
  structure morphisms of each of the two functors as mates of those of the other.

For the latter, observe that the pushforward is isomorphic to the composite
`sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ presheafToSheaf J A`
(`CategoryTheory.Functor.sheafPushforwardContinuousIsoCompPresheafToSheaf`): composing with
`presheafToSheaf J A` loses nothing because the underlying presheaf of the pushforward of a
sheaf is already a sheaf. In this composite, the middle precomposition functor is monoidal
for the pointwise monoidal structures on the presheaf categories, and the two outer functors
are lax monoidal, so the lax monoidal structure is obtained by transport along the
isomorphism.

The oplax monoidal structure on the pullback functor is obtained from the lax monoidal
structure on the pushforward by the doctrinal adjunction construction
`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`.

When `A` is moreover braided and the sheaf categories carry the braided structure
`Sheaf.braidedCategory`, all of this is compatible with the braidings:

- `CategoryTheory.sheafToPresheafLaxBraided`: the inclusion of sheaves into presheaves is
  lax braided, being the right adjoint of the braided sheafification functor.
- `CategoryTheory.Functor.sheafPushforwardContinuousLaxBraided`: the pushforward functor
  is lax braided, by transporting the lax braided structure of the composite above along
  the same isomorphism.
- `CategoryTheory.Functor.sheafPullbackBraided`: as soon as the oplax structure morphisms
  of the pullback functor are isomorphisms, the pullback functor is braided, i.e. strong
  monoidal and compatible with the braidings. This is again doctrinal adjunction: the
  braided axiom for the pullback is the transpose of the braided axiom for the
  pushforward (`CategoryTheory.Adjunction.leftAdjointBraided`).

Since a symmetric monoidal functor is by definition a braided functor between symmetric
monoidal categories, this also covers the symmetric case: for a morphism of sites between
sites with symmetric coefficients, `f_*` is lax symmetric monoidal and `f^*` is strong
symmetric monoidal as soon as its comparison morphisms are invertible.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

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

section

variable [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The pullback of sheaves along a continuous functor is oplax monoidal with respect
to the monoidal category structures on sheaves obtained by localization: it is the left
adjoint of the lax monoidal pushforward functor, so the structure morphisms are obtained
as mates by doctrinal adjunction. -/
noncomputable instance sheafPullbackOplaxMonoidal :
    (F.sheafPullback A J K).OplaxMonoidal :=
  (F.sheafAdjunctionContinuous A J K).leftAdjointOplaxMonoidal

/-- The adjunction between the pullback and the pushforward of sheaves along a
continuous functor is compatible with the oplax monoidal structure on the pullback and
the lax monoidal structure on the pushforward. In particular the compatibility lemmas
of `CategoryTheory.Adjunction.IsMonoidal` (such as
`Adjunction.unit_app_tensor_comp_map_δ` and `Adjunction.map_μ_comp_counit_app_tensor`)
apply, expressing the structure morphisms of each of the two functors as mates of those
of the other. -/
instance sheafAdjunctionContinuousIsMonoidal :
    (F.sheafAdjunctionContinuous A J K).IsMonoidal :=
  inferInstance

@[reassoc]
lemma sheafPullback_η :
    OplaxMonoidal.η (F.sheafPullback A J K) =
      ((F.sheafAdjunctionContinuous A J K).homEquiv _ _).symm
        (LaxMonoidal.ε (F.sheafPushforwardContinuous A J K)) :=
  (F.sheafAdjunctionContinuous A J K).leftAdjointOplaxMonoidal_η

@[reassoc]
lemma sheafPullback_δ (F₁ F₂ : Sheaf J A) :
    OplaxMonoidal.δ (F.sheafPullback A J K) F₁ F₂ =
      ((F.sheafAdjunctionContinuous A J K).homEquiv _ _).symm
        (((F.sheafAdjunctionContinuous A J K).unit.app F₁ ⊗ₘ
            (F.sheafAdjunctionContinuous A J K).unit.app F₂) ≫
          LaxMonoidal.μ (F.sheafPushforwardContinuous A J K) _ _) :=
  (F.sheafAdjunctionContinuous A J K).leftAdjointOplaxMonoidal_δ F₁ F₂

section

variable [IsIso (OplaxMonoidal.η (F.sheafPullback A J K))]
  [∀ F₁ F₂, IsIso (OplaxMonoidal.δ (F.sheafPullback A J K) F₁ F₂)]

/-- If the oplax monoidal structure morphisms of the pullback of sheaves along a
continuous functor are isomorphisms, the pullback is strong monoidal. -/
@[implicit_reducible]
noncomputable def sheafPullbackMonoidal : (F.sheafPullback A J K).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

end

end

end Functor

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

section

variable [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [IsIso (OplaxMonoidal.η (F.sheafPullback A J K))]
  [∀ F₁ F₂, IsIso (OplaxMonoidal.δ (F.sheafPullback A J K) F₁ F₂)]

attribute [local instance] sheafPullbackMonoidal

/-- The pullback of sheaves along a continuous functor is braided, as soon as its oplax
monoidal structure morphisms are isomorphisms: it is then a strong monoidal left adjoint
of the lax braided pushforward functor, so the braided axiom is obtained by transposing
the braided axiom of the pushforward through the adjunction. Since a symmetric monoidal
functor is by definition a braided functor between symmetric monoidal categories, this
also covers the symmetric case. -/
@[implicit_reducible]
noncomputable def sheafPullbackBraided : (F.sheafPullback A J K).Braided :=
  (F.sheafAdjunctionContinuous A J K).leftAdjointBraided

end

end Functor

end BraidedCategory

end CategoryTheory
