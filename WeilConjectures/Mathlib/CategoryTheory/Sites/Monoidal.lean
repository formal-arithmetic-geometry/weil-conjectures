/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Lax monoidal structure on the pushforward of sheaves

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

For the latter, observe that the pushforward is isomorphic to the composite
`sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ presheafToSheaf J A`
(`CategoryTheory.Functor.sheafPushforwardContinuousIsoCompPresheafToSheaf`): composing with
`presheafToSheaf J A` loses nothing because the underlying presheaf of the pushforward of a
sheaf is already a sheaf. In this composite, the middle precomposition functor is monoidal
for the pointwise monoidal structures on the presheaf categories, and the two outer functors
are lax monoidal, so the lax monoidal structure is obtained by transport along the
isomorphism.

The dual statements for the pullback functor `F.sheafPullback A J K` (an oplax monoidal
structure, which is strong under suitable hypotheses) are the subject of future work.

Moreover, when `F` exhibits `(C, J)` as a dense subsite of `(D, K)` and `A` is a
concrete category for which `J.W` and `K.W` agree with the classes of locally bijective
morphisms of presheaves, we upgrade the lax monoidal structure on the restriction
functor `F.sheafPushforwardContinuous A J K` to a strong monoidal one
(`CategoryTheory.Functor.IsDenseSubsite.sheafPushforwardContinuousMonoidal`) and record
two transport results: monoidality of `W` ascends from the dense subsite to the big site
(`CategoryTheory.Functor.IsDenseSubsite.isMonoidal_W`), and monoidal closedness
transports across the restriction functor whenever it is an equivalence
(`CategoryTheory.Functor.IsDenseSubsite.monoidalClosed`).

Finally, if `A` is a closed symmetric monoidal category with suitable limits, Day's
reflection theorem (`Monoidal.Reflective.monoidalClosed`) applied to the reflective
adjunction `sheafificationAdjunction J A` shows that the localized monoidal structure
on `Sheaf J A` is closed (`CategoryTheory.Sheaf.monoidalClosed`). Like
`Sheaf.monoidalCategory` itself, this is not made a global instance.

Moreover, the constant sheaf functor `constantSheaf J A : A ⥤ Sheaf J A` is monoidal:
it is the composition of the constant presheaf functor (monoidal for the pointwise
monoidal structure on presheaves, see
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory`) with the
sheafification functor `presheafToSheaf J A` (monoidal by the monoidal localization
theory, see `Mathlib.CategoryTheory.Sites.Monoidal`). When `A` is moreover braided and
`Sheaf J A` carries the braided structure `Sheaf.braidedCategory`, the constant sheaf
functor is braided, by the same composition. Since a symmetric monoidal functor is by
definition a braided functor between symmetric monoidal categories, this also covers the
symmetric case.

This file imports both `Mathlib.CategoryTheory.Sites.ConstantSheaf` and
`Mathlib.CategoryTheory.Sites.Monoidal` since neither imports the other.
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

end Functor

section

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

/-- The unit of the lax monoidal structure on `sheafToPresheaf J A` becomes an
isomorphism after sheafification. -/
lemma GrothendieckTopology.W_ε_sheafToPresheaf : J.W (ε (sheafToPresheaf J A)) := by
  rw [J.W_iff]
  exact IsIso.of_isIso_fac_right
    ((sheafificationAdjunction J A).map_ε_comp_counit_app_unit)

/-- The tensorator of the lax monoidal structure on `sheafToPresheaf J A` becomes an
isomorphism after sheafification. -/
lemma GrothendieckTopology.W_μ_sheafToPresheaf (F₁ F₂ : Sheaf J A) :
    J.W (μ (sheafToPresheaf J A) F₁ F₂) := by
  rw [J.W_iff]
  exact IsIso.of_isIso_fac_right
    ((sheafificationAdjunction J A).map_μ_comp_counit_app_tensor F₁ F₂)

end

namespace Functor.IsDenseSubsite

open Functor.LaxMonoidal Functor.OplaxMonoidal

universe w'

variable {FA : A → A → Type*} {CA : A → Type w'}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]
variable [hFd : F.IsDenseSubsite J K]
variable [hJW : J.WEqualsLocallyBijective A] [hKW : K.WEqualsLocallyBijective A]

include F hFd hJW hKW in
/-- If `F` exhibits `(C, J)` as a dense subsite of `(D, K)` and the class `J.W` of
morphisms of presheaves on `C` inverted by sheafification is monoidal, then so is
the corresponding class `K.W` on `D`. -/
lemma isMonoidal_W [(J.W (A := A)).IsMonoidal] : (K.W (A := A)).IsMonoidal := by
  rw [← GrothendieckTopology.W_inverseImage_whiskeringLeft_of_isDenseSubsite F J K A]
  infer_instance

variable [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

instance : IsIso (ε (F.sheafPushforwardContinuous A J K)) := by
  have e : ε (F.sheafPushforwardContinuous A J K) =
      ε ((sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op) ⋙ presheafToSheaf J A) ≫
        (F.sheafPushforwardContinuousIsoCompPresheafToSheaf J K A).hom.app (𝟙_ (Sheaf K A)) :=
    rfl
  rw [e, Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.comp_ε, Functor.map_comp]
  haveI : IsIso ((presheafToSheaf J A).map
      (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op).map (ε (sheafToPresheaf K A)))) :=
    (J.W_iff _).1 ((GrothendieckTopology.W_whiskerLeft_iff_of_isDenseSubsite F J K _).2
      (K.W_ε_sheafToPresheaf A))
  infer_instance

instance (F₁ F₂ : Sheaf K A) : IsIso (μ (F.sheafPushforwardContinuous A J K) F₁ F₂) := by
  have e : μ (F.sheafPushforwardContinuous A J K) F₁ F₂ =
      ((F.sheafPushforwardContinuousIsoCompPresheafToSheaf J K A).inv.app F₁ ⊗ₘ
        (F.sheafPushforwardContinuousIsoCompPresheafToSheaf J K A).inv.app F₂) ≫
      μ ((sheafToPresheaf K A ⋙ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op) ⋙ presheafToSheaf J A)
        F₁ F₂ ≫
      (F.sheafPushforwardContinuousIsoCompPresheafToSheaf J K A).hom.app (F₁ ⊗ F₂) :=
    rfl
  rw [e, Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ, Functor.map_comp]
  haveI : IsIso ((presheafToSheaf J A).map
      (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op).map (μ (sheafToPresheaf K A) F₁ F₂))) :=
    (J.W_iff _).1 ((GrothendieckTopology.W_whiskerLeft_iff_of_isDenseSubsite F J K _).2
      (K.W_μ_sheafToPresheaf A F₁ F₂))
  infer_instance

/-- The restriction functor to a dense subsite is strong monoidal with respect to the
monoidal category structures on sheaves obtained by localization: the unit and the
tensorator of its lax monoidal structure
(`CategoryTheory.Functor.sheafPushforwardContinuousLaxMonoidal`) are isomorphisms.

This is not made a global instance in order not to compete with the lax monoidal
structure it refines; its underlying lax monoidal structure is definitionally the
existing instance. -/
@[implicit_reducible]
noncomputable def sheafPushforwardContinuousMonoidal :
    (F.sheafPushforwardContinuous A J K).Monoidal :=
  Functor.Monoidal.ofLaxMonoidal _

example : (sheafPushforwardContinuousMonoidal F J K A).toLaxMonoidal =
    F.sheafPushforwardContinuousLaxMonoidal J K A :=
  rfl

/-- Monoidal closedness transports along the restriction to a dense subsite whenever
the restriction functor is an equivalence (which holds for instance for
one-hypercover-dense functors, see
`CategoryTheory.Functor.isEquivalence_of_isOneHypercoverDense`). -/
@[implicit_reducible]
noncomputable def monoidalClosed [(F.sheafPushforwardContinuous A J K).IsEquivalence]
    [MonoidalClosed (Sheaf J A)] : MonoidalClosed (Sheaf K A) :=
  letI := sheafPushforwardContinuousMonoidal F J K A
  MonoidalClosed.ofEquiv (F.sheafPushforwardContinuous A J K)
    (F.sheafPushforwardContinuous A J K).asEquivalence.toAdjunction

end Functor.IsDenseSubsite

namespace Sheaf

open Enriched.FunctorCategory MonoidalClosed MonoidalClosed.FunctorCategory

variable [SymmetricCategory A] [MonoidalClosed A] [HasWeakSheafify J A]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is closed, by Day's reflection theorem applied to the reflective adjunction
`sheafificationAdjunction J A`. -/
@[implicit_reducible]
noncomputable def monoidalClosed : MonoidalClosed (Sheaf J A) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J A)

end Sheaf

section ConstantSheaf

variable [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

noncomputable instance : (constantSheaf J A).Monoidal :=
  inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).Monoidal

section BraidedCategory

variable [BraidedCategory A]

attribute [local instance] Sheaf.braidedCategory

noncomputable instance : (constantSheaf J A).Braided :=
  inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).Braided

end BraidedCategory

end ConstantSheaf

end CategoryTheory
