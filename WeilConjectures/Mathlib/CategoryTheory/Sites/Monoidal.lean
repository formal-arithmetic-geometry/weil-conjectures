/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

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

end CategoryTheory
