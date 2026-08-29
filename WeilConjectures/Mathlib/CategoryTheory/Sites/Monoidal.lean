/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# The pushforward of sheaves is lax braided

Let `A` be a braided monoidal category and let `J` be a Grothendieck topology such that the
category of sheaves `Sheaf J A` carries the monoidal structure obtained by localizing the
pointwise monoidal structure on presheaves (`CategoryTheory.Sheaf.monoidalCategory`). The
sheafification functor `presheafToSheaf J A` is braided, hence its right adjoint
`sheafToPresheaf J A` is lax braided.

If `F : C ⥤ D` is a continuous functor of sites, the pushforward
`F.sheafPushforwardContinuous A J K : Sheaf K A ⥤ Sheaf J A` is obtained by sheafifying the
restriction along `F.op` of the underlying presheaf. As restriction is a braided functor
between the (pointwise monoidal) categories of presheaves, the pushforward is lax braided.
When `A` is symmetric this says that `F.sheafPushforwardContinuous A J K` is lax symmetric
monoidal.

## Main definitions

- `CategoryTheory.sheafToPresheafLaxBraided`: the underlying presheaf functor is lax braided.
- `CategoryTheory.Functor.sheafPushforwardContinuousLaxBraided`: the pushforward of sheaves
  along a continuous functor of sites is lax braided.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A] [BraidedCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The functor sending a sheaf to its underlying presheaf is lax monoidal, being the right
adjoint of the (strong) monoidal sheafification functor. -/
noncomputable instance sheafToPresheafLaxMonoidal : (sheafToPresheaf J A).LaxMonoidal :=
  (sheafificationAdjunction J A).rightAdjointLaxMonoidal

/-- The functor sending a sheaf to its underlying presheaf is lax braided, being the right
adjoint of the braided sheafification functor. -/
noncomputable instance sheafToPresheafLaxBraided : (sheafToPresheaf J A).LaxBraided :=
  (sheafificationAdjunction J A).rightAdjointLaxBraided

namespace Functor

variable [F.IsContinuous J K] [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

/-- The pushforward of sheaves along a continuous functor `F : C ⥤ D` is the sheafification of
the restriction along `F.op` of the underlying presheaf. -/
noncomputable def sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso :
    sheafToPresheaf K A ⋙ (whiskeringLeft _ _ A).obj F.op ⋙ presheafToSheaf J A ≅
      F.sheafPushforwardContinuous A J K :=
  isoWhiskerLeft (F.sheafPushforwardContinuous A J K)
      (asIso (sheafificationAdjunction J A).counit) ≪≫
    (F.sheafPushforwardContinuous A J K).rightUnitor

/-- The pushforward of sheaves along a continuous functor of sites is lax monoidal. -/
noncomputable instance sheafPushforwardContinuousLaxMonoidal :
    (F.sheafPushforwardContinuous A J K).LaxMonoidal :=
  LaxMonoidal.transport (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)

/-- The pushforward of sheaves along a continuous functor of sites is lax braided. When `A` is
symmetric, this says that the pushforward is lax symmetric monoidal. -/
noncomputable instance sheafPushforwardContinuousLaxBraided :
    (F.sheafPushforwardContinuous A J K).LaxBraided :=
  have := LaxMonoidal.natTransIsMonoidal_of_transport
    (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)
  LaxBraided.ofNatIso (sheafToPresheafCompWhiskeringLeftCompPresheafToSheafIso F A J K)

end Functor

end CategoryTheory
