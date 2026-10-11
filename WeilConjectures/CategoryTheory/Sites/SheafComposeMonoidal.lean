/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Postcomposition of sheaves with a lax monoidal functor

For a lax monoidal functor `G : A ⥤ B` preserving sheaves, the postcomposition
`sheafCompose J G : Sheaf J A ⥤ Sheaf J B` is lax monoidal for the sheafified tensor products:
it is isomorphic to the composite of the lax monoidal inclusion of sheaves into presheaves, of
postcomposition with `G` on presheaves and of sheafification.

## Main definitions

- `CategoryTheory.sheafComposeLaxMonoidal`: the lax monoidal structure.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
  {B : Type*} [Category B] [MonoidalCategory B] [BraidedCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
  (G : A ⥤ B) [J.HasSheafCompose G]

attribute [local instance] Sheaf.monoidalCategory

/-- The postcomposition `sheafCompose J G` is the sheafification of the postcomposition of the
underlying presheaves. -/
noncomputable def sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso :
    sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj G ⋙ presheafToSheaf J B ≅
      sheafCompose J G :=
  Functor.isoWhiskerLeft (sheafCompose J G) (asIso (sheafificationAdjunction J B).counit) ≪≫
    (sheafCompose J G).rightUnitor

variable [G.LaxMonoidal]

/-- The postcomposition of sheaves with a lax monoidal functor is lax monoidal. -/
noncomputable instance sheafComposeLaxMonoidal : (sheafCompose J G).LaxMonoidal :=
  Functor.LaxMonoidal.transport (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso J G)

end CategoryTheory
