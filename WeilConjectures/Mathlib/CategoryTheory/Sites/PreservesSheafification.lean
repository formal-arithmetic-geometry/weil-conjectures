/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Composing with a functor which preserves sheafification

This settles the `TODO` of `Mathlib.CategoryTheory.Sites.PreservesSheafification`: when
`F : A ⥤ B` preserves sheafification and postcomposition with `F` preserves sheaves, the
functor `Sheaf.composeAndSheafify J F` (compose, then sheafify) is isomorphic to
`sheafCompose J F` (compose, no sheafification needed).

As a consequence, if `F` is moreover a left adjoint, then so is `sheafCompose J F`, since
`Sheaf.composeAndSheafify J F` is. This is how one sees that, for instance, the restriction
of scalars of sheaves of modules preserves colimits.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
  [HasWeakSheafify J A] [HasWeakSheafify J B] [J.HasSheafCompose F]
  [J.PreservesSheafification F]

/-- The canonical isomorphism `Sheaf.composeAndSheafify J F ≅ sheafCompose J F` when `F`
preserves sheafification: `composeAndSheafify` sheafifies `P ⋙ F` for a sheaf `P`, and
sheafifying commutes with `F`, so the result is the sheafification of the sheaf `P`
composed with `F`, which is `P ⋙ F` itself. -/
noncomputable def Sheaf.composeAndSheafifyIsoSheafCompose :
    Sheaf.composeAndSheafify J F ≅ sheafCompose J F :=
  isoWhiskerLeft (sheafToPresheaf J A)
      (sheafComposeNatIso J F (sheafificationAdjunction J A) (sheafificationAdjunction J B)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (asIso (sheafificationAdjunction J A).counit) (sheafCompose J F) ≪≫
    Functor.leftUnitor _

/-- If `F` preserves sheafification and is a left adjoint, then so is `sheafCompose J F`: it is
isomorphic to `Sheaf.composeAndSheafify J F`, which is a left adjoint. -/
lemma sheafCompose_isLeftAdjoint [F.IsLeftAdjoint] : (sheafCompose J F).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (Sheaf.composeAndSheafifyIsoSheafCompose J F)

end CategoryTheory
