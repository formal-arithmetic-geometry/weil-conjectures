/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # The functorial word underlying ordinary proper/open alpha

Source: the intrinsic composition of Stacks Project, Tag 0F7B, written in functor categories.
(blueprint: lem-cbc-proper-open-word-components)
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory.Functor

/-- Package the specified beta, projector and comparison maps before specialization.
Source: Stacks Project, Tag 0F7B, intrinsic ordinary construction.
(blueprint: lem-cbc-proper-open-word-components). -/
@[irreducible] def properOpenCompositeTransformation
    (A C D E T : Type*) [Category A] [Category C] [Category D]
    [Category E] [Category T]
    (I : A ⥤ T) (P : T ⥤ C) (Q : A ⥤ D) (L : D ⥤ E)
    (J : E ⥤ D) (H : D ⥤ C) (K : E ⥤ C) (R : A ⥤ E)
    (b : I ⋙ P ⟶ Q ⋙ H) (d : 𝟭 D ⟶ L ⋙ J)
    (t : J ⋙ H ⟶ K) (c : Q ⋙ L ⟶ R) : I ⋙ P ⟶ R ⋙ K :=
  b ≫ whiskerRight (whiskerLeft Q d) H ≫
    whiskerRight (associator Q L J).inv H ≫
    (associator (Q ⋙ L) J H).hom ≫
    whiskerLeft (Q ⋙ L) t ≫ whiskerRight c K

end CategoryTheory.Functor

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

end AlgebraicGeometry.ProEtale.StrictTower
