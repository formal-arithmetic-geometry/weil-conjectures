/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z9
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Restriction normalization under specified counit isomorphisms.

Source: blueprint det-prop-scalar-six-pullback, proof (2).
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory

/-- Restriction normalization, stated over arbitrary categories.
Source: blueprint det-prop-scalar-six-pullback, proof (2), equations (N) and q coherence.
(blueprint: def-sfb-immersion-comparison-normalized). -/
def immersionComparisonNormalized
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Lr : A ⥤ B) (Ls : C ⥤ D) (Er : B ⥤ A) (Es : D ⥤ C)
    (rr : Er ⋙ Lr ≅ 𝟭 B) (rs : Es ⋙ Ls ≅ 𝟭 D)
    (FX : A ⥤ C) (FS : B ⥤ D) (q : FX ⋙ Ls ≅ Lr ⋙ FS)
    (d : Er ⋙ FX ≅ FS ⋙ Es) : Prop :=
  ∀ M : B, Ls.map (d.hom.app M) ≫ rs.hom.app (FS.obj M) =
    q.hom.app (Er.obj M) ≫ FS.map (rr.hom.app M)

end CategoryTheory
