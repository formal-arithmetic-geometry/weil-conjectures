/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z9
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Composition coherence for specified inverse-image comparisons.

Source: blueprint det-prop-scalar-six-pullback, proof (2).
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory

/-- Composition coherence, stated over arbitrary categories.
Source: blueprint det-prop-scalar-six-pullback, proof (2), equations (N) and q coherence.
(blueprint: def-sfb-immersion-comparison-composition). -/
def immersionComparisonComposition
    {Xr Sr Tr Xs Ss Ts : Type*}
    [Category Xr] [Category Sr] [Category Tr] [Category Xs] [Category Ss] [Category Ts]
    (Lar : Xr ⥤ Sr) (Lbr : Sr ⥤ Tr) (Labr : Xr ⥤ Tr)
    (Las : Xs ⥤ Ss) (Lbs : Ss ⥤ Ts) (Labs : Xs ⥤ Ts)
    (cr : Labr ≅ Lar ⋙ Lbr) (cs : Labs ≅ Las ⋙ Lbs)
    (FX : Xr ⥤ Xs) (FS : Sr ⥤ Ss) (FT : Tr ⥤ Ts)
    (qa : FX ⋙ Las ≅ Lar ⋙ FS) (qb : FS ⋙ Lbs ≅ Lbr ⋙ FT)
    (qab : FX ⋙ Labs ≅ Labr ⋙ FT) : Prop :=
  ∀ M : Xr, qab.hom.app M ≫ FT.map (cr.hom.app M) =
    cs.hom.app (FX.obj M) ≫ Lbs.map (qa.hom.app M) ≫ qb.hom.app (Lar.obj M)

end CategoryTheory
