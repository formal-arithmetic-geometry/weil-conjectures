/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenDescentNormalization
public import WeilConjectures.WeilSheaf.SmoothPurityDescentPasting
public import WeilConjectures.WeilSheaf.SmoothPurityShriekWeilUniversality
public import WeilConjectures.WeilSheaf.SmoothPurityShriekDescentComparisons

/-! # The geometric carrier of descended compact support -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
  (c : Compactification f) (h : f ≫ t = s)
  (hi : UpperStarWeilCompatible Λ c.i (c.i_comp_g_comp h))
  (hg : UpperStarWeilCompatible Λ c.g (rfl : c.g ≫ t = c.g ≫ t))

variable
  {P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
  {N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))}
  (ε : (rightDerivedLowerShriekOfCompactification Λ c).obj P ⟶ N)

end AlgebraicGeometry.ProEtale.CondensedRing
