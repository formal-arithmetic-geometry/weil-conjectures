/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityPullCoefficientComposition

/-! # Changing coefficients of a geometric pullback datum twice -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] (b : Λ' ⟶ Λ'') [IsMonHom b]
  (c : Λ ⟶ Λ'') [IsMonHom c] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Change coefficients of a specified geometric pullback comparison. -/
noncomputable def purityCoefficientPullbackIso
    {M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    {N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : (g)^*⟦Λ⟧.obj M ≅ N) :
    (g)^*⟦Λ'⟧.obj ((Mod.extendScalars (coefficientMap a Y)).obj M) ≅
      (Mod.extendScalars (coefficientMap a X)).obj N :=
  ((pullIso a g).app M).symm ≪≫ (Mod.extendScalars (coefficientMap a X)).mapIso e

end AlgebraicGeometry.ProEtale.CondensedRing
