/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.EpiMono

/-! # Transposing the supported coefficient square

The exceptional transposition step of the finite reduction of purity.

## Implementation details

Apply injectivity of the smaller exceptional counit transpose and precompose with the epic
compact-support comparison. Counit naturality and naturality of the support comparison move the
input map and the larger orientation into place, and the reduced-counit normalization replaces
the remaining pair by the reduction of the larger counit. No flatness assumption is used.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction

/-- A reduced supported-class square transposes to the orientation square. -/
theorem orientationSquare_of_supportedSquare
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ⥤ D) (G : D ⥤ C) (F' : C' ⥤ D') (G' : D' ⥤ C')
    (S : C ⥤ C') (T : D ⥤ D')
    {A : C} {L : D} {A' : C'} {L' : D'}
    (a : A ⟶ G.obj L) (a' : A' ⟶ G'.obj L')
    (u : S.obj A ⟶ A') (j : T.obj L ⟶ L')
    (b : S.obj (G.obj L) ⟶ G'.obj (T.obj L))
    (qA : T.obj (F.obj A) ⟶ F'.obj (S.obj A))
    (qG : T.obj (F.obj (G.obj L)) ⟶ F'.obj (S.obj (G.obj L)))
    (ε : F.obj (G.obj L) ⟶ L)
    (εT : F'.obj (G'.obj (T.obj L)) ⟶ T.obj L)
    (ε' : F'.obj (G'.obj L') ⟶ L') [Epi qA]
    (hinj : Function.Injective (fun h : S.obj A ⟶ G'.obj L' ↦ F'.map h ≫ ε'))
    (ha : T.map (F.map a) ≫ qG = qA ≫ F'.map (S.map a))
    (hj : F'.map (G'.map j) ≫ ε' = εT ≫ j)
    (hb : qG ≫ F'.map b ≫ εT = T.map ε)
    (hclass : T.map (F.map a ≫ ε) ≫ j = qA ≫ F'.map u ≫ F'.map a' ≫ ε') :
    S.map a ≫ b ≫ G'.map j = u ≫ a' := by
  apply hinj
  apply (cancel_epi qA).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [hj, ← reassoc_of% ha, reassoc_of% hb]
  simpa only [Functor.map_comp, Category.assoc] using hclass

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
