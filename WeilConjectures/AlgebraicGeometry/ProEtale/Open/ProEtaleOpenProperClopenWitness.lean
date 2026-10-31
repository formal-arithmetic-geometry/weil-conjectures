/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows

/-!
# Clopen geometric witness for an open proper square

This records the geometric factorisation used in the pro-etale acyclicity
argument.  The existence theorem is the geometric part of the argument.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-geometry)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A clopen factorisation of a commutative proper/open square. -/
structure OpenProperClopenWitness {B D C E : Scheme.{u}}
    (p : B ⟶ D) (r : C ⟶ E) (k : C ⟶ B) (i : E ⟶ D) where
  V : Scheme.{u}
  b : V ⟶ B
  s : V ⟶ E
  t : C ⟶ V
  comm : b ≫ p = s ≫ i
  bt : t ≫ b = k
  st : t ≫ s = r
  b_open : IsOpenImmersion b
  s_proper : IsProper s
  t_open : IsOpenImmersion t
  t_closed : IsClosedImmersion t

/-- The fibre-product/clopen construction for a commutative proper/open square.

Source: Stacks Project, Tag 0F7B, case (b), together with Tags 01W4 and 01W6.
The fibre product of the open immersion with the proper map is open, and the
map induced by the commutative square is a proper immersion, hence clopen.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-geometry)
-/
theorem exists_openProperClopenWitness
    {B D C E : Scheme.{u}} (p : B ⟶ D) (r : C ⟶ E)
    (k : C ⟶ B) (i : E ⟶ D)
    [IsProper p] [IsProper r]
    [IsOpenImmersion k] [QuasiCompact k]
    [IsOpenImmersion i] [QuasiCompact i]
    (hcomm : k ≫ p = r ≫ i) :
    Nonempty (OpenProperClopenWitness p r k i) := by
  let V := pullback p i
  let b : V ⟶ B := pullback.fst p i
  let s : V ⟶ E := pullback.snd p i
  let t : C ⟶ V := pullback.lift k r hcomm
  have ht : t ≫ b = k := by
    dsimp only [t, b]
    exact pullback.lift_fst _ _ _
  have hts : t ≫ s = r := by
    dsimp only [t, s]
    exact pullback.lift_snd _ _ _
  have hclopen :
      IsOpenImmersion (ProEtale.StrictTower.squareLift k r p i hcomm) ∧
        IsClosedImmersion (ProEtale.StrictTower.squareLift k r p i hcomm) :=
    ProEtale.StrictTower.squareLift_clopen k r p i hcomm
  let w : OpenProperClopenWitness p r k i := {
    V := V
    b := b
    s := s
    t := t
    comm := by
      dsimp only [b, s]
      exact pullback.condition
    bt := ht
    st := hts
    b_open := by
      dsimp only [b]
      infer_instance
    s_proper := by
      dsimp only [s]
      infer_instance
    t_open := hclopen.1
    t_closed := hclopen.2 }
  exact ⟨w⟩

end AlgebraicGeometry.Scheme
