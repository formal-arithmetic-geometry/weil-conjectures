/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Semilinear maps and restriction of scalars

Let `φ : R ⟶ S` and `ψ : R ⟶ S'` be two ring maps out of a common ring. We record that an
additive map from an `S`-module to an `S'`-module which is semilinear over `φ` and `ψ` is a
morphism of `R`-modules between the restrictions of scalars, and that an element of `R` killed
by `φ` acts as zero on the restriction of scalars along `φ`.

The additive map is taken to be a morphism of the category `Ab` rather than an `AddMonoidHom`:
this is what makes the construction usable without ever unfolding the map.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ModuleCat

/-- An additive map from an `S`-module to an `S'`-module which is semilinear over two ring maps
`φ : R ⟶ S` and `ψ : R ⟶ S'` out of a common ring `R`, as a morphism of `R`-modules between the
restrictions of scalars. -/
noncomputable def ofSemilinear {R S S' : CommRingCat.{u}} (φ : R ⟶ S) (ψ : R ⟶ S')
    {A B : Ab.{u}} [Module S A] [Module S' B] (g : A ⟶ B)
    (hg : ∀ (r : R) (a : A), g (φ r • a) = ψ r • g a) :
    (restrictScalars φ.hom).obj (of S A) ⟶ (restrictScalars ψ.hom).obj (of S' B) :=
  ofHom (X := (restrictScalars φ.hom).obj (of S A))
    (Y := (restrictScalars ψ.hom).obj (of S' B))
    { toFun := g
      map_add' := map_add _
      map_smul' := hg }

@[simp]
lemma ofSemilinear_apply {R S S' : CommRingCat.{u}} (φ : R ⟶ S) (ψ : R ⟶ S')
    {A B : Ab.{u}} [Module S A] [Module S' B] (g : A ⟶ B)
    (hg : ∀ (r : R) (a : A), g (φ r • a) = ψ r • g a) (a : A) :
    (ofSemilinear φ ψ g hg).hom a = g a := rfl

/-- An element of `R` killed by `φ : R ⟶ S` acts as zero on the restriction of scalars
along `φ`. -/
lemma smul_restrictScalars_eq_zero {R S : CommRingCat.{u}} (φ : R ⟶ S) (A : Ab.{u}) [Module S A]
    {r : R} (hr : φ r = 0) (y : (restrictScalars φ.hom).obj (of S A)) : r • y = 0 := by
  change φ r • (y : A) = 0
  rw [hr, zero_smul]

end ModuleCat
