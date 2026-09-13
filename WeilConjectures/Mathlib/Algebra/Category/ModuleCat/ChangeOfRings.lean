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
morphism of `R`-modules between the restrictions of scalars, that this construction is
functorial, and that an element of `R` killed by `φ` acts as zero on the restriction of scalars
along `φ`.

The additive map is taken to be a morphism of the category `Ab` rather than an `AddMonoidHom`:
this is what makes the construction usable without ever unfolding the map.
-/

@[expose] public section

universe v

open CategoryTheory

namespace ModuleCat

/-- An additive map from an `S`-module to an `S'`-module which is semilinear over two ring maps
`φ : R ⟶ S` and `ψ : R ⟶ S'` out of a common ring `R`, as a morphism of `R`-modules between
the restrictions of scalars. -/
noncomputable def ofSemilinear {R S S' : CommRingCat.{v}} (φ : R ⟶ S)
    (ψ : R ⟶ S') {A B : Ab.{v}} [Module S A] [Module S' B] (g : A ⟶ B)
    (hg : ∀ (r : R) (a : A), g (φ r • a) = ψ r • g a) :
    (restrictScalars φ.hom).obj (of S A) ⟶ (restrictScalars ψ.hom).obj (of S' B) :=
  ofHom (X := (restrictScalars φ.hom).obj (of S A))
    (Y := (restrictScalars ψ.hom).obj (of S' B))
    { toFun := g
      map_add' := map_add _
      map_smul' := hg }

@[simp]
lemma ofSemilinear_apply {R S S' : CommRingCat.{v}} (φ : R ⟶ S)
    (ψ : R ⟶ S') {A B : Ab.{v}} [Module S A] [Module S' B] (g : A ⟶ B)
    (hg : ∀ (r : R) (a : A), g (φ r • a) = ψ r • g a) (a : A) :
    (ofSemilinear φ ψ g hg).hom a = g a := rfl

/-- A semilinear map whose underlying additive map is the identity is the identity. -/
lemma ofSemilinear_eq_id {R S : CommRingCat.{v}} (φ : R ⟶ S) {A : Ab.{v}} [Module S A]
    (g : A ⟶ A) (hg : ∀ (r : R) (a : A), g (φ r • a) = φ r • g a) (hid : g = 𝟙 A) :
    ofSemilinear φ φ g hg = 𝟙 ((restrictScalars φ.hom).obj (of S A)) := by
  subst hid
  rfl

/-- Composing two semilinear maps gives the semilinear map of the composite. -/
lemma ofSemilinear_comp {R S S' S'' : CommRingCat.{v}} (φ : R ⟶ S) (ψ : R ⟶ S') (χ : R ⟶ S'')
    {A B C : Ab.{v}} [Module S A] [Module S' B] [Module S'' C] (g : A ⟶ B)
    (hg : ∀ (r : R) (a : A), g (φ r • a) = ψ r • g a) (g' : B ⟶ C)
    (hg' : ∀ (r : R) (b : B), g' (ψ r • b) = χ r • g' b) (g'' : A ⟶ C)
    (hg'' : ∀ (r : R) (a : A), g'' (φ r • a) = χ r • g'' a) (hcomp : g ≫ g' = g'') :
    ofSemilinear φ ψ g hg ≫ ofSemilinear ψ χ g' hg' = ofSemilinear φ χ g'' hg'' := by
  subst hcomp
  rfl

/-- An element of `R` killed by `φ : R →+* S` acts as zero on the restriction of scalars
along `φ`. -/
lemma restrictScalars.smul_eq_zero {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (M : ModuleCat.{v} S) {r : R} (hr : φ r = 0) (m : (restrictScalars φ).obj M) : r • m = 0 := by
  rw [restrictScalars.smul_def, hr, zero_smul]

end ModuleCat
