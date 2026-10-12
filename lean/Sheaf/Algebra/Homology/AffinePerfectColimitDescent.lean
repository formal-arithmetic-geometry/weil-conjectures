/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Algebra.FinitePresentationColimit

/-! # Affine descent of bounded finite projective complexes

Source: Stacks Project, More on Algebra, Lemma 15.76.18 (Tag 0BC7), affine complex case
(blueprint: lem-pc-affine-perfect-colimit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A bounded complex of finite projective modules over a directed colimit of commutative
rings descends, as a complex, to one stage.
Source: Stacks Project, More on Algebra, Lemma 15.76.18 (Tag 0BC7), affine complex case
(blueprint: lem-pc-affine-perfect-colimit-descent).

Proof: Choose bounds outside which the complex is zero. Its finitely many terms are finite
projective, hence finitely presented. Descend them by
`lem-pc-fp-module-map-descent-affine`, and use directedness to choose one stage. Descend each
splitting as a summand of a finite free module, and use the equality clause of that lemma to
make the splitting identities hold after enlarging the stage; the descended terms are then
finite projective. Descend the finitely many differentials by the maps clause of the same
lemma. Use its equality clause to impose the finitely many relations that successive
differentials compose to zero, again at a common later stage. The termwise base-change
isomorphisms commute with the differentials and assemble to the asserted complex isomorphism.
-/
theorem exists_finite_projective_model_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (P : CochainComplex (ModuleCat.{u} (colimit F : CommRingCat.{u})) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hfinite : ∀ n : ℤ, Module.Finite (colimit F : CommRingCat.{u}) (P.X n))
    (hprojective : ∀ n : ℤ, Module.Projective (colimit F : CommRingCat.{u}) (P.X n)) :
    ∃ (i : I) (Pi : CochainComplex (ModuleCat.{u} (F.obj i)) ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Pi.X n)) ∧
      (∀ n : ℤ, Module.Finite (F.obj i) (Pi.X n)) ∧
      (∀ n : ℤ, Module.Projective (F.obj i) (Pi.X n)) ∧
      Nonempty (((ModuleCat.extendScalars (colimit.ι F i).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Pi ≅ P) := by
  sorry

end CochainComplex
