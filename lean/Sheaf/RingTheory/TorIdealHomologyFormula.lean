/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Cycle formula on the homology of a free resolution

Source: Stacks Project, Algebra, Tags 00M5 and 00M6.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

/-- Source: Stacks Project, Algebra, proof of Tag 00M5 and Remark 00M6.
(blueprint: lem-weil-pbc-tor-ideal-homology-formula)

Proof in words: tensor the exact sequence of the ideal, ring and quotient with
all free resolution terms. Flatness gives injective ideal-tensor maps and right
exactness identifies their cokernels with the quotient-tensor terms. For a
quotient cycle lift y, choose an ideal-tensor preimage of d y. Send it to I ⊗ M
by tensor symmetry and the augmentation. Changing the ideal-tensor preimage
has no effect by injectivity, and changing the lift adds the differential of
an ideal tensor, killed by augmentation. This gives a linear map on cycles
which vanishes on boundaries, hence a linear map on homology. For a finite
expression d y = Σ a_j p_j, choose Σ p_j ⊗ a_j as preimage, giving the formula.
The construction also applies to the zero and unit ideals and the zero module.
-/
theorem exists_tor_ideal_homology_formula
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (hP : ∀ n : ℕ, Module.Free R (P.complex.X n))
    :
    ∃ δH : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology 1 →ₗ[R] (I ⊗[R] M),
      (∀ (z : ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸
        I))).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).cycles 1)
        (y : P.complex.X 1) (k : ℕ) (a : Fin k → I) (p : Fin k → P.complex.X 0),
        ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex).iCycles 1 z = y ⊗ₜ[R] (1 : R ⧸ I) →
        P.complex.d 1 0 y = ∑ j, (a j : R) • p j →
        δH
          (((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homologyπ 1 z) =
          ∑ j, a j ⊗ₜ[R] P.π.f 0 (p j)) := by sorry

end ModuleCat
