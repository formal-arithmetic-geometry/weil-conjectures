/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.AffineFiniteFreeSheafComplexLift

/-! # Finite free models for one degree of derived fibres

Source: Stacks Project, Tag 0BDI, affine reduction and stupid truncation.
(blueprint: lem-sc-pseudo-coherent-fiber-finite-free-model).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A fixed degree of the derived fibres of a pseudo-coherent object is computed on a
neighbourhood by one bounded finite free algebraic complex.

Source: Stacks Project, Tag 0BDI, affine reduction and stupid truncation.
(blueprint: lem-sc-pseudo-coherent-fiber-finite-free-model).

Proof: At x choose the bounded-above finite free sheaf complex supplied by
IsPseudoCoherent. Shrink its neighbourhood to an affine open U = Spec A containing x.
Restriction preserves the free terms and the derived comparison. Transport the
restricted complex to Spec A. Apply
affine_finiteFree_sheaf_complex_lift to obtain a bounded-above complex F of finite
free A-modules and an isomorphism of its associated sheaf complex with that complex.
Set K to the stupid
truncation of F below i - 1. It is bounded above by the bound of F and below by i - 1;
if the upper bound is smaller, the zero complex has the required bounds. The terms
and both adjacent differentials in degree i are unchanged, so K and F have identical
H^i after tensoring with any residue field. Finite free terms are flat, and the
bounded-above flat pullback comparison computes each derived fibre termwise.
The residue-field identification of the affine chart gives a linear isomorphism
between that fibre cohomology and H^i(K tensor_A kappa(p)). Taking finrank gives the
asserted equality for every point of U. No global quasi-separatedness is used. -/
theorem exists_pseudoCoherent_fiber_finiteFree_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPseudoCoherent X E) (i : ℤ) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ (A : Type u) (_ : CommRing A) (e : ↥(U : Set X) ≃ₜ PrimeSpectrum A)
        (K : CochainComplex (ModuleCat.{u} A) ℤ),
        (∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b) ∧
        (∀ n : ℤ, Module.Free A (K.X n) ∧ Module.Finite A (K.X n)) ∧
        ∀ z : U, derivedFiberBetti X E i z =
          Module.finrank (e z).asIdeal.ResidueField
            ((((ModuleCat.extendScalars
              (algebraMap A (e z).asIdeal.ResidueField)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K).homology i) := by sorry

end AlgebraicGeometry.Scheme
