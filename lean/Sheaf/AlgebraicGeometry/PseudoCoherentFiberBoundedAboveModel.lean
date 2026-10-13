/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
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

/-! # Local bounded-above algebraic models of pseudo-coherent fibres

Source: Stacks Project, Tags 08E7 and 0BDI.
(blueprint: lem-sc-pseudo-coherent-fiber-bounded-above-model).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A single bounded-above finite-free algebraic complex computes all fibre degrees
on an affine neighbourhood. This does not assert a bounded representative.

Source: Stacks Project, Tags 08E7 and 0BDI, affine reduction.
(blueprint: lem-sc-pseudo-coherent-fiber-bounded-above-model).

Proof: Use pseudo-coherence to choose a bounded-above finite-free sheaf complex
on a neighbourhood of x. Choose an affine open inside that neighbourhood containing x.
Restrict its terms and derived comparison, and transport along the affine chart.
Restriction preserves free sheaves of finite rank and zero terms. Full faithfulness
of the associated-sheaf functor lifts the resulting complex to an algebraic complex F,
by affine_finiteFree_sheaf_complex_lift, with the same upper bound and finite free terms.
Finite free terms are flat. The bounded-above flat derived-pullback comparison therefore
computes the derived pullback to each residue field termwise. Derived pullback commutes
with restriction to the open neighbourhood. On the residue-field spectrum, evaluation
of the cohomology sheaf identifies it with the homology of F tensor the residue field.
The canonical residue-field isomorphism attached to the affine chart transports the
scalar action. It preserves dimension, giving the equality for every degree and point.
This also covers an upper bound below the degree: both vector spaces then vanish. -/
theorem exists_pseudoCoherent_fiber_boundedAbove_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPseudoCoherent X E) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ (A : Type u) (_ : CommRing A) (e : ↥(U : Set X) ≃ₜ PrimeSpectrum A)
        (F : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ),
        F.IsStrictlyLE b ∧
        (∀ n : ℤ, Module.Free A (F.X n) ∧ Module.Finite A (F.X n)) ∧
        ∀ (i : ℤ) (z : U), derivedFiberBetti X E i z =
          Module.finrank (e z).asIdeal.ResidueField
            ((((ModuleCat.extendScalars
              (algebraMap A (e z).asIdeal.ResidueField)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj F).homology i) := by sorry

end AlgebraicGeometry.Scheme
