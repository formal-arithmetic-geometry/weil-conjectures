/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import Sheaf.AlgebraicGeometry.ProperBasic
import Sheaf.AlgebraicGeometry.Morphisms.GenericallyFiniteQuasiFiniteOverDimensionOne

/-!
# A proper generically finite morphism is finite near local dimension at most one

Source: Stacks Project, Varieties, Tag 0AB7, Lemma `finite-in-codim-1`, condition (1)
(blueprint: lem-per-generically-finite-proper-near-dimension-one).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper morphism with algebraic residue extensions at the generic points of all
irreducible components is finite near a point whose local ring is Noetherian of
Krull dimension at most one.

Source: Stacks Project, Varieties, Tag 0AB7, condition (1)
(blueprint: lem-per-generically-finite-proper-near-dimension-one).

Proof:
1. Properness implies locally finite type (`def-weil-proper-morphism`,
   `def-weil-finite-type-morphism`). Apply
   `lem-per-generically-finite-quasifinite-over-dimension-one` at `x`, using precisely
   the local Noetherian, dimension and generic algebraicity hypotheses. Thus `f` is
   quasi-finite at every point over `x`.
2. By `def-pc-scheme-fibre`, the fibre `f.fiber x` is homeomorphic to the subspace
   `f ⁻¹' {x}`. The theorem `lem-weil-pbc-quasi-finite-at-point-isolated` makes every
   singleton in this fibre open. Thus the fibre is discrete.
3. Its morphism to `Spec (X.residueField x)` is proper by clause (1) of
   `lem-pc-proper-base-change`. This base is affine (`def-weil-affine-spectrum`), so
   `pqf-lem-proper-basic` makes the fibre quasi-compact.
4. The singleton open cover has a finite subcover (`def-weil-pbc-quasi-compact-scheme`).
   Hence the fibre has finitely many points, including when it is empty. Transport
   this finiteness through the fibre homeomorphism to `f ⁻¹' {x}`.
5. Apply `lem-trf-proper-finite-fibre-finite-near` (Stacks 02UP), which requires no
   global Noetherian hypothesis, to obtain the asserted finite restriction.

The algebra structure in `hgeneric` is explicitly that induced by `f.residueFieldMap`;
`Algebra.IsAlgebraic` means that every element annihilates a nonzero polynomial over
that source field, with no separability or finite-degree hypothesis.
-/
theorem exists_isFinite_morphismRestrict_of_generic_algebraic_of_local_dim_le_one
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsProper f] (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (hgeneric : ∀ (Z : Set Y), Z ∈ irreducibleComponents Y →
      ∀ (η : Y), IsGenericPoint η Z →
        @Algebra.IsAlgebraic (X.residueField (f η)) (Y.residueField η) _ _
          (f.residueFieldMap η).hom.toAlgebra) :
    ∃ V : X.Opens, x ∈ V ∧ IsFinite (f ∣_ V) := by
  sorry

end AlgebraicGeometry
