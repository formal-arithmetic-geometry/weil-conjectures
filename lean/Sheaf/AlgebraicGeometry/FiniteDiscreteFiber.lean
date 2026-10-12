/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import Sheaf.RingTheory.FiniteTypeAlgebraFiniteSpectrum

/-!
# Finite fibres of locally finite type morphisms

Source: the Weil conjectures blueprint, chapter `sec-abelian-varieties`, unit
`sk-prop-av-pqf-finite` (blueprint: pqf-lem-locqf-fibre-discrete).
The isolated-point criterion is Stacks Project, Tag 01TH.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite set-theoretic fibre of a locally finite type morphism is finite discrete,
and the morphism is quasi-finite at every point above it.
Source: blueprint `sec-abelian-varieties/sk-prop-av-pqf-finite`, finite fibre over a point
(blueprint: pqf-lem-locqf-fibre-discrete); Stacks Project, Tag 01TH for the last step.

Proof: Choose affine opens `V = Spec R` containing `s` and `U = Spec A` mapping into `V`.
The ring map `R → A` is of finite type by `lem-weil-pbc-lft-affine-pairs`; base change
makes the fibre algebra finite type over the residue field. By
`lem-weil-pbc-open-fibre-product` and `lem-weil-pbc-fibre-product-affine-spectra`, the
inverse image of `U` in the fibre is the spectrum of this fibre algebra.
By `def-pc-scheme-fibre`, the fibre is homeomorphic to the finite set-theoretic fibre,
so each such affine fibre spectrum has finitely many points.
By `pqf-lem-finite-type-algebra-finite-spectrum`, these affine fibre spectra are discrete.
They form an open cover of the fibre, so every singleton in the fibre is open, and the
whole fibre is finite discrete. For any `x` above `s`, choose such `U` containing `x`.
By `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs`, the finite-type map
`R → A` is quasi-finite at the prime of `x`. These affine opens therefore witness
`IsQuasiFiniteAtPoint f x` by `pqf-def-quasifinite`. The scheme and morphism conventions
are those of `def-weil-pbc-scheme-conventions`. -/
theorem finite_discrete_fiber_and_isQuasiFiniteAtPoint
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (s : S)
    [AlgebraicGeometry.LocallyOfFiniteType f] (hf : (f ⁻¹' {s}).Finite) :
    Finite (f.fiber s) ∧ DiscreteTopology (f.fiber s) ∧
      ∀ x : X, f x = s → IsQuasiFiniteAtPoint f x := by
  sorry

end AlgebraicGeometry.Scheme.Hom
