/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Homogeneous sections of a symmetric algebra sheaf

Source: Stacks Project, Modules, Section 01CF and Tag 01CG, with the affine comparison
of the quasi-coherent symmetric algebra (blueprint: def-trf-symmetric-homogeneous-sections).

The degree condition is tested on every affine subopen using the canonical section map.
It uses the existing algebra sheaf and affine grading, and chooses no new algebra.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.SymmetricAlgebraSheaf

/-- A section is homogeneous of degree `n` if its restriction to every affine subopen
is the canonical image of an element of the degree-`n` affine symmetric algebra.
Source: Stacks Project, Modules, Section 01CF and Tag 01CG
(blueprint: def-trf-symmetric-homogeneous-sections). -/
def IsHomogeneousSection {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (U : X.Opens) (s : (algebra F).right.obj.obj (op U)) : Prop :=
  ∀ (V : X.affineOpens) (h : V.1 ≤ U),
    ∃ a : sections F (op V.1), a ∈ (gradedAlgebraData F).grading V n ∧
      sectionMap F (op V.1) a = (algebra F).right.obj.map (homOfLE h).op s

end AlgebraicGeometry.SymmetricAlgebraSheaf
