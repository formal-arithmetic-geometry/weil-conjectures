/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Discriminant

/-!
# An explicit family of local discriminant ideals

Source: Stacks Project, Tag 0BVH, construction before Lemma 49.3.1.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Sections belonging to every discriminant ideal on every free affine subchart.

This is an intersection of inverse-image ideals, with no chosen local bases. The
construction makes sense before its restriction and local-value properties are proved.
Source: Stacks Project, Tag 0BVH, construction before Lemma 49.3.1.
(blueprint: def-sbc-trace-discriminant-section-ideal) -/
noncomputable def traceDiscriminantSectionIdeal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.affineOpens) : Ideal Γ(Y, U.1) :=
  ⨅ (V : Y.affineOpens) (h : V.1 ≤ U.1),
    letI := (f.app V.1).hom.toAlgebra
    ⨅ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1)),
      (Ideal.span {Algebra.discr Γ(Y, V.1) b}).comap
        (Y.presheaf.map (homOfLE h).op).hom

end AlgebraicGeometry.Scheme
