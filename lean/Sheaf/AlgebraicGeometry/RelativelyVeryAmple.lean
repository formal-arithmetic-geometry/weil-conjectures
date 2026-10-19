/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Relative very ampleness in the projective-bundle convention

Source: Stacks Project, Morphisms, Definition 01VM, and Constructions, Definition 01OB
(blueprint: def-trf-relatively-very-ample).

The witness `D` supplies the degree-one twist with its canonical affine normalization.
Its line is therefore the usual O(1), rather than an arbitrary invertible quotient.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Relative very ampleness means an immersion over the base into P(E), for an arbitrary
quasi-coherent E, pulling the normalized degree-one twist back to L. This definition
imposes no finite-type or local-freeness condition on E and no quasi-compactness condition
on the morphism. The quotient geometry fixes the twist on every affine chart.
Source: Stacks Project, Morphisms, Definition 01VM; Constructions, Tags 01OB and 01OA
(blueprint: def-trf-relatively-very-ample). -/
def IsRelativelyVeryAmple {Y X : Scheme.{u}} (f : Y ⟶ X) (L : Y.Modules) : Prop :=
  ∃ (E : X.Modules) (hE : E.IsQuasicoherent)
    (D : @ProjectiveBundleQuotientGeometry.TautologicalQuotient X E hE)
    (i : Y ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData X E hE).relProj),
      IsImmersion i ∧
      i ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData X E hE).relProjHom = f ∧
      Nonempty ((tensorPullback i).obj D.line ≅ L)

end AlgebraicGeometry.Scheme.Modules
