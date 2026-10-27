/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Sheaf.AlgebraicGeometry.IsRegularScheme

/-! # Regular morphisms of schemes

Source: Stacks Project, Tag 07BZ, and Temkin, Non-embedded Desingularization,
§2.1.1 (blueprint: def-per-regular-scheme-morphism).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A regular scheme morphism is flat with geometrically regular fibres, tested after
all finite extensions of each residue field. The test fields have the scheme's universe,
so that the original residue field is included, and finite extensions can all be represented.
Source: Stacks Project, Tag 07BZ; Temkin §2.1.1
(blueprint: def-per-regular-scheme-morphism). -/
def IsRegularSchemeMorphism {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  Flat f ∧ ∀ (x : X) (K : Type u) [Field K] [Algebra (X.residueField x) K]
    [FiniteDimensional (X.residueField x) K],
    IsRegularScheme (pullback (f.fiberToSpecResidueField x)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))))

end AlgebraicGeometry
