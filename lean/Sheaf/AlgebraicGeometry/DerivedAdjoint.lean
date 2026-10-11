/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedPullback

/-! # Derived pullback/direct image adjunction for schemes

Source: literature/stacks-project/cohomology.tex, Tag 079W, Cohomology Lemma
cohomology-lemma-adjoint (blueprint: lem-pc-ringed-spaces-derived-adjoint).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- For a morphism of schemes, derived pullback is left adjoint to derived direct image.

Proof (the three steps of the node):
1. Apply `lem-pc-module-pullback-adjunction` to the underlying ringed-space morphism:
   the tensor module pullback is left adjoint to the underived direct image.
2. Apply `lem-pc-derived-adjoint-functors` (Stacks, Tag 09T5) to this adjunction.
   By `def-pc-derived-pullback` and `def-pc-derived-direct-image`, the chosen functors
   are respectively its left and right derived functors, defined everywhere on the
   unbounded derived categories of `def-pc-derived-category`, and computed by K-flat
   and K-injective resolutions. The result supplies the Hom-set equivalences.
3. The functoriality clause of `lem-pc-derived-adjoint-functors` makes these
   equivalences natural in both variables, which is precisely an adjunction.
Source: literature/stacks-project/cohomology.tex, Tag 079W, Cohomology Lemma
cohomology-lemma-adjoint (blueprint: lem-pc-ringed-spaces-derived-adjoint). -/
theorem nonempty_derivedPullbackAdjunction (f : X ⟶ Y) :
    Nonempty (derivedPullback f ⊣ schemeDerivedDirectImage f) := by
  sorry

end AlgebraicGeometry
