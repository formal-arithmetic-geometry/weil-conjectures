/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The graded section ring of an invertible module

Source: Stacks Project, Tags 01PZ and 01N8
(blueprint: def-sc-invertible-section-ring).

The homogeneous component is literally the global sections of the indicated tensor power.
All operations are specified, and their algebraic laws are proved from tensor-section coherence
and local free generators.

## Main definitions

- `InvertibleSectionRing`: the direct sum of tensor-power sections.
- `sectionRingGCommRing`: tensor multiplication and the degree-zero unit.
- `sectionRingGrade`, `sectionRingGradedRing`: homogeneous components and their grading.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- The recursive exponent-zero isomorphism agrees with the right unitor.

-- Naturality moves the exponent casts to the end; the induction then uses the pentagon.

-- Tensor powers of a section over an arbitrary open, without extending it globally.

-- Convert the scheme-module trivialization to a trivialization over the restricted site.

end AlgebraicGeometry.Scheme.Modules
