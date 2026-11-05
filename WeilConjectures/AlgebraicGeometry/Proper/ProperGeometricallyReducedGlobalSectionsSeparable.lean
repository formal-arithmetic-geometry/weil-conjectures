/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.RingTheory.Finite.FiniteExtensionTensorAlgebraicClosureReduced
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective

/-!
# Separability of global sections of a proper geometrically reduced scheme

Source: Stacks Project, Varieties, Lemma 0BUG (clause (4))
(blueprint: lem-pc-proper-geometrically-reduced-global-sections-separable).

The `k`-algebra structure on `Γ(X, ⊤)` is the structure map
`AlgebraicGeometry.Scheme.globalSectionsRingHom`, and the field structure is the one given by
`IsField` on the ring `Γ(X, ⊤)`, so both agree with the scheme's own ring structure.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

end AlgebraicGeometry
