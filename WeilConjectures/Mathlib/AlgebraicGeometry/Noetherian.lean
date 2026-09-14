/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The source of a quasi-compact morphism of finite type to a Noetherian scheme

`AlgebraicGeometry.LocallyOfFiniteType.isNoetherian`: if `S` is Noetherian and `f : X ⟶ S` is
locally of finite type and quasi-compact, then `X` is Noetherian. In particular this applies to
a proper morphism, which is both.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **A quasi-compact scheme of finite type over a Noetherian scheme is Noetherian**: it is
locally Noetherian because `f` is locally of finite type
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, Stacks Project Tag 01T6), and
quasi-compact because `f` is quasi-compact. The Stacks tag covers the locally Noetherian half
only, hence is cited here rather than attached as a `@[stacks]` attribute. -/
theorem LocallyOfFiniteType.isNoetherian {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

end AlgebraicGeometry
