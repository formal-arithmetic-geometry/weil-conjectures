/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Defs

/-!

# Nagata's compactification theorem: the main statement

`AlgebraicGeometry.hasCompactification_of_isSeparated_of_finiteType` is the goal of the
whole `WeilConjectures.Compactification` development: a separated morphism of finite
type over a quasi-compact quasi-separated base admits a compactification.

It is stated as a `theorem` producing the `Prop`-valued class
`AlgebraicGeometry.HasCompactification` and is **not** registered as an instance while
its proof is `sorry`. Registering it would be unsound as a development device: the
theorems building the compactification — most importantly
`AlgebraicGeometry.HasCompactification.of_two_open_cover` — take
`[HasCompactification …]` hypotheses for the pieces of a cover, and a global instance
would discharge them from this very statement at every call site, making the induction
circular in a way that `#print axioms` on the *statements* would not reveal.

-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Nagata's compactification theorem**: a separated morphism of finite type onto a
quasi-compact quasi-separated base factors as an open immersion followed by a proper
morphism. -/
theorem hasCompactification_of_isSeparated_of_finiteType [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    HasCompactification f := sorry

end AlgebraicGeometry
