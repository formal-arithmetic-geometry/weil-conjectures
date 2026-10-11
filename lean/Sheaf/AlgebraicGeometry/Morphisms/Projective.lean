/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF lead L
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Projective morphisms of schemes

Source: the blueprint of the Weil conjectures, chapter `sec-abelian-varieties`, unit
`sk-def-av-jacobian` (blueprint: def-pc-projective-morphism); Stacks Project, Morphisms of
Schemes, Definition 29.43.1 (Tag 01W8), its H-projective convention.

A scheme `X` over a field `k` is *projective over `k`* when its structure morphism is projective,
that is, `IsProjective (X ↘ Spec (.of k))`; no separate declaration is needed for it.

## Main definitions

- `AlgebraicGeometry.IsHProjective`: `f : X ⟶ S` factors as a closed immersion into `ℙⁿ_S`
  followed by the structure morphism.
- `AlgebraicGeometry.IsProjective`: `f` is H-projective and quasi-compact.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: def-pc-projective-morphism) A morphism of schemes `f : X ⟶ S` is *H-projective*
(relatively projective) if for some integer `n ≥ 0` there is a closed immersion
`i : X ⟶ ℙⁿ_S` with `f = π ∘ i`, where `π : ℙⁿ_S ⟶ S` is the structure morphism
(Stacks, Tag 01W8). The classical `ℙⁿ_S`, with `n + 1` homogeneous coordinates, is
`ℙ(ULift (Fin (n + 1)); S)` of `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`. -/
class IsHProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  exists_closedImmersion : ∃ (n : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)),
    IsClosedImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = f

/-- (blueprint: def-pc-projective-morphism) A morphism of schemes `f : X ⟶ S` is *projective*,
in the convention of this blueprint, if it is H-projective and quasi-compact (Stacks, Tag 01W8,
H-projective convention; Stacks' unqualified "projective" is a possibly broader notion).
A scheme `X` over a field `k` is projective over `k` when `IsProjective (X ↘ Spec (.of k))`. -/
class IsProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop extends IsHProjective f,
    QuasiCompact f

end AlgebraicGeometry
