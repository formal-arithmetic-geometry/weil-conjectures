/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Projective morphisms of schemes

A morphism of schemes `f : X ⟶ S` is *projective* if it factors as a closed immersion
`X ⟶ ℙ(n; S)` into a projective space over `S` with finitely many homogeneous coordinates,
followed by the structure morphism `ℙ(n; S) ↘ S`.

## Main definitions

- `AlgebraicGeometry.IsProjective` — the class of projective morphisms.

## Main results

- `AlgebraicGeometry.IsProjective.isProper` — a projective morphism is proper.

## Implementation notes

Stacks 01W8 defines `f : X ⟶ S` to be projective if there is a quasi-coherent graded
`𝒪_S`-algebra `𝒜`, generated in degree one by a finite type degree-one part, together with an
`S`-isomorphism of `X` with a closed subscheme of `Proj_S 𝒜`. The "H-projective" condition
formalised here always implies that one; the converse needs a hypothesis on the base, and holds
for example whenever `S` admits an ample family of line bundles. The `@[stacks 01W8]` tag on
`IsProjective` refers to part (2) of that definition, which is the H-projective condition itself.

No quasi-compactness hypothesis has to be imposed separately, since the factorisation already
exhibits `f` as a closed immersion (finite, hence proper) followed by the proper morphism
`ℙ(n; S) ↘ S`.

The index type of `ℙ(n; S)` lives in the same universe as `S`, so the `n + 1` homogeneous
coordinates of the classical `ℙⁿ_S` are indexed by `ULift.{u} (Fin (n + 1))` rather than by
`Fin (n + 1)`. Since `ℙ(n; S)` is not (yet) functorial in the index type `n`, the definition
below is stated with this concrete index type rather than with an arbitrary finite one.

## Blueprint

`IsProjective` implements `def:pc-projective-morphism` and `IsProjective.isProper` implements
`lem:pc-projective-proper`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ S` is **projective** if it factors as a closed immersion
into a projective space `ℙ(n; S)` over `S` with finitely many homogeneous coordinates followed
by the structure morphism `ℙ(n; S) ↘ S`.
(blueprint: `def:pc-projective-morphism`, Stacks 01W8) -/
@[stacks 01W8]
class IsProjective (f : X ⟶ S) : Prop where
  /-- A projective morphism factors as a closed immersion into some `ℙ(n; S)` followed by the
  structure morphism of that projective space. -/
  exists_isClosedImmersion : ∃ (n : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin n); S)),
    IsClosedImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin n); S) ↘ S = f

/-- A closed immersion into a projective space over `S`, compatible with the morphisms to `S`,
exhibits `f` as a projective morphism. -/
lemma IsProjective.mk' {f : X ⟶ S} {n : ℕ} (i : X ⟶ ℙ(ULift.{u} (Fin n); S))
    [IsClosedImmersion i] (hi : i ≫ ℙ(ULift.{u} (Fin n); S) ↘ S = f) : IsProjective f :=
  ⟨n, i, ‹_›, hi⟩

/-- **A projective morphism is proper.**
(blueprint: `lem:pc-projective-proper`) -/
instance (priority := 100) IsProjective.isProper (f : X ⟶ S) [IsProjective f] : IsProper f := by
  -- `f` factors as a closed immersion, which is finite and hence proper, followed by the
  -- proper structure morphism of a projective space.
  obtain ⟨n, i, hi, rfl⟩ := IsProjective.exists_isClosedImmersion (f := f)
  infer_instance

section RespectsIso

instance IsProjective.respectsIso : MorphismProperty.RespectsIso @IsProjective.{u} where
  precomp e he f hf := by
    have : IsIso e := he
    obtain ⟨n, i, hi, rfl⟩ := hf.exists_isClosedImmersion
    exact ⟨n, e ≫ i, inferInstance, by rw [Category.assoc]⟩
  postcomp e he f hf := by
    have : IsIso e := he
    obtain ⟨n, i, hi, rfl⟩ := hf.exists_isClosedImmersion
    exact ⟨n, i ≫ ProjectiveSpace.map _ e, inferInstance, by
      rw [Category.assoc, ProjectiveSpace.map_over, ← Category.assoc]⟩

end RespectsIso

end AlgebraicGeometry
