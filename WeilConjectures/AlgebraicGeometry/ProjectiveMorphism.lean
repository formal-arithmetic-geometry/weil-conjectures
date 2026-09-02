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

Stacks 01W7 defines `f : X ⟶ S` to be projective if there is a quasi-coherent graded
`𝒪_S`-algebra `𝒜`, generated in degree one by a finite type degree-one part, together with an
`S`-isomorphism of `X` with a closed subscheme of `Proj_S 𝒜`. Over a base admitting an ample
family this is equivalent to the "H-projective" condition used here, and in the generality of
this file the two conditions agree because the index type is required to be finite: the
factorisation exhibits `f` as a composition of a closed immersion with a proper morphism, so no
quasi-compactness hypothesis has to be imposed separately (closed immersions are finite, hence
proper, and `ℙ(n; S) ↘ S` is proper for finite `n`).

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

variable {X Y S : Scheme.{u}}

/-- A morphism of schemes `f : X ⟶ S` is **projective** if it factors as a closed immersion
into a projective space `ℙ(n; S)` over `S` with finitely many homogeneous coordinates followed
by the structure morphism `ℙ(n; S) ↘ S`.
(blueprint: `def:pc-projective-morphism`, Stacks 01W7) -/
@[stacks 01W7]
class IsProjective (f : X ⟶ S) : Prop where
  exists_isClosedImmersion : ∃ (n : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin n); S)),
    IsClosedImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin n); S) ↘ S = f

/-- A closed immersion into a projective space over `S`, compatible with the morphisms to `S`,
exhibits `f` as a projective morphism. -/
lemma IsProjective.mk' {f : X ⟶ S} {n : ℕ} (i : X ⟶ ℙ(ULift.{u} (Fin n); S))
    [IsClosedImmersion i] (hi : i ≫ ℙ(ULift.{u} (Fin n); S) ↘ S = f) : IsProjective f :=
  ⟨n, i, ‹_›, hi⟩

/-- **A projective morphism is proper.** Indeed it factors as a closed immersion, which is
finite and hence proper, followed by the proper structure morphism of a projective space.
(blueprint: `lem:pc-projective-proper`) -/
instance (priority := 100) IsProjective.isProper (f : X ⟶ S) [IsProjective f] : IsProper f := by
  obtain ⟨n, i, hi, rfl⟩ := IsProjective.exists_isClosedImmersion (f := f)
  infer_instance

section RespectsIso

/-- Projective space over the base is functorial in the base, so an isomorphism of bases
induces an isomorphism of the projective spaces over them. -/
private lemma isIso_projectiveSpaceMap (n : Type u) (e : S ⟶ Y) [IsIso e] :
    IsIso (ProjectiveSpace.map n e) :=
  ⟨ProjectiveSpace.map n (inv e), by
    rw [← ProjectiveSpace.map_comp, IsIso.hom_inv_id, ProjectiveSpace.map_id], by
    rw [← ProjectiveSpace.map_comp, IsIso.inv_hom_id, ProjectiveSpace.map_id]⟩

instance IsProjective.respectsIso : MorphismProperty.RespectsIso @IsProjective.{u} where
  precomp e he f hf := by
    have : IsIso e := he
    obtain ⟨n, i, hi, rfl⟩ := hf.exists_isClosedImmersion
    exact ⟨n, e ≫ i, inferInstance, by rw [Category.assoc]⟩
  postcomp e he f hf := by
    have : IsIso e := he
    obtain ⟨n, i, hi, rfl⟩ := hf.exists_isClosedImmersion
    have := isIso_projectiveSpaceMap (ULift.{u} (Fin n)) e
    exact ⟨n, i ≫ ProjectiveSpace.map _ e, inferInstance, by
      rw [Category.assoc, ProjectiveSpace.map_over, ← Category.assoc]⟩

end RespectsIso

end AlgebraicGeometry
