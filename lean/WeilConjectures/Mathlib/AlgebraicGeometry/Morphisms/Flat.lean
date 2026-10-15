/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.Localization
public import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Flatness descends along flat surjections of the source

If `u : X' ⟶ X` is flat and surjective and `u ≫ f` is flat, then `f` is flat: at a point `x`
with preimage `x'`, the local ring map `𝒪_{X,x} ⟶ 𝒪_{X',x'}` is flat and local, hence faithfully
flat, and flatness of `𝒪_{X',x'}` over `𝒪_{S,f(x)}` descends to `𝒪_{X,x}`.

## Main results

- `AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective` (blueprint `lem-pc-flat-source-descent`).

## Implementation notes

Every morphism `X ⟶ Spec k` to the spectrum of a field is flat (blueprint `lem-pc-flat-field`).
This is Mathlib's low-priority instance `Flat f` for `f : X ⟶ Y` with `[Subsingleton Y]`
`[IsIntegral Y]`, found by `inferInstance`, so it is not restated here.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Flatness descends along a flat surjection on the source.** If `u : X' ⟶ X` is flat and
surjective and `u ≫ f` is flat, then `f` is flat.

(blueprint: `lem-pc-flat-source-descent`) -/
theorem Flat.of_comp_of_flat_of_surjective {X' X S : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [Flat (u ≫ f)] : Flat f := by
  refine Flat.of_stalkMap f fun x ↦ ?_
  obtain ⟨x', rfl⟩ := u.surjective x
  have h := Flat.stalkMap (u ≫ f) x'
  rw [Scheme.Hom.stalkMap_comp] at h
  have hu := Flat.stalkMap u x'
  algebraize [(f.stalkMap (u x')).hom, (u.stalkMap x').hom,
    (u.stalkMap x').hom.comp (f.stalkMap (u x')).hom]
  have : Module.FaithfullyFlat (X.presheaf.stalk (u x')) (X'.presheaf.stalk x') :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ hu (u.toLRSHom.prop x')
  have : Module.Flat (S.presheaf.stalk (f (u x'))) (X'.presheaf.stalk x') := h
  exact Module.Flat.of_flat_of_faithfullyFlat (B := X.presheaf.stalk (u x'))
    (C := X'.presheaf.stalk x')

/-- The canonical morphism `Spec 𝒪_{X,x} ⟶ X` through an affine open `U ∋ x` is flat: it is
`Spec` of the localization `Γ(X, U) ⟶ 𝒪_{X,x}` followed by an open immersion. -/
instance IsAffineOpen.flat_fromSpecStalk {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) : Flat (hU.fromSpecStalk hx) := by
  dsimp [IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [Flat.SpecMap_iff]
    let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
  infer_instance

/-- The canonical morphism `Spec 𝒪_{X,x} ⟶ X` is flat. -/
instance Scheme.flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) :=
  IsAffineOpen.flat_fromSpecStalk _ _

end AlgebraicGeometry
