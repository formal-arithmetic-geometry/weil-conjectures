/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Flatness descends along flat surjections of the source; morphisms to a field are flat

If `u : X' ⟶ X` is flat and surjective and `u ≫ f` is flat, then `f` is flat: at a point `x`
with preimage `x'`, the local ring map `𝒪_{X,x} ⟶ 𝒪_{X',x'}` is flat and local, hence faithfully
flat, and flatness of `𝒪_{X',x'}` over `𝒪_{S,f(x)}` descends to `𝒪_{X,x}`.

## Main results

- `AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective` (blueprint `lem-pc-flat-source-descent`).
- `AlgebraicGeometry.Flat.of_field`: every morphism to the spectrum of a field is flat
  (blueprint `lem-pc-flat-field`).
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

/-- **Every morphism to the spectrum of a field is flat.** Affine-locally `X ⟶ Spec k` is given
by a ring map `k ⟶ A`, and `A` is a free, hence flat, `k`-module. This is the instance for
morphisms to an integral scheme with a single point.

(blueprint: `lem-pc-flat-field`) -/
theorem Flat.of_field {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Flat f :=
  inferInstance

end AlgebraicGeometry
