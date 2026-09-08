/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Finite products of proper schemes, and dense proper open subschemes

A finite product of proper `S`-schemes is proper over `S`
(`AlgebraicGeometry.isProper_pi_hom`). This is an instance of the general fact that the
structure morphism of a finite product in an over category satisfies any multiplicative
morphism property that is stable under base change.

An open subscheme `V ≤ W` of a scheme `Z` that is topologically dense in `W` and proper over a
base over which `W` is separated is all of `W`
(`AlgebraicGeometry.Scheme.Opens.eq_of_isProper_of_dense`): properness of a composite
`V ⟶ W ⟶ T` with `W ⟶ T` separated forces the inclusion `V ⟶ W` to be universally closed, so
`AlgebraicGeometry.Scheme.Opens.eq_of_universallyClosed_of_dense` applies.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The structure morphism of a finite product of proper `S`-schemes is proper. -/
theorem isProper_pi_hom {S : Scheme.{u}} {ι : Type*} [Finite ι] (F : ι → Over S)
    [HasProduct F] [∀ i, IsProper (F i).hom] : IsProper (∏ᶜ F).hom :=
  MorphismProperty.pi_hom _ F fun _ ↦ inferInstance

variable {Z T : Scheme.{u}}

/-- An open subscheme `V ≤ W` that is proper over a base `T` over which `W` is separated and
that is topologically dense in `W` is all of `W`. -/
theorem Scheme.Opens.eq_of_isProper_of_dense {V W : Z.Opens} (h : V ≤ W) (q : W.toScheme ⟶ T)
    [IsProper (Z.homOfLE h ≫ q)] [IsSeparated q]
    (hd : (W : Set Z) ⊆ closure (V : Set Z)) :
    V = W :=
  have : UniversallyClosed (Z.homOfLE h) :=
    UniversallyClosed.of_comp_of_isSeparated (f := Z.homOfLE h) (g := q)
  eq_of_universallyClosed_of_dense h hd

end AlgebraicGeometry
