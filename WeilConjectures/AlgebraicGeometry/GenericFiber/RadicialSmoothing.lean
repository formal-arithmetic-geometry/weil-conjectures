/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# A smooth dense open after a finite radicial base change

Let `S` be integral of finite type over a field and `f : X ⟶ S` of finite type. After shrinking
`S` to a nonempty open `U` and making a finite, surjective, radicial base change `S' ⟶ U`, the
reduction of `X_{S'}` has a dense open `V` which is smooth over `S'`, and on which a given
constructible sheaf on `X` becomes finite locally constant. In characteristic zero no base
change is needed (generic smoothness); in characteristic `p` one passes to a finite purely
inseparable extension of the function field of `S`. This is the third step of Deligne's
generic constructibility theorem (`thm-fin-deligne-generic-open`).

## Main statements

- `AlgebraicGeometry.exists_isFinite_universallyInjective_smooth_dense`
  (`lem-fin-generic-radicial-smoothing`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- Blueprint `lem-fin-generic-radicial-smoothing`: A smooth dense open after a finite radicial
base change.

Let `S` be integral of finite type over a field `k` and let `f : X ⟶ S` be of finite type with
`X` nonempty. Then there are a nonempty open `U ⊆ S` and a finite, surjective, radicial
(universally injective) `π : S' ⟶ U`, with base change `f' : X' ⟶ S'` of `f` over `U`, and an
immersion `v : V ⟶ X'` from a reduced scheme, with open dense image (so that `V` is a dense open
of `(X')_red`), such that `V` is smooth over `S'`. For a given constructible sheaf `F` on `X`,
one may require the pullback of `F` to `V` to be finite locally constant.

Moreover, every point `x` of the generic fibre of `f'` outside `V` is a proper specialization of
a point of `V` in the generic fibre: in the generic fibre, the closure of `x` is a proper closed
subset of the irreducible closed subset of `X'` containing it, so that (the generic fibre being
of finite type over a field) every component of the complement of `V` in the generic fibre has
dimension strictly smaller than the component of `X'` containing it. -/
theorem exists_isFinite_universallyInjective_smooth_dense {k : Type u} [Field k]
    {S X : Scheme.{u}} [IsIntegral S] (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS]
    [QuasiCompact aS] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [Nonempty X]
    (Λ : Type (u + 1)) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    ∃ (U : S.Opens) (S' : Scheme.{u}) (π : S' ⟶ U) (X' : Scheme.{u}) (q : X' ⟶ f ⁻¹ᵁ U)
      (f' : X' ⟶ S') (V : Scheme.{u}) (v : V ⟶ X'),
      (U : Set S).Nonempty ∧ IsFinite π ∧ Surjective π ∧ UniversallyInjective π ∧
      IsPullback q f' (f ∣_ U) π ∧ IsImmersion v ∧ IsReduced V ∧ IsOpen (Set.range v) ∧
      Dense (Set.range v) ∧ Smooth (v ≫ f') ∧
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (v ≫ q ≫ (f ⁻¹ᵁ U).ι)).obj F) ∧
      ∀ x : X', IsGenericPoint (f' x) Set.univ → x ∉ Set.range v →
        ∃ y ∈ Set.range v, IsGenericPoint (f' y) Set.univ ∧ y ⤳ x ∧ y ≠ x :=
  sorry

end AlgebraicGeometry
