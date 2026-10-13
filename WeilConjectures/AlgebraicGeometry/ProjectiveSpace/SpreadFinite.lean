/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Spreading out finite algebras from the generic fibre

Let `A` be a Noetherian domain with fraction field `K` and `T ⟶ Spec A` projective. A finite
morphism `Y₀ ⟶ T_K` to the generic fibre, i.e. a finite coherent `𝒪_{T_K}`-algebra, is the
generic fibre of a finite morphism `Y ⟶ T_U` over a nonempty open `U` of `Spec A`; finitely many
of them (the factors of a finite product decomposition) can be spread out simultaneously
(`lem-fin-spread-finite-algebra`).

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.exists_isFinite_spread`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

/-- Blueprint `lem-fin-spread-finite-algebra`: Spreading a finite algebra from the generic
fibre.

Let `A` be a Noetherian domain with fraction field `K`, `η : Spec K ⟶ Spec A` the generic point,
and `f : T ⟶ Spec A` projective (`f = π ∘ i` for a closed immersion `i : T ⟶ ℙ(n; Spec A)`).
Let `gₐ : Y₀ₐ ⟶ T_K = T ×_{Spec A} Spec K`, for `a` in a finite type `ι`, be finite morphisms
(the factors of a finite product decomposition of a finite coherent `𝒪_{T_K}`-algebra). There is
a nonempty open `U` of `Spec A` and finite morphisms `g'ₐ : Yₐ ⟶ f⁻¹(U)` whose base changes
along `T_K ⟶ T` are the `gₐ`. -/
theorem exists_isFinite_spread {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A)) {n : Type u} [Finite n]
    (i : T ⟶ ℙ(n; Spec (.of A))) [IsClosedImmersion i]
    (hi : i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A) = f) {ι : Type u} [Finite ι]
    (Y₀ : ι → Scheme.{u})
    (g : ∀ a, Y₀ a ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))))
    [∀ a, IsFinite (g a)] :
    ∃ (U : (Spec (.of A)).Opens) (_ : U ≠ ⊥) (Y : ι → Scheme.{u})
      (g' : ∀ a, Y a ⟶ (f ⁻¹ᵁ U).toScheme) (_ : ∀ a, IsFinite (g' a))
      (e : ∀ a, Y₀ a ≅ pullback (g' a ≫ (f ⁻¹ᵁ U).ι)
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))))),
      ∀ a, (e a).hom ≫ pullback.snd _ _ = g a := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
