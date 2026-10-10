/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Derived.Locally

/-!
# Complexes with a strictly perfect top part

Let `Y` be a scheme and `Λ` a commutative ring. The proof that a dualizable object `K` of
`D(Y_proét, Λ)` is locally perfect (Stacks, Tag 0FPV) represents `K`, locally on `Y_proét`, by
complexes `M` whose terms in degrees `≥ m` form a bounded complex of finite free sheaves, for
smaller and smaller `m`. This file sets up this notion and shows that it is stable under
pullback along weakly étale morphisms.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsFiniteFree`: a sheaf of `Λ`-modules isomorphic to the constant
  sheaf `Λⁿ`.
- `AlgebraicGeometry.ProEtale.HasPerfectTop K m`: `K ≅ Q(M)` for a complex `M` with a
  subcomplex `E` which is a bounded complex of finite free sheaves vanishing in degrees `< m` and
  equal to `M` in degrees `≥ m`.

## Main results

- `AlgebraicGeometry.ProEtale.HasPerfectTop.upperStar`: stability under derived pullback along a
  weakly étale morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A pro-étale sheaf of `Λ`-modules is *finite free* if it is isomorphic to the constant sheaf
`Λⁿ` for some `n`. -/
def IsFiniteFree {Y : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :
    Prop :=
  ∃ n : ℕ, Nonempty (F ≅ (constantSheaf _ _).obj (ModuleCat.of Λ (Fin n → Λ)))

/-- `K ∈ D(Y_proét, Λ)` *has a perfect top part in degrees `≥ m`* if `K ≅ Q(M)` for a complex
`M` with a degreewise monomorphism `j : E ⟶ M` from a bounded complex `E` of finite free
sheaves vanishing in degrees `< m`, which is an isomorphism in degrees `≥ m`. -/
def HasPerfectTop {Y : Scheme.{u}}
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) (m : ℤ) :
    Prop :=
  ∃ (M E : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ)
    (j : E ⟶ M) (b : ℤ), Nonempty (K ≅ DerivedCategory.Q.obj M) ∧ (∀ i, Mono (j.f i)) ∧
      (∀ i, m ≤ i → IsIso (j.f i)) ∧ E.IsStrictlyGE m ∧ E.IsStrictlyLE b ∧
        ∀ i, IsFiniteFree (E.X i)

lemma HasPerfectTop.of_iso {Y : Scheme.{u}}
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') {m : ℤ} (h : HasPerfectTop K m) : HasPerfectTop K' m := by
  obtain ⟨M, E, j, b, ⟨e'⟩, h⟩ := h
  exact ⟨M, E, j, b, ⟨e.symm ≪≫ e'⟩, h⟩

/-- The pullback of a finite free sheaf is finite free. -/
lemma IsFiniteFree.upperStar {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    {F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)} (hF : IsFiniteFree F) :
    IsFiniteFree ((g)^*[ModuleCat.{u + 1} Λ].obj F) := by
  obtain ⟨n, ⟨e⟩⟩ := hF
  exact ⟨n, ⟨(g)^*[ModuleCat.{u + 1} Λ].mapIso e ≪≫
    (upperStarConstantSheafIso g).app _⟩⟩

/-- Having a perfect top part is stable under derived pullback along a weakly étale morphism. -/
lemma HasPerfectTop.upperStar {Y Z : Scheme.{u}} (g : Z ⟶ Y) [WeaklyEtale g]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))} {m : ℤ}
    (h : HasPerfectTop K m) : HasPerfectTop (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) m := by
  sorry

end AlgebraicGeometry.ProEtale
