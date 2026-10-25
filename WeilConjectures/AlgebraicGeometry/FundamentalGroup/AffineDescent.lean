/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.AffineCoaction

/-!
# Notation for coactions in affine descent

Let `p : W ⟶ S` and `v : V ⟶ W` be morphisms of schemes. A *coaction* on `V` relative to `W/S`
is a morphism `γ : V ×_S W ⟶ V` over `W` (i.e. `γ ≫ v = pr₂`) which is counital
(`γ (x, v x) = x`) and coassociative (`γ (γ (x, w₁), w₂) = γ (x, w₂)`). This file names the
schemes and morphisms entering these identities, without any hypothesis on `p` and `v`. For flat
`p` between affine schemes and `V` affine every coaction is effective
(`AlgebraicGeometry.exists_isPullback_of_coaction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace AffineCoaction

variable {S W V : Scheme.{u}} (p : W ⟶ S) (v : V ⟶ W)

/-- `P = V ×_S W`. -/
noncomputable abbrev P : Scheme.{u} := pullback (v ≫ p) p

/-- `P₂ = V ×_S W ×_S W`. -/
noncomputable abbrev P₂ : Scheme.{u} := pullback (pullback.snd (v ≫ p) p ≫ p) p

/-- The diagonal `V ⟶ V ×_S W`, `x ↦ (x, v x)`. -/
noncomputable abbrev d : V ⟶ P p v := pullback.lift (𝟙 _) v (by simp)

/-- The projection `V ×_S W ×_S W ⟶ V ×_S W` forgetting the middle factor. -/
noncomputable abbrev π₁ : P₂ p v ⟶ P p v :=
  pullback.map _ _ _ _ (pullback.fst (v ≫ p) p) (𝟙 W) (𝟙 S) (by simp [pullback.condition])
    (by simp)

/-- The map `V ×_S W ×_S W ⟶ V ×_S W` applying `γ` to the first two factors. -/
noncomputable abbrev γ₁ (γ : P p v ⟶ V) (hγ : γ ≫ v = pullback.snd (v ≫ p) p) : P₂ p v ⟶ P p v :=
  pullback.map _ _ _ _ γ (𝟙 W) (𝟙 S) (by simp [reassoc_of% hγ]) (by simp)

end AffineCoaction

end AlgebraicGeometry
