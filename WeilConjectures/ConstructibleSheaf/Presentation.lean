/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Defs

/-!
# Constructible sheaves are quotients of sums of `j_{V!} Λ_V`

On a quasi-compact quasi-separated scheme `X` and for a finite ring `Λ`, every constructible
sheaf of `Λ`-modules on `X_ét` is a quotient of a finite coproduct `∐ j_{V!} Λ_V` of extensions
by zero of constant sheaves along étale maps `j_V : V ⟶ X` from affine schemes [Stacks 095M;
SGA 4½, Rapport, 4.6].

## Main statements

- `AlgebraicGeometry.Scheme.exists_epi_sigma_lowerShriek_constantSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]

/-- **Constructible sheaves are quotients of sums of `j_{V!} Λ_V`** [Stacks 095M; SGA 4½,
Rapport, 4.6]. This is an input to blueprint `sk-lem-sf-flat-model`.

On a quasi-compact quasi-separated scheme `X` and for a finite ring `Λ`, every constructible
sheaf `F` of `Λ`-modules on `X_ét` is a quotient of a finite coproduct `∐ j_{V!} Λ_V`, with
`j_V : V ⟶ X` étale and `V` affine. Choosing each `V` to map into an affine open of `X` makes
`j_V` separated of finite type, hence compactifiable. Each `j_{V!} Λ_V` is flat and, as `Λ` is
finite, constructible. -/
theorem exists_epi_sigma_lowerShriek_constantSheaf [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ (n : ℕ) (V : Fin n → Scheme.{u}) (j : ∀ i, V i ⟶ X),
      (∀ i, Etale (j i) ∧ IsAffine (V i)) ∧
      ∃ (_ : ∀ i, HasCompactification (j i))
        (φ : (∐ fun i ↦ (Etale.lowerShriek (ModuleCat.{u + 1} Λ) (j i)).obj
          ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))) ⟶ F), Epi φ :=
  sorry

end AlgebraicGeometry.Scheme
