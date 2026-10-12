/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Constructibility of finite pushforward of open quotient constants

Source: normalization exact-sequence blueprint, unit `sk-thm-p1`.
(blueprint: lem-weil-pbc-finite-pushforward-open-quotient-constant)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Finite pushforward of an extension-by-zero finite quotient constant is constructible.

Source: normalization exact-sequence blueprint,
`sec-proper-base-change/sk-thm-p1/lemma-weil-pbc-normalization-exact-sequence.md`,
constructibility of the middle term.
(blueprint: lem-weil-pbc-finite-pushforward-open-quotient-constant)

Proof: Y is Noetherian, since it is finite over X. Write R = Λ/(ℓ). Its constant sheaf
is finite locally constant, because R is cyclic as a Λ-module. Extend its stratification
by the closed complement of the quasi-compact open j to obtain constructibility of j_!R.
Its underlying abelian sheaf has finite constructible stalks. Finite direct image preserves
this constructibility by finite base change, the finite geometric-fibre formula and
Noetherian induction. Extension by zero and finite direct image preserve annihilation by ℓ,
so the module action factors through the finite ring R. Refine the finite-set trivializations
on every stratum to trivialize the finitely many R-operations. These give constant finite
R-module values, finitely generated over Λ, and hence the required module stratification.
Neither finiteness nor Noetherianity of Λ is needed. Empty opens and the zero quotient
produce zero sheaves, which satisfy the same conclusion. -/
theorem finite_pushforward_open_constantModSheaf_constructible
    {X Y U : Scheme.{u}} [IsNoetherian X] (ν : Y ⟶ X) [IsFinite ν]
    (j : U ⟶ Y) [IsOpenImmersion j] (ℓ : ℕ)
    [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})] :
    Scheme.IsConstructibleSheaf ((ν)_*[ModuleCat.{u + 1} Λ].obj
      ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ))) := by
  sorry
end AlgebraicGeometry
