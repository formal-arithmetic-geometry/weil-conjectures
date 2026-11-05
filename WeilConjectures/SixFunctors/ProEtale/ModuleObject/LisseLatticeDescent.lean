/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeValues

/-!
# Descent of lisse `E`-sheaves to `𝒪_E` from integral transition values

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`, `S` a scheme and `L` a module object over `E_S`
trivialised, `e_k : E_{V_k}ⁿ ≅ f_k^* L`, on a finite pro-étale cover `{f_k : V_k ⟶ S}`. For
`a : W ⟶ V_j` and `b : W ⟶ V_k` with `a ≫ f_j = b ≫ f_k`, the transition morphism from the
pullback of `e_k` to the pullback of `e_j` is a matrix of continuous functions `W → E`; its values
are invertible matrices `T_{jk}(a, b)(x) ∈ GL_n(E)`
(`AlgebraicGeometry.ProEtale.exists_transitionValues`). They

* are continuous in `x`, together with their inverses;
* are compatible with precomposition: `T_{jk}(c ≫ a, c ≫ b)(x) = T_{jk}(a, b)(c x)`;
* satisfy the cocycle condition `T_{jl}(a, c) = T_{jk}(a, b) T_{kl}(b, c)` and `T_{kk}(a, a) = 1`.

If `g_k : V_k → GL_n(E)` are continuous and the conjugates `g_j(p₁ w)⁻¹ T_{jk}(p₁, p₂)(w) g_k(p₂ w)`
on the fibre products `V_j ×_S V_k` and their inverses have integral entries, then `L` descends
to a locally free `𝒪_{E,S}`-module: the trivialisations changed by the `g_k` have transition
matrices with entries in `𝒪_E`, and the descent of
`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_isDefinedOver` applies.

We also show that trivialisations of a locally free `E_S`-module over overlapping charts have the
same rank (`AlgebraicGeometry.ProEtale.rank_eq_of_comp_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

end AlgebraicGeometry.ProEtale
