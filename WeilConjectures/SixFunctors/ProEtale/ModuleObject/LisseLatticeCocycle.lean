/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.RegularLattice
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TransitionCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LisseLatticeBasis

/-!
# Integral changes of trivialisation on regular schemes

Let `S` be a regular Noetherian scheme, `{f_k : V_k ⟶ S}` a finite pro-étale cover by affine
schemes and `T_{jk}(a, b)(x) ∈ GL_n(E)` a system of transition values: continuous in the point
`x` of a scheme `W` with `a : W ⟶ V_j`, `b : W ⟶ V_k` over `S`, compatible with precomposition
and satisfying the cocycle condition (the values of the transition matrices of a trivialisation,
`AlgebraicGeometry.ProEtale.exists_transitionValues`). Then there are continuous
`g_k : V_k → GL_n(E)` such that the conjugates `g_j(p₁ w)⁻¹ T_{jk}(p₁, p₂)(w) g_k(p₂ w)` on the
fibre products `V_j ×_S V_k` and their inverses have integral entries
(`AlgebraicGeometry.exists_integral_conj_of_transitionValues`).

The proof: on the single cover `F : ∐ V_k ⟶ S`, the transition values define a continuous
cocycle `γ : (∐ V_k) ×_S (∐ V_k) → GL_n(E)`, a point of the fibre product being the image of a
point of a scheme `R` with `a : R ⟶ V_j`, `b : R ⟶ V_k`; it acts on the lattices of `Eⁿ` by a
descent cocycle. By the lattice theorem on regular schemes
(`AlgebraicGeometry.exists_isTwistedSection_compactOpenLattice`, blueprint
`sk-lem-stratified-lattice`), it has a lattice-valued twisted section `σ`; the bases `g` of the
`𝒪_E`-spans of the lattices `σ` (`PadicAlgCl.CompactOpenLattice.integersBasisGL`) are locally
constant and conjugate `γ` into `GL_n(𝒪_E)`
(`PadicAlgCl.CompactOpenLattice.norm_integersBasisGL_inv_mul_mul_le_one`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {E : IntermediateField ℚ_[l] (PadicAlgCl l)}
  [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry
