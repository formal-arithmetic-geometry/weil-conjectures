/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier

/-!
# The dual of an Artin–Schreier sheaf

The dual of the Artin–Schreier sheaf `ℒ_{ψ(a x)}` on the affine line is the Artin–Schreier
sheaf `ℒ_{ψ⁻¹(a x)}` of the inverse character
(`AlgebraicGeometry.nonempty_iso_dual_artinSchreier`): this is the clause
`(ℒ_{ψ,f})^{-1} ≅ ℒ_{ψ,-f} ≅ ℒ_{ψ^{-1},f}` of the isotypic decomposition of the Artin–Schreier
pushforward, for `f = a x`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The dual of an Artin–Schreier sheaf.** The dual of the linear Artin–Schreier sheaf
`ℒ_{ψ(a x)}` on `𝔸¹_{k₀}` is the Artin–Schreier sheaf `ℒ_{ψ⁻¹(a x)}`: this is the clause
`(ℒ_{ψ,f})^{-1} ≅ ℒ_{ψ,-f} ≅ ℒ_{ψ^{-1},f}` for `f = a x`, the inverse of the rank-one sheaf
`ℒ_{ψ,f}` being its dual. (blueprint: `lem-fd-as-characters`, subsection
`sk-lem-as-properties` of `sec-fourier-transform`) -/
theorem nonempty_iso_dual_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    Nonempty ((artinSchreier ψ a).dual (isLisse_artinSchreier ψ a) ≅ artinSchreier ψ⁻¹ a) :=
  sorry

end AlgebraicGeometry
