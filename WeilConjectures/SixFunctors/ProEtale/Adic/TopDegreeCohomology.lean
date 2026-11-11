/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.Adic.SubfieldCohomologicalDimension

/-!
# Top-degree cohomology with coefficients `𝒪_E` and `E`

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k`, `E ⊆ ℚ̄_ℓ` a finite
extension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `X` smooth, proper and geometrically connected
of pure dimension `d` over `k`. The trace maps `H^{2d}(X, 𝒪_{E,X}) ⟶ 𝒪_E(-d)` and
`H^{2d}(X, E_X) ⟶ E(-d)` of the blueprint are isomorphisms. The repository has trace maps only
at the finite étale stage (`AlgebraicGeometry.Etale.TateOrientation.traceMap`) and no
`𝒪_E`- or `E`-module structure on the pro-étale cohomology `Hᵠ(X_proét, -)` of abelian sheaves,
so the statements are the existence of additive isomorphisms
`H^{2d}(X_proét, 𝒪_{E,X}) ≅ 𝒪_E` and `H^{2d}(X_proét, E_X) ≅ E` (the twists being trivial over
the algebraically closed `k`).

## Main statements

- `AlgebraicGeometry.ProEtale.nonempty_addEquiv_H_padicIntegersSheaf_two_mul`
  (blueprint `theorem-trace-isomorphism-top-degree--5`).
- `AlgebraicGeometry.ProEtale.nonempty_addEquiv_H_padicSubfieldSheaf_two_mul`
  (blueprint `theorem-trace-isomorphism-top-degree--7`).

## Implementation notes

Both statements are left with `sorry`. The blueprint proof passes from the finite stages
`𝒪_E/ϖⁿ`, where the trace isomorphism is
`Etale.TateOrientation.bijective_untwistedTraceMap_comp_cohomologyAddEquivCompactSupport`,
to `𝒪_E` by the Milnor sequence, and to `E` by inverting `ℓ`. This needs the comparison of the
pro-étale cohomology of the constant sheaves `𝒪_E/ϖⁿ` with the étale cohomology groups
`Hom(Λ_X, Λ_X[2d])` of `D(X_ét, Λ)` used at the finite stage, which is not available in this
form.
-/

@[expose] public section

universe u

open CategoryTheory PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (d : ℕ)
  [IsProper a] [SmoothOfRelativeDimension d a] [GeometricallyConnected a] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k ≠ l)] (E : Type) [Field E] [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
  [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

include a

/-- Blueprint `theorem-trace-isomorphism-top-degree--5` (the trace isomorphism with integral
coefficients), in existential form: for `X` smooth, proper and geometrically connected of pure
dimension `d` over the algebraically closed `k` and `ℓ` invertible in `k`,
`H^{2d}(X_proét, 𝒪_{E,X}) ≅ 𝒪_E(-d) ≅ 𝒪_E` as abelian groups. Not proved here (see the module
docstring). -/
theorem nonempty_addEquiv_H_padicIntegersSheaf_two_mul :
    letI := normedFieldOfAlgebra l E
    Nonempty (Sheaf.H (continuousMapAbSheaf X (integers l E)) (2 * d) ≃+ integers l E) := by
  sorry

/-- Blueprint `theorem-trace-isomorphism-top-degree--7` (the trace isomorphism with coefficients
in a finite extension `E` of `ℚ_ℓ`), in existential form: for `X` smooth, proper and
geometrically connected of pure dimension `d` over the algebraically closed `k` and `ℓ`
invertible in `k`, `H^{2d}(X_proét, E_X) ≅ E(-d) ≅ E` as abelian groups. Not proved here (see
the module docstring). -/
theorem nonempty_addEquiv_H_padicSubfieldSheaf_two_mul :
    letI := normedFieldOfAlgebra l E
    Nonempty (Sheaf.H (continuousMapAbSheaf X E) (2 * d) ≃+ E) := by
  sorry

end AlgebraicGeometry.ProEtale
