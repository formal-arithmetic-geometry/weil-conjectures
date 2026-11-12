/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ContinuousSheafPi
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicHTopDegree
public import WeilConjectures.SixFunctors.ProEtale.Adic.SubfieldCohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.Adic.SubfieldSheafCohomologyLocalization

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

The finite stages are `ℤ/ℓᵐ`: by the trace isomorphism, `H^{2d}(X_proét, ℤ/ℓᵐ)` has `ℓᵐ`
elements (`AlgebraicGeometry.ProEtale.nat_card_finiteAdicH_two_mul`), and the Bockstein and
Milnor sequences give `H^{2d}(X_proét, ℤ_ℓ) ≅ ℤ_ℓ`
(`AlgebraicGeometry.ProEtale.nonempty_linearEquiv_integralAdicH_two_mul`). As `𝒪_E ≅ ℤ_ℓʳ` as
topological groups (`PadicAlgCl.exists_continuousAddEquiv_integers`) and cohomology commutes
with finite products, `H^{2d}(X_proét, 𝒪_{E,X}) ≅ ℤ_ℓʳ ≅ 𝒪_E`. Inverting `ℓ` gives the case of
`E` (`AlgebraicGeometry.ProEtale.nonempty_addEquiv_H_padicSubfieldSheaf_of_addEquiv`).

The isomorphisms obtained this way are not the trace maps: they depend on a choice of a
`ℤ_ℓ`-basis of `𝒪_E` and of generators. A pro-étale trace map, whose bijectivity would be the
blueprint statement proper, is not available in the repository.
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
`H^{2d}(X_proét, 𝒪_{E,X}) ≅ 𝒪_E(-d) ≅ 𝒪_E` as abelian groups.

The isomorphism is not the trace map, which is not available on pro-étale cohomology in the
repository; it is `H^{2d}(X_proét, 𝒪_{E,X}) ≅ H^{2d}(X_proét, ℤ_ℓ)ʳ ≅ ℤ_ℓʳ ≅ 𝒪_E` for a
`ℤ_ℓ`-basis of `𝒪_E` (see the module docstring). -/
theorem nonempty_addEquiv_H_padicIntegersSheaf_two_mul :
    letI := normedFieldOfAlgebra l E
    Nonempty (Sheaf.H (continuousMapAbSheaf X (integers l E)) (2 * d) ≃+ integers l E) := by
  let := normedFieldOfAlgebra l E
  have hl : (l : k) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime k
    (Fact.out : l.Prime) (Fact.out : ringChar k ≠ l)
  obtain ⟨r, ⟨e⟩⟩ := exists_continuousAddEquiv_integers l E
  obtain ⟨φ⟩ := nonempty_linearEquiv_integralAdicH_two_mul a d l hl
  exact ⟨(Sheaf.H.mapAddEquiv (continuousSheafMapIso X e) (2 * d)).trans <|
    (continuousSheafPiHAddEquiv X (2 * d)).trans <|
      (AddEquiv.piCongrRight fun _ ↦ φ.toAddEquiv).trans e.toAddEquiv.symm⟩

/-- Blueprint `theorem-trace-isomorphism-top-degree--7` (the trace isomorphism with coefficients
in a finite extension `E` of `ℚ_ℓ`), in existential form: for `X` smooth, proper and
geometrically connected of pure dimension `d` over the algebraically closed `k` and `ℓ`
invertible in `k`, `H^{2d}(X_proét, E_X) ≅ E(-d) ≅ E` as abelian groups.

As `E_X = 𝒪_{E,X}[1/ℓ]`, this is the localization at `ℓ` of
`AlgebraicGeometry.ProEtale.nonempty_addEquiv_H_padicIntegersSheaf_two_mul`. The isomorphism is
not the trace map, which is not available on pro-étale cohomology in the repository. -/
theorem nonempty_addEquiv_H_padicSubfieldSheaf_two_mul :
    letI := normedFieldOfAlgebra l E
    Nonempty (Sheaf.H (continuousMapAbSheaf X E) (2 * d) ≃+ E) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated a
  obtain ⟨ψ⟩ := nonempty_addEquiv_H_padicIntegersSheaf_two_mul a d l E
  exact nonempty_addEquiv_H_padicSubfieldSheaf_of_addEquiv X l E (2 * d) ψ

end AlgebraicGeometry.ProEtale
