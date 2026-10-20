module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! Declarations of ours that lived in the upstream file
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts` (moved out by the scheduled sync,
tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# The standard affine charts of projective space

The standard open `D₊(Tᵢ)` of `ℙ(n; S)` is the affine space `𝔸({j : n // j ≠ i}; S)` over `S`,
with the affine coordinates given by the quotients `Tⱼ / Tᵢ`.

Over the integral model, this is `AlgebraicGeometry.Proj.basicOpenIsoSpec` combined with
`MvPolynomial.homogeneousLocalizationAwayXEquiv`, which identifies the degree-zero part of
`ℤ[T]_{Tᵢ}` with the polynomial ring `ℤ[Yⱼ : j ≠ i]`. Since `ℙ(n; S)` and `𝔸(m; S)` are both
defined as base changes of their integral models along `S ⟶ Spec ℤ`, and `D₊(Tᵢ) ⊆ ℙ(n; S)`
is the preimage of `D₊(Tᵢ) ⊆ ℙⁿ_ℤ`, the chart over `S` is obtained by base change.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.standardOpenIso` — the isomorphism of `S`-schemes
  `D₊(Tᵢ) ≅ 𝔸({j : n // j ≠ i}; S)`.
- `AlgebraicGeometry.ProjectiveLine.affineChart` — the standard chart `𝔸¹_S ↪ ℙ¹_S`,
  `x ↦ [x : 1]`, an open immersion of `S`-schemes onto `D₊(T₁)`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.standardOpenIso_hom_over` — the chart isomorphism is a
  morphism over `S`.
- `AlgebraicGeometry.ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom` — the
  computation rule: for `g : X ⟶ S` and sections `s : n → Γ(X, ⊤)` generating the unit ideal,
  the morphism `X_{s i} ⟶ 𝔸({j // j ≠ i}; S)` obtained by restricting `homOfSections g s hs`
  and applying the chart isomorphism is `AffineSpace.homOfVector` for the vector of
  quotients `s j / s i`.

## Implementation notes

`MvPolynomial.homogeneousLocalizationAwayXEquiv` takes a `DecidableEq` instance on the index
type, which the chart isomorphism should not carry around. Since everything here is
noncomputable anyway, `Classical.decEq` is enabled as a local instance, so that a single
instance is used throughout the file and none appears in any statement.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

variable (S : Scheme.{u})

/-- Reindexing the single coordinate of the standard affine chart is an isomorphism.
The upstream Charts module supplies the instance used in this compatibility declaration.
-/
instance Charts_isIso : IsIso (AffineSpace.reindex (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨1⟩} ↦
    PUnit.unit.{u + 1}) S) := by
  infer_instance

end AlgebraicGeometry.ProjectiveLine
