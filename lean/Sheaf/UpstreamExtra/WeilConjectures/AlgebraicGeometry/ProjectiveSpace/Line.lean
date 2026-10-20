module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line

/-! Declarations of ours that lived in the upstream file
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line` (moved out by the scheduled sync,
tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-!
# The affine and projective lines

Over a scheme `S`, the projective line `ℙ¹_S = ProjectiveLine S` is covered by two copies of the
affine line `𝔸¹_S = 𝔸(PUnit; S)`: the affine chart `t ↦ [t : 1]` of
`AlgebraicGeometry.ProjectiveLine.affineChart` and the chart at infinity `z ↦ [1 : z]`. This
file shows that `ℙ¹_S` is glued from them along `t = z⁻¹`, that the complement of the affine
chart is the point `∞ = [1 : 0]`, and how the `q`-power Frobenius of `ℙ¹_F` acts on the charts
over a finite field `F` with `q` elements.

## Main definitions

- `AlgebraicGeometry.ProjectiveLine.infinityChart`: the chart at infinity `𝔸¹_S ↪ ℙ¹_S`,
  `z ↦ [1 : z]`, onto `D₊(T₀)`.
- `AlgebraicGeometry.ProjectiveLine.infinity`: the point at infinity `∞ : S ⟶ ℙ¹_S`, the section
  `z = 0` of the chart at infinity.

## Main results

- `AlgebraicGeometry.ProjectiveLine.isPullback_affineChart_infinityChart`: the two charts
  intersect in the locus `t ≠ 0` of the affine chart, which the chart at infinity sees through
  `z = t⁻¹`.
- `AlgebraicGeometry.ProjectiveLine.opensRange_affineChart_sup_opensRange_infinityChart`: the two
  charts cover `ℙ¹_S`.
- `AlgebraicGeometry.ProjectiveLine.range_infinity`: the complement of the affine chart is the
  image of `∞`; over a field it is a single point
  (`AlgebraicGeometry.ProjectiveLine.compl_opensRange_affineChart_eq_singleton`).
- `AlgebraicGeometry.ProjectiveLine.affineChart_comp_eq_of_isFrobenius`,
  `AlgebraicGeometry.ProjectiveLine.infinityChart_comp_eq_of_isFrobenius`: the `q`-power
  Frobenius acts by `t ↦ t ^ q` and `z ↦ z ^ q` on the charts `Spec F[t]` and `Spec F[z]`.

## Blueprint

Together with `AlgebraicGeometry.ProjectiveLine.affineChart` and `AlgebraicGeometry.affineLine`,
this file implements the remark `d-lines` of the blueprint subsection `sk-d-lines`. The
blueprint defines `ℙ¹_F` by gluing `Spec F[t]` and `Spec F[z]` along `F[t, t⁻¹] = F[z, z⁻¹]`;
here `ℙ¹_F` is defined as `ℙ(ULift (Fin 2); Spec F)`, and the gluing description is the theorem
`isPullback_affineChart_infinityChart` together with the covering statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

variable {X S : Scheme.{u}}

instance Line_isIso : IsIso (AffineSpace.reindex (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦
    PUnit.unit.{u + 1}) S) := by
  -- Reuse the upstream isomorphism instance for this exact map over the arbitrary base S.
  infer_instance

end AlgebraicGeometry.ProjectiveLine
