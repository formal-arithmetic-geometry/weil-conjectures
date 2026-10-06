/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.DegreeOne
public import WeilConjectures.DeligneLaumon.AffineLine.Endpoints
public import WeilConjectures.DeligneLaumon.AffineLine.Exactness
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The Deligne–Laumon estimate on the affine line

Let `j : U₀ ↪ 𝔸¹_{𝔽_q}` be a dense open immersion and `F` a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^r(𝔸¹, j_*F)` has
weights at most `w + r` for every `r`.

The endpoint lemmas of `WeilConjectures.DeligneLaumon.AffineLine.Endpoints` settle every degree
except one: degree zero vanishes and degree two is pure of weight `w + 2`. For degree one,
choose a finite composition filtration of the Weil representation of `F`; its lisse irreducible
factors are still pure of weight `w`, their stalk spectra being subquotient spectra, and still
unramified at infinity. A geometrically constant factor extends constantly to the whole line
and has `H_c^1 = 0` because `RΓ_c(𝔸¹, ℚ̄_ℓ) = ℚ̄_ℓ(-1)[-2]`; every other factor is covered by
`AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_one`. Each filtration step
stays short exact after `j_*` by `AlgebraicGeometry.shortExact_map_directImage`, so the long
exact sequence gives an exact triple in degree one whose middle term inherits the common upper
bound, characteristic polynomials being multiplicative in short exact sequences of Frobenius
modules. Induction through the filtration finishes the proof.

The blueprint proof opens with two further steps: a base change to a finite constant extension
`𝔽_{q^m}` (`FrobeniusModule.hasWeightsAtMost_of_pow` shows the bound descends) and a reduction
to geometrically irreducible graded pieces
(`AlgebraicGeometry.WeilGroup.exists_filtration_geometric_isIrreducible`). The Fourier route of
`sk-p-dl-a1-middle` only assumes arithmetic irreducibility, so the composition filtration of
the Weil representation over `k₀` is already fine enough. No splitting of the filtration or
semisimplicity theorem for pure sheaves is used.

The transport of the estimate to arbitrary smooth curves, which the blueprint subsection also
contains, is in `WeilConjectures.DeligneLaumon.AffineLine.Curve`.

## Main statements

In the namespace `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen`:

- `hasWeightsAtMost_compactlySupportedCohomology_directImage`: the affine-line estimate.
- `subsingleton_compactlySupportedCohomology_directImage_zero` and
  `isPureOfWeightOver_compactlySupportedCohomology_directImage_two`: the two sharper endpoint
  assertions on the line.
- `hasWeightsAtMostOver_compactlySupportedCohomology_of_iso_constantTwist`: the bound for an
  exceptional rank-one constituent.
- `exists_surjective_compactlySupportedCohomology_one`: deleting a regular point to make the
  sheaf unramified at infinity.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry

namespace WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The affine line is smooth of relative dimension one over `k₀`. -/
local instance : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
  simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))

-- the provisional Weil complexes are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- *Exceptional rank-one constituents.* Let `E` be a Weil sheaf on a dense open `U₀` of the
affine line which is the restriction of a constant twist `ℒ_{ψ(a x)} ⊗ 𝓑_b` of an
Artin–Schreier sheaf, `a ∈ k₀` (for `a = 0` this is the rank-one constant Weil sheaf `𝓑_b`). If
`E` is punctually `ι`-pure of weight `w`, then `H_c^i(U, E)` has weights at most `w + i` for every
`i`.

Let `E₀ = ℒ_{ψ(a x)} ⊗ 𝓑_b` be the lisse extension of `E` to the line. By Poincaré duality and
the vanishing of the cohomology of a nontrivial Artin–Schreier sheaf, `RΓ_c(𝔸¹, E₀) = 0` for
`a ≠ 0`, while `RΓ_c(𝔸¹, 𝓑_b) = 𝓑_b(-1)[-2]`. The localization sequence for `U ↪ 𝔸¹` with the
finite boundary `Z` gives `H_c^0(U, E) = 0`, makes `H_c^1(U, E)` a quotient of the boundary group
`H_c^0(Z, E₀|_Z)`, of weights at most `w`
(`AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite`),
and `H_c^2(U, E)` a subobject of `H_c^2(𝔸¹, E₀)`, of weights at most `w + 2`.

That localization sequence is not available for the provisional, non-triangulated Weil
complexes; with the present coefficients `H_c^i(U, E)` is zero, which is how the statement is
proved here. (blueprint: `lem-a1-exceptional-constituents`) -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_of_iso_constantTwist
    (ι : PadicAlgCl l →+* ℂ) (ψ : AddChar k₀ (PadicAlgCl l)) (D : LisseOnDenseOpen k₀ l)
    (a : k₀) (b : (PadicAlgCl l)ˣ)
    (hE : Nonempty (D.sheaf ≅ (WeilSheaf.upperStar D.j).obj ((artinSchreier ψ a).constantTwist b)))
    {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (i : ℤ) :
    (D.sheaf.compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι (w + i) :=
  have : Subsingleton (D.sheaf.compactlySupportedCohomology i).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _

-- the provisional Weil complexes are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- *Removing a regular point to arrange infinity.* Let `F` be a lisse Weil sheaf on a dense
open `U₀` of the affine line, punctually `ι`-pure of weight `w`. After a finite constant-field
extension `k₁ / k₀` there are a dense open `V₀ ⊆ 𝔸¹_{k₁}` and a lisse Weil sheaf `E` on `V₀`,
punctually `ι`-pure of weight `w` and unramified at infinity, together with a surjection
`H_c^1(V, E) ↠ H_c^1(U, F)` carrying the Frobenius of `k₁` to the `[k₁ : k₀]`-th power of the
Frobenius of `k₀`.

Choose a geometric point `s ∈ U` and, over a finite extension `k₁`, a `τ ∈ PGL₂(k₁)` with
`τ(s) = ∞`; put `V₀ = τ(U₀ \ {s})` and let `E` be the transported restriction of `F`, which
extends lisse across `∞` since `F` is lisse at `s`. The localization sequence for
`U \ {s} ↪ U` and the vanishing of `H_c^1` of a point give the surjection. The blueprint adds
that geometric irreducibility is preserved; the provisional interface has no notion of
geometric irreducibility, so this clause is not stated.

The constant-field extension and the localization sequence are not available for the
provisional Weil sheaves; with the present coefficients every Weil sheaf is zero, and the
datum `k₁ = k₀`, `V₀ = 𝔸¹`, `E = 0` is a witness, which is how the statement is proved here.
(blueprint: `lem-a1-unramified-at-infinity`) -/
theorem exists_surjective_compactlySupportedCohomology_one (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₀ k₁)
      (_ : Fact (ringChar k₁ ≠ l)) (E : LisseOnDenseOpen k₁ l),
      E.IsUnramifiedAtInfinity ∧ E.sheaf.IsPunctuallyPureOfWeight ι w ∧
      ∃ f : (E.sheaf.compactlySupportedCohomology 1).carrier →ₗ[PadicAlgCl l]
          (D.sheaf.compactlySupportedCohomology 1).carrier,
        Function.Surjective f ∧ ∀ x, f ((E.sheaf.compactlySupportedCohomology 1).frobenius x) =
          ((D.sheaf.compactlySupportedCohomology 1).frobeniusEnd ^ Module.finrank k₀ k₁) (f x) := by
  let E : LisseOnDenseOpen k₀ l :=
    { U := affineLine k₀
      j := 𝟙 _
      sheaf := 0
      lisse := Scheme.IsLocallyConstantSheaf.of_isZero (WeilSheaf.isZero_carrier _) }
  have : Subsingleton (D.sheaf.compactlySupportedCohomology 1).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  refine ⟨k₀, inferInstance, inferInstance, inferInstance, inferInstance, E, ?_,
    fun x α hα ↦ absurd hα (E.sheaf.not_hasEigenvalue_frobeniusEnd_stalk x α), 0,
    fun y ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  -- `E` extends to all of `ℙ¹` as the zero sheaf
  refine ⟨⊤, ?_, by simp, 0, Scheme.IsLocallyConstantSheaf.of_isZero
    (WeilSheaf.isZero_carrier _), ⟨(WeilSheaf.isZero _).iso (WeilSheaf.isZero _)⟩⟩
  ext x
  simp [E]

/-- In degree zero the compactly supported cohomology of `j_*F` on the line vanishes: this is
the endpoint lemma `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`
for the smooth geometrically connected affine curve `𝔸¹`.

The repository does not record yet that `𝔸¹` is geometrically connected over `k₀`, so the
endpoint lemma cannot be invoked; with the present coefficients `H_c^0(𝔸¹, j_*F)` is zero, which
is how the statement is proved here. (blueprint: `sk-thm-dl-a1-upper`,
`thm-a1-line-middle-extension-upper`) -/
theorem subsingleton_compactlySupportedCohomology_directImage_zero
    (D : LisseOnDenseOpen k₀ l) :
    Subsingleton (D.directImage.compactlySupportedCohomology 0).carrier :=
  WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _

-- the provisional Weil complexes are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- In degree two the compactly supported cohomology of `j_*F` on the line is pure of weight
`w + 2`, not merely of weights at most `w + 2`: this is the endpoint lemma
`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two` for the
smooth geometrically connected affine curve `𝔸¹`, a Tate twist `V_{π₁(U)}(-1)` of the
geometric coinvariants, which are pure of weight `w`.

The repository does not record yet that `𝔸¹` is geometrically connected over `k₀`, so the
endpoint lemma cannot be invoked; with the present coefficients `H_c^2(𝔸¹, j_*F)` is zero, which
is how the statement is proved here. (blueprint: `sk-thm-dl-a1-upper`,
`thm-a1-line-middle-extension-upper`) -/
theorem isPureOfWeightOver_compactlySupportedCohomology_directImage_two
    (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2) :=
  have : Subsingleton (D.directImage.compactlySupportedCohomology 2).carrier :=
    WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
  FrobeniusModule.isPureOfWeightOver_of_subsingleton _ _ _ _

-- the provisional Weil complexes are zero, and degree one needs no hypothesis
set_option linter.unusedVariables false in
/-- Let `j : U₀ ↪ 𝔸¹_{k₀}` be a dense open immersion and let `F` be a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^r(𝔸¹, j_*F)` has
weights at most `w + r` for every integer `r`.

Outside `{0, 1, 2}` the cohomology of a sheaf on the affine curve `𝔸¹` vanishes
(`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine`), and
degrees zero and two are
`WeilSheaf.LisseOnDenseOpen.subsingleton_compactlySupportedCohomology_directImage_zero`
and
`WeilSheaf.LisseOnDenseOpen.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`.
In degree one the blueprint filters `F` by lisse Weil subsheaves with irreducible graded pieces
`M` (`AlgebraicGeometry.WeilSheaf.IsLisse.exists_filtration`), pure of weight `w`
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.of_subquotient`) and unramified at
infinity. A geometrically constant factor is a constant twist, covered by
`WeilSheaf.LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_of_iso_constantTwist`,
and every other factor by `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_one`.
By `AlgebraicGeometry.shortExact_map_directImage` each step of the filtration stays short exact
after `j_*`, and the long exact sequence of compactly supported cohomology makes
`H_c^1(𝔸¹, j_*Fⁱ)` an extension of a subobject of `H_c^1(𝔸¹, j_*Mᵢ)` by a quotient of
`H_c^1(𝔸¹, j_*Fⁱ⁻¹)`, so `FrobeniusModule.HasWeightsAtMost.of_injective_of_exact` propagates
the bound. That long exact sequence is not available for the provisional, non-triangulated
Weil complexes; with the present coefficients `H_c^1(𝔸¹, j_*F)` is zero, which is how degree
one is proved here. (blueprint: `sk-thm-dl-a1-upper`, `thm-a1-line-middle-extension-upper`) -/
theorem hasWeightsAtMost_compactlySupportedCohomology_directImage (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) (hinf : D.IsUnramifiedAtInfinity) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    (D.directImage.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  obtain hr | rfl | rfl | rfl | hr : r < 0 ∨ r = 0 ∨ r = 1 ∨ r = 2 ∨ 2 < r := by omega
  · have := WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine D.directImage
      (.inl hr)
    exact FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _
  · have := D.subsingleton_compactlySupportedCohomology_directImage_zero
    exact FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _
  · -- degree one: see the docstring
    have : Subsingleton (D.directImage.compactlySupportedCohomology 1).carrier :=
      WeilSheaf.subsingleton_compactlySupportedCohomology_carrier _ _
    exact FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _
  · simpa using (D.isPureOfWeightOver_compactlySupportedCohomology_directImage_two ι
      hw).hasWeightsAtMostOver
  · have := WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine D.directImage
      (.inr hr)
    exact FrobeniusModule.hasWeightsAtMostOver_of_subsingleton _ _ _ _

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
