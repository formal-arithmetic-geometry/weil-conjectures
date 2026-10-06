/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension
public import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy

/-!
# The realified Fourier kernel

Let `M` be a lisse Weil sheaf on a dense open `j : U₀ ↪ A₀ = 𝔸¹_{k₀}`, punctually `ι`-pure of
weight `w`, and let `b ∈ ℚ̄_ℓˣ` with `ι b = q ^ w`. Its *twisted dual* is
`M† = M^∨ ⊗ 𝓑_b`, whose local eigenvalues are the `ι`-conjugates of those of `M`. On the
Fourier square `A₀ ×_{k₀} A'₀`, with projections `p₁` and `p₂`, the *realified kernel* is

`𝒦 = p₁^*(j_!M) ⊗ 𝒦_ψ ⊕ p₁^*(j_!M†) ⊗ 𝒦_{ψ⁻¹}`,

where `𝒦_ψ = μ^* ℒ_ψ` is the Fourier kernel, the pullback of the Artin–Schreier sheaf along
the multiplication `μ : (x, ξ) ↦ x ξ`. Its two summands have conjugate local eigenvalues, so it
is `ι`-real. For a constituent-nonexceptional `M` the compactly supported direct images of `𝒦`
along `p₂` are concentrated in degree one, and `R¹p₂!𝒦` is then `ι`-real and contains
`FT_ψ(j_!M)` as a direct summand. This is the real envelope of the transform used to show that
the generic Fourier sheaf is pure of some weight
(`WeilConjectures.DeligneLaumon.AffineLine.Purity`). Forming the envelope after extension by
zero is what makes it real: at a missing point both summands have zero stalk.

## Main definitions

- `AlgebraicGeometry.affineLine.fourierSquare`: the Fourier square `A₀ ×_{k₀} A'₀`.
- `AlgebraicGeometry.WeilSheaf.fourierKernel`: the Fourier kernel `𝒦_ψ = ℒ_{ψ(x ξ)}`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.realifiedKernel`: the realified kernel.

## Main statements

- `AlgebraicGeometry.WeilSheaf.isReal_higherLowerShriek_one_of_isReal`: reality survives the
  Fourier projection (blueprint: `lem-fd-realness-pushforward`).
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isReal_realifiedKernel`: the realified kernel is
  real (blueprint: `lem-fd-realified-kernel-real`).
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_higherLowerShriek_realifiedKernel` and
  its companions: concentration of the zero-extension transform
  (blueprint: `lem-fd-constituent-nonexceptional-concentration`).
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isReal_higherLowerShriek_one_realifiedKernel`:
  `R¹p₂!𝒦` is real (Step 1 of blueprint `thm-fd-generic-fourier-sheaf-pure`).

## Implementation notes

With the present coefficients every Weil sheaf is zero (`AlgebraicGeometry.WeilSheaf.isZero`),
and so is every Weil complex (`AlgebraicGeometry.WeilComplex.isZero`). This is how the
statements of this file are proved; the comments in the proofs record the blueprint argument
that will replace it once Weil sheaves are redefined with `ℓ`-adic coefficients.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The Fourier square `A₀ ×_{k₀} A'₀` of the affine line `A₀ = 𝔸¹_{k₀}` and its dual line
`A'₀`, another copy of the affine line. -/
noncomputable abbrev affineLine.fourierSquare (k₀ : Type u) [Field k₀] : Scheme.{u} :=
  pullback (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

namespace affineLine

/-- The Fourier square is a `k₀`-scheme through its projection to the dual line. -/
noncomputable instance (k₀ : Type u) [Field k₀] :
    (fourierSquare k₀).Over (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.snd _ _ ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀)⟩

instance (k₀ : Type u) [Field k₀] :
    (pullback.fst (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.condition⟩

instance (k₀ : Type u) [Field k₀] :
    (pullback.snd (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

/-- The pairing `μ : (x, ξ) ↦ x ξ` of the Fourier square, a morphism to the affine line. -/
noncomputable def fourierPairing (k₀ : Type u) [Field k₀] :
    fourierSquare k₀ ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (fourierSquare k₀ ↘ Spec (CommRingCat.of k₀))
    fun _ ↦ AffineSpace.stdPairing PUnit.{u + 1} (Spec (CommRingCat.of k₀))

instance (k₀ : Type u) [Field k₀] :
    (fourierPairing k₀).IsOver (Spec (CommRingCat.of k₀)) := by
  unfold fourierPairing
  infer_instance

end affineLine

/-- The first projection `p₁ : A₀ ×_{k₀} A'₀ ⟶ A₀` of the Fourier square. -/
local notation "p₁" => pullback.fst (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
  (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

/-- The second projection `p₂ : A₀ ×_{k₀} A'₀ ⟶ A'₀` of the Fourier square. -/
local notation "p₂" => pullback.snd (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
  (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

namespace WeilSheaf

/-- The Fourier kernel `𝒦_ψ = ℒ_{ψ(x ξ)} = μ^* ℒ_ψ` on the Fourier square: the pullback of the
Artin–Schreier sheaf `ℒ_{ψ(x)}` along the pairing `μ : (x, ξ) ↦ x ξ`. It is lisse of rank one,
and `𝒦_{ψ⁻¹}` is its inverse. (blueprint: `def-fd-kernel`) -/
noncomputable def fourierKernel (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilSheaf k₀ l (affineLine.fourierSquare k₀) :=
  (upperStar (affineLine.fourierPairing k₀)).obj (artinSchreier ψ 1)

-- with the present coefficients the stalks are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- **Reality survives the Fourier projection.** Let `𝒦` be an `ι`-real Weil sheaf on the
Fourier square whose compactly supported direct images `Rᵛp₂!𝒦` along the second projection
vanish for `ν ≠ 1`. Then `R¹p₂!𝒦` is `ι`-real. At a closed point `ξ` of the dual line the
Grothendieck–Lefschetz trace formula on the fibre gives
`-Tr(F_ξᵐ | (R¹p₂!𝒦)_ξ̄) = ∑ₓ Tr(Fₓᵐ | 𝒦_x̄)`, a sum of traces of conjugation-stable
eigenvalue multisets, hence real; Newton's identities make the local polynomial at `ξ` real.
(blueprint: `lem-fd-realness-pushforward`) -/
theorem isReal_higherLowerShriek_one_of_isReal (ι : PadicAlgCl l →+* ℂ)
    {K : WeilSheaf k₀ l (affineLine.fourierSquare k₀)} (hK : K.IsReal ι)
    (hvan : ∀ ν ≠ 1, IsZero ((higherLowerShriek k₀ l p₂ ν).obj K)) :
    ((higherLowerShriek k₀ l p₂ 1).obj K).IsReal ι := by
  -- with the present coefficients the stalks of `R¹p₂!𝒦` are zero
  -- (`AlgebraicGeometry.WeilSheaf.isZero_stalkObj`), so its local polynomials are `1`
  intro x n
  rw [localPolynomial_stalk_eq_one, Polynomial.coeff_one]
  split_ifs <;> simp

namespace LisseOnDenseOpen

variable (ψ : AddChar k₀ (PadicAlgCl l)) (D : LisseOnDenseOpen k₀ l)

/-- The realified kernel on the Fourier square attached to `D = (j : U₀ ↪ A₀, M)` and a unit
`b ∈ ℚ̄_ℓˣ`,

`𝒦 = p₁^*(j_!M) ⊗ 𝒦_ψ ⊕ p₁^*(j_!M†) ⊗ 𝒦_{ψ⁻¹}`,

where `M† = M^∨ ⊗ 𝓑_b` is the twisted dual of `M`. It is meant for `M` punctually `ι`-pure of
weight `w` and `ι b = q ^ w`, when it is `ι`-real
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isReal_realifiedKernel`). The derived tensor
products of the blueprint are ordinary ones, the Fourier kernels being lisse.
(blueprint: `lem-fd-realified-kernel-real`) -/
noncomputable def realifiedKernel (b : (PadicAlgCl l)ˣ) :
    WeilSheaf k₀ l (affineLine.fourierSquare k₀) :=
  ((upperStar p₁).obj D.extensionByZero).tensorObj (fourierKernel ψ) ⊞
    ((upperStar p₁).obj ((WeilSheaf.extensionByZero D.j).obj
      (D.sheaf.dual.constantTwist b))).tensorObj (fourierKernel ψ⁻¹)

-- with the present coefficients the stalks are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- **The realified kernel is real.** If `M` is punctually `ι`-pure of weight `w` and
`ι b = q ^ w`, the realified kernel is `ι`-real. At a closed point `x` of `U₀` of degree `m`
the eigenvalues `b ᵐ α⁻¹` of `M†` have `ι (b ᵐ α⁻¹) = q ^ (m w) / ι α = conj (ι α)`, while the
Fourier kernel `𝒦_ψ`, pure of weight `0`
(`AlgebraicGeometry.isPunctuallyPureOfWeight_artinSchreier`), has a unique eigenvalue `λ`
with `conj (ι λ) = ι λ⁻¹`, the eigenvalue of `𝒦_{ψ⁻¹}`. So at a point `z` of the square
over `x` the conjugation exchanges the eigenvalues `αᵉ λ` of the first summand with the
eigenvalues `conj (ι α)ᵉ λ⁻¹` of the second. Over a missing point both summands have zero
stalk. No irreducibility or nonexceptionality of `M` is needed.
(blueprint: `lem-fd-realified-kernel-real`) -/
theorem isReal_realifiedKernel (ι : PadicAlgCl l →+* ℂ) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ}
    (hb : ι b = ((Nat.card k₀ : ℝ) ^ w : ℝ)) :
    (D.realifiedKernel ψ b).IsReal ι := by
  -- with the present coefficients the stalks of `𝒦` are zero
  -- (`AlgebraicGeometry.WeilSheaf.isZero_stalkObj`), so its local polynomials are `1`
  intro x n
  rw [localPolynomial_stalk_eq_one, Polynomial.coeff_one]
  split_ifs <;> simp

-- with the present coefficients every Weil sheaf is zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- **Twisted compactly supported cohomology is concentrated in degree one.** Let `M` be a
nonzero irreducible lisse sheaf on `U₀` which is constituent-nonexceptional. Then for every
`a ∈ k₀` the compactly supported cohomology `H_c^q(A, j_!M ⊗ ℒ_{ψ(a x)}) = H_c^q(U, M ⊗ ℒ_{ψ(a x)})`
vanishes for `q ≠ 1`: `H_c^0` vanishes on an affine curve, and a nonzero `H_c^2`, the
coinvariants of `M ⊗ ℒ_{ψ(a x)}` under the geometric monodromy, would make `ℒ_{ψ(-a x)}` a
geometric constituent of `M`. The blueprint allows `a` in the algebraic closure; the
Artin–Schreier sheaves of the repository are only defined for `a ∈ k₀`.
(blueprint: `lem-fd-constituent-nonexceptional-concentration`, part 1) -/
theorem subsingleton_compactlySupportedCohomology_tensorObj_artinSchreier [Simple D.sheaf]
    (hne : D.sheaf.IsNonexceptional ψ) (a : k₀) {q : ℤ} (hq : q ≠ 1) :
    Subsingleton
      ((D.extensionByZero.tensorObj (artinSchreier ψ a)).compactlySupportedCohomology q).carrier :=
  -- with the present coefficients every Weil complex is zero
  WeilComplex.subsingleton_compactlySupportedCohomology_carrier _ q

-- TODO(adic): needs geometric irreducible constituents, through which
-- `AlgebraicGeometry.WeilSheaf.HasLinearArtinSchreierConstituent` is to be defined
/-- **The twisted dual is constituent-nonexceptional.** If `M` is constituent-nonexceptional,
so is its twisted dual `M† = M^∨ ⊗ 𝓑_b`: after geometric base change `𝓑_b` is trivial, the
geometric constituents of `M^∨` are the duals of those of `M`, and the dual of `ℒ_{ψ(a x)}` is
`ℒ_{ψ(-a x)}`. (blueprint: `lem-fd-constituent-nonexceptional-concentration`, part 2) -/
theorem isNonexceptional_constantTwist_dual (hne : D.sheaf.IsNonexceptional ψ)
    (b : (PadicAlgCl l)ˣ) : (D.sheaf.dual.constantTwist b).IsNonexceptional ψ⁻¹ :=
  sorry

-- with the present coefficients every Weil complex is zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- **The zero-extension transform is a sheaf.** For a nonzero irreducible lisse sheaf `M` on
`U₀` which is constituent-nonexceptional, the transform `FT_ψ(j_!M[1])` is concentrated in
degree `-1`, that is, `FT_ψ(j_!M)` is a sheaf: by the stalk formula its stalk at `ξ̄` is
`H_c^*(U, M ⊗ ℒ_{ψ(ξ x)})[1]`, concentrated in degree `0` by part 1 (`AlgebraicGeometry.
WeilSheaf.LisseOnDenseOpen.subsingleton_compactlySupportedCohomology_tensorObj_artinSchreier`).
(blueprint: `lem-fd-constituent-nonexceptional-concentration`, part 3) -/
theorem isZero_homologySheaf_fourierTransform_shiftedExtensionByZero [Simple D.sheaf]
    (hne : D.sheaf.IsNonexceptional ψ) {n : ℤ} (hn : n ≠ -1) :
    IsZero ((WeilComplex.homologySheaf n).obj
      ((fourierTransform ψ).obj D.shiftedExtensionByZero)) :=
  -- with the present coefficients every Weil sheaf is zero
  WeilSheaf.isZero _

-- with the present coefficients every Weil sheaf is zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- **The realified kernel has a single direct image.** For a nonzero irreducible lisse sheaf
`M` on `U₀`, constituent-nonexceptional and punctually `ι`-pure of weight `w`, and
`ι b = q ^ w`, the compactly supported direct images `Rᵛp₂!𝒦` of the realified kernel vanish
for `ν ≠ 1`: the direct images of the two summands are `FT_ψ(j_!M)[-1]` and
`FT_{ψ⁻¹}(j_!M†)[-1]`, both concentrated in degree one by part 3, applied to `M` and to its
twisted dual (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isNonexceptional_constantTwist_dual`).
(blueprint: `lem-fd-constituent-nonexceptional-concentration`, part 3) -/
theorem isZero_higherLowerShriek_realifiedKernel (ι : PadicAlgCl l →+* ℂ) [Simple D.sheaf]
    (hne : D.sheaf.IsNonexceptional ψ) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w)
    {b : (PadicAlgCl l)ˣ} (hb : ι b = ((Nat.card k₀ : ℝ) ^ w : ℝ)) {ν : ℕ} (hν : ν ≠ 1) :
    IsZero ((higherLowerShriek k₀ l p₂ ν).obj (D.realifiedKernel ψ b)) :=
  -- with the present coefficients every Weil sheaf is zero
  WeilSheaf.isZero _

-- with the present coefficients every Weil sheaf is zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- **The zero-extension transform is a direct summand of `R¹p₂!𝒦`.** In the situation of
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_higherLowerShriek_realifiedKernel`, the
sheaf `G = 𝓗⁻¹ FT_ψ(j_!M[1]) = FT_ψ(j_!M)` is a direct summand of `R¹p₂!𝒦`: since `Rp₂!` is
additive, `R¹p₂!𝒦 ≅ FT_ψ(j_!M) ⊕ FT_{ψ⁻¹}(j_!M†)`.
(blueprint: `lem-fd-constituent-nonexceptional-concentration`, part 3) -/
theorem exists_comp_eq_id_higherLowerShriek_realifiedKernel (ι : PadicAlgCl l →+* ℂ)
    [Simple D.sheaf] (hne : D.sheaf.IsNonexceptional ψ) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) {b : (PadicAlgCl l)ˣ}
    (hb : ι b = ((Nat.card k₀ : ℝ) ^ w : ℝ)) :
    ∃ (i : (WeilComplex.homologySheaf (-1)).obj
        ((fourierTransform ψ).obj D.shiftedExtensionByZero) ⟶
        (higherLowerShriek k₀ l p₂ 1).obj (D.realifiedKernel ψ b))
      (r : (higherLowerShriek k₀ l p₂ 1).obj (D.realifiedKernel ψ b) ⟶
        (WeilComplex.homologySheaf (-1)).obj
          ((fourierTransform ψ).obj D.shiftedExtensionByZero)),
      i ≫ r = 𝟙 _ :=
  -- with the present coefficients every Weil sheaf is zero
  ⟨0, 0, (WeilSheaf.isZero _).eq_of_src _ _⟩

/-- **The real envelope of the zero-extension transform.** For a nonzero irreducible lisse sheaf
`M` on `U₀`, constituent-nonexceptional and punctually `ι`-pure of weight `w`, and
`ι b = q ^ w`, the sheaf `R¹p₂!𝒦` on the dual line, which contains `FT_ψ(j_!M)` as a direct
summand, is `ι`-real: the realified kernel is real, its direct images are concentrated in
degree one, and reality survives the projection `p₂`.
(blueprint: `thm-fd-generic-fourier-sheaf-pure`, Step 1) -/
theorem isReal_higherLowerShriek_one_realifiedKernel (ι : PadicAlgCl l →+* ℂ) [Simple D.sheaf]
    (hne : D.sheaf.IsNonexceptional ψ) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w)
    {b : (PadicAlgCl l)ˣ} (hb : ι b = ((Nat.card k₀ : ℝ) ^ w : ℝ)) :
    ((higherLowerShriek k₀ l p₂ 1).obj (D.realifiedKernel ψ b)).IsReal ι :=
  isReal_higherLowerShriek_one_of_isReal ι (D.isReal_realifiedKernel ψ ι hw hb)
    fun _ hν ↦ D.isZero_higherLowerShriek_realifiedKernel ψ ι hne hw hb hν

end LisseOnDenseOpen

end WeilSheaf

end AlgebraicGeometry
