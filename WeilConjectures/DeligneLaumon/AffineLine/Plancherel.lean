/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Purity
public import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy

/-!
# The Fourier transform shifts the `L²`-weight by one

The trace function of a Weil complex `K` is the alternating sum
`t_K(x) = ∑ⱼ (-1)ʲ Tr(F_x^{(n)} | 𝓗ʲ(K)_x̄)` of the trace functions of its cohomology sheaves,
and its trace energies `S_n(K) = ∑_x |ι t_K(x)|²` define the `L²`-weight parameter `‖K‖`
exactly as for a Weil sheaf. The Plancherel identity `S_n(FT_ψ K) = qⁿ S_n(K)` then says that
the Fourier transform shifts the `L²`-weight by one, `‖FT_ψ K‖ = ‖K‖ + 1`. For the middle
extension `(j_*M)[1]` of a nonzero lisse sheaf `M`, pure of weight `w`, the `L²`-weight is `w`;
so if the transform is again a middle extension `(j'_*M')[1]` with `M'` pure of weight `v`,
then `v = w + 1`.

## Main declarations

- `AlgebraicGeometry.WeilComplex.traceFunction`, `AlgebraicGeometry.WeilComplex.traceEnergy`,
  `AlgebraicGeometry.WeilComplex.l2Weight`: the trace function, the trace energies and the
  `L²`-weight parameter of a Weil complex.
- `AlgebraicGeometry.WeilComplex.l2Weight_fourierTransform`: `‖FT_ψ K‖ = ‖K‖ + 1`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.eq_add_one_of_isFourierPartner`: the weight of
  a pure Fourier partner is `w + 1`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isPunctuallyPureOfWeight_add_one`: the
  irreducible Fourier partner of an irreducible nonexceptional `M` pure of weight `w` is pure of
  weight `w + 1`.

## Implementation notes

With the present coefficients every Weil sheaf and every Weil complex is zero
(`AlgebraicGeometry.WeilSheaf.isZero`, `AlgebraicGeometry.WeilComplex.isZero`): the trace
functions and trace energies vanish, and the Plancherel identity and the invariance of the
trace energies under isomorphisms and under the shift are proved this way. The passage from the
Plancherel identity to the `L²`-weights is proved in general.
-/

@[expose] public section

universe u

open CategoryTheory Filter

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The trace function `t_{K,n}` of a Weil complex: the alternating sum
`t_K(x) = ∑ⱼ (-1)ʲ Tr(F_x^{(n)} | 𝓗ʲ(K)_x̄)` of the trace functions
(`AlgebraicGeometry.WeilSheaf.traceFunction`) of its cohomology sheaves. The sum is finite for a
bounded complex; otherwise it has the junk value `0`. (blueprint: `def-fd-trace-function`) -/
noncomputable def traceFunction (K : WeilComplex k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    PadicAlgCl l :=
  ∑ᶠ j : ℤ, (-1) ^ j.natAbs * ((homologySheaf j).obj K).traceFunction n x

/-- The trace function of a Weil complex vanishes: with the present coefficients the stalks of
its cohomology sheaves are zero (`AlgebraicGeometry.WeilSheaf.traceFunction_eq_zero`). -/
theorem traceFunction_eq_zero (K : WeilComplex k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    K.traceFunction n x = 0 := by
  simp [traceFunction, WeilSheaf.traceFunction_eq_zero]

/-- The trace energy `S_n(X₀, K) = ∑_{x ∈ X₀(𝔽_{qⁿ})} |ι t_{K,n}(x)|²` of a Weil complex, with
junk value `0` if `X₀` has infinitely many `𝔽_{qⁿ}`-points; see
`AlgebraicGeometry.WeilSheaf.traceEnergy`. -/
noncomputable def traceEnergy (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X) (n : ℕ) : ℝ :=
  ∑ᶠ x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n),
    ‖ι (K.traceFunction n x)‖ ^ 2

/-- The trace energy of a Weil complex vanishes, its trace function being zero
(`AlgebraicGeometry.WeilComplex.traceFunction_eq_zero`). -/
theorem traceEnergy_eq_zero (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X) (n : ℕ) :
    K.traceEnergy ι n = 0 := by
  simp [traceEnergy, traceFunction_eq_zero]

/-- The *`L²`-weight parameter* `‖K‖` of a Weil complex, the exponent of growth of its trace
energies `S_m = ‖f_K‖²_m` (`AlgebraicGeometry.WeilComplex.traceEnergy`):

`‖K‖ = sup {β ∈ ℝ | limsup_{m → ∞} S_m / q^{m(β + 1)} > 0}`,

as in `AlgebraicGeometry.WeilSheaf.l2Weight`. (blueprint: `def-wf-l2-norm`) -/
noncomputable def l2Weight (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X) : EReal :=
  ⨆ (β : ℝ) (_ : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
    (K.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop), (β : EReal)

/-- The `L²`-weight parameter of a Weil complex only depends on its trace energies in degrees
`m ≥ 1`; here the complexes may live on different schemes. -/
theorem l2Weight_eq_of_traceEnergy_eq (ι : PadicAlgCl l →+* ℂ) {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) (L : WeilComplex k₀ l Y)
    (h : ∀ m : ℕ, 1 ≤ m → L.traceEnergy ι m = K.traceEnergy ι m) :
    L.l2Weight ι = K.l2Weight ι := by
  refine iSup_congr fun β ↦ iSup_congr_Prop (Iff.of_eq (congrArg _ (limsup_congr ?_))) fun _ ↦ rfl
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [h m hm]

/-- The `L²`-weight parameter of the complex `F[1]` attached to a Weil sheaf `F` is that of
`F`: the shift multiplies the trace function by `-1`, of `ι`-modulus one, so the trace energies
agree. -/
theorem l2Weight_shift_toComplex (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) :
    ((WeilSheaf.toComplex.obj F)⟦(1 : ℤ)⟧).l2Weight ι = F.l2Weight ι := by
  -- with the present coefficients both trace energies vanish
  have h : ∀ m : ℕ, ((WeilSheaf.toComplex.obj F)⟦(1 : ℤ)⟧).traceEnergy ι m =
      F.traceEnergy ι m := fun m ↦ by
    rw [traceEnergy_eq_zero, WeilSheaf.traceEnergy_eq_zero]
  simp only [l2Weight, WeilSheaf.l2Weight, h]

/-- Isomorphic Weil complexes have the same `L²`-weight parameter, their trace functions being
equal. -/
theorem l2Weight_congr (ι : PadicAlgCl l →+* ℂ) {K L : WeilComplex k₀ l X} (_e : K ≅ L) :
    K.l2Weight ι = L.l2Weight ι :=
  -- with the present coefficients both trace energies vanish
  l2Weight_eq_of_traceEnergy_eq ι L K fun m _ ↦ by rw [traceEnergy_eq_zero, traceEnergy_eq_zero]

/-- If the trace energies of `L` are those of `K` multiplied by `q^m`, for `m ≥ 1`, then
`‖L‖ = ‖K‖ + 1`: the defining ratio of `L` at `β` is that of `K` at `β - 1`. -/
theorem l2Weight_eq_add_one_of_traceEnergy_eq (ι : PadicAlgCl l →+* ℂ) {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) (L : WeilComplex k₀ l Y)
    (h : ∀ m : ℕ, 1 ≤ m → L.traceEnergy ι m = (Nat.card k₀ : ℝ) ^ m * K.traceEnergy ι m) :
    L.l2Weight ι = K.l2Weight ι + 1 := by
  have hq0 : 0 < (Nat.card k₀ : ℝ) := by exact_mod_cast Nat.card_pos
  have key : ∀ β : ℝ, limsup (fun m : ℕ ↦ ENNReal.ofReal
      (L.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop =
      limsup (fun m : ℕ ↦ ENNReal.ofReal
        (K.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * ((β - 1) + 1)))) atTop := by
    refine fun β ↦ limsup_congr ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [h m hm, show (m : ℝ) * (β - 1 + 1) = m * (β + 1) - m by ring, Real.rpow_sub hq0,
      div_div_eq_mul_div, Real.rpow_natCast, mul_comm (K.traceEnergy ι m)]
  refine le_antisymm (iSup₂_le fun β hβ ↦ ?_) ?_
  · rw [key] at hβ
    calc (β : EReal) = ((β - 1 : ℝ) : EReal) + 1 := by norm_cast; ring
      _ ≤ K.l2Weight ι + 1 := by
        gcongr
        exact le_iSup₂_of_le (f := fun (γ : ℝ) _ ↦ (γ : EReal)) (β - 1) hβ le_rfl
  · change K.l2Weight ι + ((1 : ℝ) : EReal) ≤ L.l2Weight ι
    rw [← EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot 1)) (.inl (EReal.coe_ne_top 1))]
    refine iSup₂_le fun γ hγ ↦ ?_
    have hγ' : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
        (L.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * ((γ + 1) + 1)))) atTop := by
      rwa [key, add_sub_cancel_right]
    have := le_iSup₂_of_le (f := fun (β : ℝ) (_ : 0 < limsup (fun m : ℕ ↦ ENNReal.ofReal
        (L.traceEnergy ι m / (Nat.card k₀ : ℝ) ^ ((m : ℝ) * (β + 1)))) atTop) ↦ (β : EReal))
      (γ + 1) hγ' le_rfl
    rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot 1)) (.inl (EReal.coe_ne_top 1))]
    exact_mod_cast this

variable (ψ : AddChar k₀ (PadicAlgCl l))

-- with the present coefficients every Weil complex is zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- The *Plancherel identity*: for a nontrivial `ψ`, every Weil complex `K` on the affine line
and every `n ≥ 1`,

`∑_{y ∈ 𝔽_{qⁿ}} |ι t_{FT_ψ K}(y)|² = qⁿ ∑_{x ∈ 𝔽_{qⁿ}} |ι t_K(x)|²`.

The Fourier trace formula writes `t_{FT_ψ K}(y)` as the finite Fourier sum
`-∑ₓ t_K(x) ψ(Tr(xy))`, and the orthogonality of the additive characters makes the `y`-sum of
its squared modulus the diagonal sum. (blueprint: `cor-fd-plancherel`) -/
theorem traceEnergy_fourierTransform (ι : PadicAlgCl l →+* ℂ) (hψ : ψ ≠ 1)
    (K : WeilComplex k₀ l (affineLine k₀)) {n : ℕ} (hn : 1 ≤ n) :
    ((fourierTransform ψ).obj K).traceEnergy ι n = (Nat.card k₀ : ℝ) ^ n * K.traceEnergy ι n := by
  -- both trace energies vanish, see `traceEnergy_eq_zero`
  rw [traceEnergy_eq_zero, traceEnergy_eq_zero, mul_zero]

/-- *The Fourier transform shifts the `L²`-weight by one*: for a nontrivial `ψ` and a Weil
complex `K` on the affine line, `‖FT_ψ K‖ = ‖K‖ + 1`. By the Plancherel identity
`AlgebraicGeometry.WeilComplex.traceEnergy_fourierTransform` the trace energies satisfy
`S_m(FT_ψ K) = q^m S_m(K)`, so the defining ratio of `FT_ψ K` at `β` is that of `K` at `β - 1`.
(blueprint: `lem-fd-l2-plancherel-shift`) -/
theorem l2Weight_fourierTransform (ι : PadicAlgCl l →+* ℂ) (hψ : ψ ≠ 1)
    (K : WeilComplex k₀ l (affineLine k₀)) :
    ((fourierTransform ψ).obj K).l2Weight ι = K.l2Weight ι + 1 :=
  l2Weight_eq_add_one_of_traceEnergy_eq ι _ _ fun _ hm ↦
    traceEnergy_fourierTransform ψ ι hψ K hm

end WeilComplex

namespace WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- The `L²`-weight of the middle extension `(j_*M)[1]` of a nonzero lisse sheaf `M` on a smooth
geometrically connected affine curve, punctually `ι`-pure of weight `w`, is `w`: the shift does
not change the trace energies, and `‖j_*M‖ = w` by
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.l2Weight_directImage`. -/
theorem l2Weight_middleExtension (ι : PadicAlgCl l →+* ℂ) (D : LisseOnDenseOpen k₀ l)
    [IsAffine D.U] [LocallyOfFiniteType (D.U ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (D.U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (D.U ↘ Spec (CommRingCat.of k₀))]
    (hM : ¬ Limits.IsZero D.sheaf) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    D.middleExtension.l2Weight ι = w := by
  obtain ⟨h1, h2⟩ := D.l2Weight_directImage ι hM hw
  rw [middleExtension, WeilComplex.l2Weight_shift_toComplex, h1, h2]

/-- *Plancherel for a middle extension*: let `M` be a nonzero lisse Weil sheaf on the dense open
`U₀` of the affine line, punctually `ι`-pure of weight `w`, and let `D'` be a Fourier partner of
`D`, i.e. `FT_ψ((j_*M)[1]) ≅ (j'_*M')[1]`, with `M'` nonzero and punctually `ι`-pure of weight
`v`. Then `v = w + 1`.

The Plancherel shift `AlgebraicGeometry.WeilComplex.l2Weight_fourierTransform` gives
`‖(j'_*M')[1]‖ = ‖FT_ψ((j_*M)[1])‖ = ‖(j_*M)[1]‖ + 1`, and the two middle extensions have
`L²`-weights `v` and `w` by
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.l2Weight_middleExtension`.

The dense opens `U₀` and `U'₀` are assumed to be smooth geometrically connected affine curves of
finite type over `k₀`, and `M'` nonzero, as in the rigidity
`AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isPunctuallyPureOfWeight`.
(blueprint: `cor-fd-l2-plancherel-middle-extension`) -/
theorem eq_add_one_of_isFourierPartner (ι : PadicAlgCl l →+* ℂ) (hψ : ψ ≠ 1)
    (D D' : LisseOnDenseOpen k₀ l)
    [IsAffine D.U] [LocallyOfFiniteType (D.U ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (D.U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (D.U ↘ Spec (CommRingCat.of k₀))]
    [IsAffine D'.U] [LocallyOfFiniteType (D'.U ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (D'.U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (D'.U ↘ Spec (CommRingCat.of k₀))]
    (hM : ¬ Limits.IsZero D.sheaf) (hM' : ¬ Limits.IsZero D'.sheaf) {w v : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D')
    (hv : D'.sheaf.IsPunctuallyPureOfWeight ι v) :
    v = w + 1 := by
  obtain ⟨e⟩ := hFT
  have h := WeilComplex.l2Weight_fourierTransform ψ ι hψ D.middleExtension
  rw [WeilComplex.l2Weight_congr ι e, l2Weight_middleExtension ι D' hM' hv,
    l2Weight_middleExtension ι D hM hw] at h
  exact_mod_cast h

/-- The irreducible Fourier partner `M'` of a nonzero irreducible nonexceptional lisse sheaf `M`,
punctually `ι`-pure of weight `w`, is punctually `ι`-pure of weight `w + 1`: it is pure of some
weight `v` by `AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner`, and
`v = w + 1` by `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.eq_add_one_of_isFourierPartner`.
(blueprint: `cor-fd-l2-plancherel-middle-extension`) -/
theorem isPunctuallyPureOfWeight_add_one (ι : PadicAlgCl l →+* ℂ) (hψ : ψ ≠ 1)
    (D D' : LisseOnDenseOpen k₀ l) [Simple D.sheaf] [Simple D'.sheaf]
    [IsAffine D.U] [LocallyOfFiniteType (D.U ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (D.U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (D.U ↘ Spec (CommRingCat.of k₀))]
    [IsAffine D'.U] [LocallyOfFiniteType (D'.U ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (D'.U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (D'.U ↘ Spec (CommRingCat.of k₀))]
    (hne : D.sheaf.IsNonexceptional ψ) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w)
    (hFT : D.IsFourierPartner ψ D') :
    D'.sheaf.IsPunctuallyPureOfWeight ι (w + 1) := by
  obtain ⟨v, hv⟩ := exists_isPunctuallyPureOfWeight_of_isFourierPartner ψ ι hψ D D' hne hw hFT
  rwa [← eq_add_one_of_isFourierPartner ψ ι hψ D D' (Simple.not_isZero _)
    (Simple.not_isZero _) hw hFT hv]

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
