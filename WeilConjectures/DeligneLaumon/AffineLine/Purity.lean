/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist
public import WeilConjectures.DeligneLaumon.AffineLine.DenseOpen
public import WeilConjectures.DeligneLaumon.AffineLine.RealPushforward
public import WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel
public import WeilConjectures.WeilSheaf.DenseOpen
public import WeilConjectures.WeilSheaf.FiniteLength
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.OpenImmersionRestriction
public import WeilConjectures.WeilSheaf.RealPurity
public import WeilConjectures.WeilSheaf.StalkIso
public import WeilConjectures.WeilSheaf.UpperStarExact
public import WeilConjectures.WeilSheaf.UpperStarPointwise

/-!
# The generic Fourier sheaf is pure of some weight

Write `M^c = M^∨ ⊗ T_w` for the conjugate of a sheaf pure of weight `w`, where `T_w` is the
constant Weil line whose Frobenius has realization `q^w`. On a common dense lisse open the
paired complex `FT_ψ(j_!M[1]) ⊕ FT_{ψ⁻¹}(j_!M^c[1])` is `H[1]` for a lisse sheaf `H`, and the
Fourier trace identity makes every point trace of `H` a sum `-∑_x (a_x ψ_n(xy) + a̅_x ψ_n(xy)⁻¹)`,
which is real. Newton's identities then make every local characteristic polynomial real, so
`H` is `ι`-real; real-sheaf purity gives each of its irreducible constituents, in particular
`M'`, a real weight, and semicontinuity extends purity to the whole lisse domain of `M'`.

Forming the conjugate envelope *after* extending by zero is what avoids assuming reality of
`j_*M` itself.

## Implementation notes

The realified kernel `𝒦 = pr₁^*(j_!M) ⊗ 𝒦_ψ ⊕ pr₁^*(j_!M†) ⊗ 𝒦_{ψ⁻¹}` is formed with
`M† = M^∨ ⊗ 𝓑_b`, `ι b = q^w`. Since `ι` is only an embedding, such a `b` need not exist; we
first reduce to weight `0` by a constant twist
(`AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner_of_weight_zero`), where
`b = 1`.

The real-sheaf purity argument is run for the Fourier partner `D''` with irreducible lisse sheaf
supplied by `AlgebraicGeometry.exists_middleExtension_fourierTransform`; purity is then
transferred to an arbitrary Fourier partner `D'` pointwise, on the common dense open, through
`j'_*M' ≅ j''_*M''` and `j'^* j'_* M' ≅ M'`, and extended by
`AlgebraicGeometry.WeilSheaf.IsLisse.isPunctuallyPureOfWeight_of_upperStar`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isReal_higherLowerShriek_realifiedKernel`: the
  sheaf `H = R¹pr₂! 𝒦` is `ι`-real, and it surjects onto the middle extension `j'_*M'`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_isPunctuallyPureOfWeight_of_correction`:
  the purity argument for an irreducible Fourier partner (`thm-fd-generic-fourier-sheaf-pure`,
  steps 1–4).
- `AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner`: the Fourier
  partner of an irreducible nonexceptional pure sheaf is pure of some real weight.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf.LisseOnDenseOpen

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ψ : AddChar k₀ (PadicAlgCl l)}

/-- The transform of the zero extension `j_!M` of `D` is the middle term `G` of the correction
sequence, placed in degree `0`: cancel the shift in `FT_ψ(j_!M[1]) ≅ G[1]`. -/
noncomputable def FourierCorrection.fourierTransformExtensionByZeroIso
    {D D' : LisseOnDenseOpen k₀ l} (c : FourierCorrection ψ D D') :
    (fourierTransform ψ).obj (toComplex.obj D.extensionByZero) ≅ toComplex.obj c.seq.X₂ :=
  (shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (1 : ℤ)).preimageIso
    ((((fourierTransform ψ).commShiftIso (1 : ℤ)).app _).symm ≪≫ c.isoExtensionByZero)

instance (ν : ℕ) : PreservesBinaryBiproducts (higherLowerShriek k₀ l (affinePlane.snd k₀) ν) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

variable {D D' E' : LisseOnDenseOpen k₀ l} {b : (PadicAlgCl l)ˣ}
  (c : FourierCorrection ψ D D') (c' : FourierCorrection ψ⁻¹ (D.twistedDual b) E')

include c c' in
/-- The higher direct images with compact support `R^ν pr₂! 𝒦` of the realified kernel vanish
for `ν ≠ 1`, both transforms `FT_ψ(j_!M)` and `FT_{ψ⁻¹}(j_!M†)` being sheaves.
(blueprint: `lem-fd-constituent-nonexceptional-concentration`, part (3)) -/
theorem isZero_higherLowerShriek_realifiedKernel {ν : ℕ} (hν : ν ≠ 1) :
    IsZero ((higherLowerShriek k₀ l (affinePlane.snd k₀) ν).obj (realifiedKernel ψ D b)) :=
  ((biprod_isZero_iff _ _).2
    ⟨isZero_higherLowerShriek_fourierKernelTensor c.fourierTransformExtensionByZeroIso hν,
      isZero_higherLowerShriek_fourierKernelTensor c'.fourierTransformExtensionByZeroIso hν⟩).of_iso
    (Functor.mapBiprod _ _ _)

/-- The sheaf `H = R¹pr₂! 𝒦` of the realified kernel is the sum
`FT_ψ(j_!M) ⊕ FT_{ψ⁻¹}(j_!M†)` of the two transforms.
(blueprint: `lem-fd-constituent-nonexceptional-concentration`, part (3)) -/
noncomputable def higherLowerShriekRealifiedKernelIso :
    (higherLowerShriek k₀ l (affinePlane.snd k₀) 1).obj (realifiedKernel ψ D b) ≅
      c.seq.X₂ ⊞ c'.seq.X₂ :=
  Functor.mapBiprod _ _ _ ≪≫
    biprod.mapIso (higherLowerShriekFourierKernelTensorIso c.fourierTransformExtensionByZeroIso)
      (higherLowerShriekFourierKernelTensorIso c'.fourierTransformExtensionByZeroIso)

include c c' in
/-- **The sheaf `H = R¹pr₂! 𝒦` is `ι`-real**, when the realified kernel `𝒦` is: `R pr₂! 𝒦` is
concentrated in degree one. (blueprint: `thm-fd-generic-fourier-sheaf-pure`, step 1) -/
theorem isReal_higherLowerShriek_realifiedKernel {ι : PadicAlgCl l →+* ℂ}
    (hreal : (realifiedKernel ψ D b).IsReal ι) :
    ((higherLowerShriek k₀ l (affinePlane.snd k₀) 1).obj (realifiedKernel ψ D b)).IsReal ι :=
  isReal_higherLowerShriek_snd_one hreal fun _ hν ↦ isZero_higherLowerShriek_realifiedKernel c c' hν

/-- The epimorphism `H ↠ G ↠ j'_*M'` from the sheaf `H = R¹pr₂! 𝒦` of the realified kernel onto
the middle extension of the Fourier partner: the projection onto the summand `G = FT_ψ(j_!M)`
followed by the epimorphism of the correction sequence.
(blueprint: `thm-fd-generic-fourier-sheaf-pure`, steps 1–2) -/
noncomputable def higherLowerShriekRealifiedKernelToDirectImage :
    (higherLowerShriek k₀ l (affinePlane.snd k₀) 1).obj (realifiedKernel ψ D b) ⟶ D'.directImage :=
  (higherLowerShriekRealifiedKernelIso c c').hom ≫ biprod.fst ≫ c.seq.g ≫ c.isoDirectImage.hom

instance : Epi (higherLowerShriekRealifiedKernelToDirectImage c c') := by
  have := c.shortExact.epi_g
  unfold higherLowerShriekRealifiedKernelToDirectImage
  infer_instance

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- A nonempty open of the dense open `U₀` is dense in `U₀`. -/
theorem isDominant_opens_ι (D : LisseOnDenseOpen k₀ l) (W : D.U.Opens)
    (hW : (W : Set D.U).Nonempty) : IsDominant W.ι :=
  ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact W.isOpen.dense hW⟩

end AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen

namespace AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance] Abelian.hasFiniteBiproducts

variable {ψ : AddChar k₀ (PadicAlgCl l)} {D D' E' : LisseOnDenseOpen k₀ l} {b : (PadicAlgCl l)ˣ}
  (c : FourierCorrection ψ D D') (c' : FourierCorrection ψ⁻¹ (D.twistedDual b) E')

/-- The middle extension `j_*M` of the datum, unfolded. Rewriting with this equation avoids a
slow kernel check of the definitional unfolding. -/
theorem directImage_eq (D : LisseOnDenseOpen k₀ l) :
    D.directImage = (WeilSheaf.directImage D.j).obj D.sheaf :=
  rfl

/-- The restriction of the middle extension `j_*M` to `U₀` is `M`. -/
theorem nonempty_upperStar_directImage_iso (D : LisseOnDenseOpen k₀ l) :
    Nonempty ((upperStar D.j).obj D.directImage ≅ D.sheaf) :=
  by
  rw [directImage_eq]
  exact WeilSheaf.nonempty_upperStar_directImage_iso D.j D.sheaf

include c c' in
/-- **Purity of an irreducible Fourier partner.** Suppose that the realified kernel `𝒦` of `D`
is `ι`-real, and that `D'` is a Fourier partner of `D` whose lisse sheaf `M'` is irreducible,
with correction sequences `c` for `D` and `c'` for the twisted dual `D†` (so that both
transforms `FT_ψ(j_!M)` and `FT_{ψ⁻¹}(j_!M†)` are sheaves). Then `M'` is punctually `ι`-pure of
some real weight: on a dense open `W ⊆ U'` where `H = R¹pr₂! 𝒦` is lisse, `M'|_W` is an
irreducible quotient of the `ι`-real lisse sheaf `H|_W`, hence pure by real-sheaf purity, and
purity extends from `W` to `U'`. (blueprint: `thm-fd-generic-fourier-sheaf-pure`, steps 1–4) -/
theorem exists_isPunctuallyPureOfWeight_of_correction {ι : PadicAlgCl l →+* ℂ}
    (hreal : (realifiedKernel ψ D b).IsReal ι) (hD' : D'.sheaf.IsIrreducibleLisse) :
    ∃ v : ℝ, D'.sheaf.IsPunctuallyPureOfWeight ι v := by
  set H := (higherLowerShriek k₀ l (affinePlane.snd k₀) 1).obj (realifiedKernel ψ D b)
  have hH : H.IsReal ι := isReal_higherLowerShriek_realifiedKernel c c' hreal
  -- restrict the epimorphism `H ↠ j'_*M'` to `U'`, where `j'^* j'_* M' ≅ M'`
  obtain ⟨e⟩ := D'.nonempty_upperStar_directImage_iso
  let q : (upperStar D'.j).obj H ⟶ D'.sheaf :=
    (upperStar D'.j).map (higherLowerShriekRealifiedKernelToDirectImage c c') ≫ e.hom
  have : Epi q := epi_comp' ((upperStar D'.j).map_epi _) (IsIso.epi_of_iso e.hom)
  -- a dense open `W ⊆ U'` on which `j'^* H` is lisse
  obtain ⟨W, hWd, hWl⟩ := exists_dense_isLisse_upperStar ((upperStar D'.j).obj H)
  have := D'.nonempty_U
  have hW : (W : Set D'.U).Nonempty := hWd.nonempty
  have := D'.isDominant_opens_ι W hW
  have : Nonempty W := hW.to_subtype
  have := W.smoothOfRelativeDimension_one (k₀ := k₀)
  have := W.geometricallyIrreducible (k₀ := k₀)
  have : GeometricallyConnected (W.toScheme ↘ Spec (.of k₀)) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  have := W.locallyOfFiniteType (k₀ := k₀)
  have := W.isSeparated (k₀ := k₀)
  have := SmoothOfRelativeDimension.smooth 1 (W.toScheme ↘ Spec (.of k₀))
  have := irreducibleSpace_geometricFiber_of_smooth (k₀ := k₀) W.toScheme
  let G := (upperStar W.ι).obj ((upperStar D'.j).obj H)
  -- the irreducible quotient `M'|_W` of the real lisse sheaf `H|_W`
  let S : WeilSheaf k₀ l W := (upperStar W.ι).obj D'.sheaf
  have hS : S.IsIrreducibleLisse := hD'.upperStar_of_isDominant W.ι
  let qW : G ⟶ S := (upperStar W.ι).map q
  have : Epi qW := (upperStar W.ι).map_epi q
  have hreal' : G.IsReal ι := (hH.upperStar D'.j).upperStar W.ι
  have hker : (kernel qW).IsLisse := IsLisse.kernel hWl hS.1 qW
  let eS : cokernel (kernel.ι qW) ≅ S :=
    (colimit.isColimit _).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))
  obtain ⟨v, hv⟩ := IsReal.exists_isPunctuallyPureOfWeight_cokernel hWl hreal'
    (kernel.ι qW) (𝟙 _) hker hWl (hS.of_iso eS.symm)
  -- extend the purity from `W` to `U'`
  exact ⟨v, D'.lisse.isPunctuallyPureOfWeight_of_upperStar W.ι (hv.of_epi eS.hom)⟩

end AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen
