/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier

/-!
# The Fourier–Deligne transform on an affine space

Let `k₀` be a finite field, `ψ` an additive character of `k₀` with values in `ℚ̄_ℓ` and `ι` a
finite index type, of cardinality `r`. The *Fourier–Deligne transform* of a Weil complex `K` on
the affine space `𝔸^ι = 𝔸(ι; Spec k₀)` is

`FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ)[r]`,

where `pr₁, pr₂ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸^ι` are the projections and
`⟨-, -⟩ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸¹`, `(x, y) ↦ ∑ᵢ xᵢ yᵢ`, is the standard pairing
(`AlgebraicGeometry.affineSpaceFourierTransform`), with Laumon's shift by the relative dimension
`r`. Since `affineLine k₀` is `𝔸(PUnit; Spec k₀)`, the case `ι = PUnit` is the affine line, and
there the pairing is the multiplication `AlgebraicGeometry.affinePlane.mul`
(`AlgebraicGeometry.affineSpacePair.pairing_punit`).

## Main declarations

- `AlgebraicGeometry.affineSpacePair`: `𝔸^ι ×_{k₀} 𝔸^ι`, with its projections
  `AlgebraicGeometry.affineSpacePair.fst`, `AlgebraicGeometry.affineSpacePair.snd` and the
  pairing `AlgebraicGeometry.affineSpacePair.pairing`.
- `AlgebraicGeometry.affineSpaceFourierKernel`: the kernel `⟨-, -⟩^* ℒ_ψ`.
- `AlgebraicGeometry.affineSpaceFourierTransform`: the Fourier–Deligne transform on `𝔸^ι`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (ι : Type u) {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime]

section Geometry

variable (k₀)

/-- The product `𝔸^ι ×_{k₀} 𝔸^ι` of the affine space `𝔸^ι = 𝔸(ι; Spec k₀)` with itself, with
its two projections and the standard pairing to the affine line. For `ι = PUnit` it is the
affine plane `AlgebraicGeometry.affinePlane`. -/
noncomputable def affineSpacePair : Scheme.{u} :=
  pullback (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
    (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))

noncomputable instance affineSpacePair.instOver :
    (affineSpacePair ι k₀).Over (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.fst _ _ ≫ 𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)⟩

instance affineSpacePair.locallyOfFiniteType_over [Finite ι] :
    LocallyOfFiniteType (affineSpacePair ι k₀ ↘ Spec (CommRingCat.of k₀)) := by
  have : LocallyOfFiniteType
      (pullback.fst (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
        (𝔸(ι; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact inferInstanceAs (LocallyOfFiniteType (pullback.fst _ _ ≫ _))

/-- The first projection `pr₁ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸^ι`. -/
noncomputable def affineSpacePair.fst : affineSpacePair ι k₀ ⟶ 𝔸(ι; Spec (CommRingCat.of k₀)) :=
  pullback.fst _ _

/-- The second projection `pr₂ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸^ι`. -/
noncomputable def affineSpacePair.snd : affineSpacePair ι k₀ ⟶ 𝔸(ι; Spec (CommRingCat.of k₀)) :=
  pullback.snd _ _

instance affineSpacePair.isOver_fst :
    (affineSpacePair.fst ι k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

instance affineSpacePair.isOver_snd :
    (affineSpacePair.snd ι k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.condition.symm⟩

instance affineSpacePair.isSeparated_snd : IsSeparated (affineSpacePair.snd ι k₀) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.quasiCompact_snd : QuasiCompact (affineSpacePair.snd ι k₀) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance affineSpacePair.locallyOfFiniteType_snd [Finite ι] :
    LocallyOfFiniteType (affineSpacePair.snd ι k₀) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The standard pairing `⟨-, -⟩ : 𝔸^ι ×_{k₀} 𝔸^ι ⟶ 𝔸¹`, `(x, y) ↦ ∑ᵢ xᵢ yᵢ`, the morphism to
the affine line given by the global function `AlgebraicGeometry.AffineSpace.stdPairing`. -/
noncomputable def affineSpacePair.pairing [Fintype ι] : affineSpacePair ι k₀ ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (affineSpacePair ι k₀ ↘ Spec (CommRingCat.of k₀)) fun _ ↦
    AffineSpace.stdPairing ι (Spec (CommRingCat.of k₀))

instance affineSpacePair.isOver_pairing [Fintype ι] :
    (affineSpacePair.pairing ι k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.homOfVector_over _ _⟩

lemma affineSpacePair.pairing_appTop_coord [Fintype ι] :
    (affineSpacePair.pairing ι k₀).appTop (AffineSpace.coord _ PUnit.unit) =
      ∑ i : ι, (affineSpacePair.fst ι k₀).appTop (AffineSpace.coord _ i) *
        (affineSpacePair.snd ι k₀).appTop (AffineSpace.coord _ i) :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- For `ι = PUnit`, the product `𝔸^ι ×_{k₀} 𝔸^ι` is the affine plane and the standard pairing
is the multiplication `μ : 𝔸¹ ×_{k₀} 𝔸¹ ⟶ 𝔸¹`: a one-term sum is the product. -/
theorem affineSpacePair.pairing_punit :
    affineSpacePair.pairing PUnit.{u + 1} k₀ = affinePlane.mul k₀ := by
  refine congrArg (AffineSpace.homOfVector _) (funext fun _ ↦ ?_)
  rw [AffineSpace.stdPairing, Fintype.sum_unique]
  rfl

end Geometry

section Fourier

variable [Finite k₀] [Fact (ringChar k₀ ≠ l)] [Fintype ι]

/-- The kernel `⟨-, -⟩^* ℒ_ψ` of the Fourier–Deligne transform on `𝔸^ι ×_{k₀} 𝔸^ι`, the
pullback of the Artin–Schreier sheaf along the standard pairing. -/
noncomputable def affineSpaceFourierKernel (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilSheaf k₀ l (affineSpacePair ι k₀) :=
  (WeilSheaf.upperStar (affineSpacePair.pairing ι k₀)).obj (artinSchreier ψ 1)

/-- The kernel of the Fourier–Deligne transform on `𝔸^ι` is lisse, as a pullback of the lisse
Artin–Schreier sheaf. -/
theorem isLisse_affineSpaceFourierKernel (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineSpaceFourierKernel ι ψ).IsLisse :=
  ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreier ψ 1)

/-- The Fourier–Deligne transform `FT_ψ(K) = Rpr₂!(pr₁^* K ⊗ ⟨-, -⟩^* ℒ_ψ)[r]` from Weil
complexes on `𝔸^ι` to Weil complexes on the dual affine space, `r = #ι`, with Laumon's shift by
the relative dimension. It is a triangulated functor between the triangulated categories of
Weil complexes. -/
noncomputable def affineSpaceFourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) :
    WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)) ⥤
      WeilComplex k₀ l 𝔸(ι; Spec (CommRingCat.of k₀)) :=
  WeilComplex.upperStar (affineSpacePair.fst ι k₀) ⋙
    WeilComplex.tensorLisse (affineSpaceFourierKernel ι ψ)
      (isLisse_affineSpaceFourierKernel ι ψ) ⋙
    WeilComplex.derivedLowerShriek k₀ l (affineSpacePair.snd ι k₀) ⋙
    shiftFunctor _ (Fintype.card ι : ℤ)

instance affineSpaceFourierTransform.additive (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineSpaceFourierTransform (l := l) ι ψ).Additive := by
  unfold affineSpaceFourierTransform
  infer_instance

noncomputable instance affineSpaceFourierTransform.commShift (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineSpaceFourierTransform (l := l) ι ψ).CommShift ℤ := by
  unfold affineSpaceFourierTransform
  infer_instance

/-- The Fourier–Deligne transform on `𝔸^ι` is a triangulated functor, as a composite of the
triangulated functors `pr₁^*`, `- ⊗ ⟨-, -⟩^* ℒ_ψ`, `Rpr₂!` and the shift. -/
instance affineSpaceFourierTransform.isTriangulated (ψ : AddChar k₀ (PadicAlgCl l)) :
    (affineSpaceFourierTransform (l := l) ι ψ).IsTriangulated := by
  unfold affineSpaceFourierTransform
  infer_instance

end Fourier

end AlgebraicGeometry
