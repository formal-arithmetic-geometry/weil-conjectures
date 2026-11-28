/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.WeilFourierTransform
import WeilConjectures.WeilSheaf.WeilFourierTransform
import WeilConjectures.FourierTransform.Defs
import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
import WeilConjectures.WeilSheaf.TateTwist
import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
import WeilConjectures.WeilSheaf.FourierInversion.AffineSpaceComposite
import WeilConjectures.WeilSheaf.FourierInversion.AffineSpaceDelta
import WeilConjectures.WeilSheaf.FourierInversion.Reflection
import WeilConjectures.WeilSheaf.TateTwistPullback
import WeilConjectures.WeilSheaf.WeilFourierConvolutionInverseIntegrand
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Fourier inversion on constructible Weil complexes

This file states Fourier inversion for the Fourier transform on an affine space over a finite
field: the composite of the transforms for `ψ` and `ψ⁻¹` is the Tate twist by minus the rank, and
the square of the transform for `ψ` is negation pullback followed by that twist.

Both conclusions are isomorphisms of functors, so their components are Weil-equivariant
and natural in every constructible Weil complex. A finite coordinate type `n` represents
an affine space of arbitrary rank, including rank zero.

## Implementation details

On the triple product with points `(x, ξ, z)`, the composite of the transforms for `ψ` and `ψ'`
is the compact-support integral of `ℒ_{ψ'}(⟨ξ, z⟩) ⊗ ℒ_ψ(⟨x, ξ⟩)`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_affineFourierTransform_comp_affineFourierTransform`).
For `ψ' = ψ⁻¹` the kernel is `ℒ_ψ(∑ᵢ (xᵢ - zᵢ) ξᵢ)`, and the delta kernel on the trivial bundle
`r₁₃`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_sum`)
cuts the integral down to the diagonal `Δ`, the zero locus of `x - z`, with twist `(-r)` and
shift `[-2r]`; `pr₁ ∘ Δ = pr₂ ∘ Δ = id` and the two shifts `[r]` finish the computation.

For `ψ' = ψ` the kernel is `ℒ_ψ(∑ᵢ (xᵢ + zᵢ) ξᵢ)`, whose zero locus is the antidiagonal
`γ = (id, a)` with `a` the negation; then `pr₁ ∘ γ = id`, and `a! ≅ a^*` because `a` is an
involution.

## References

* Laumon, *Transformation de Fourier*, (1.2.2.1)--(1.2.2.3).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

/-- Negation on affine space is a morphism over the base. -/
instance AlgebraicGeometry.AffineSpace.isOver_neg (n : Type u) (S : AlgebraicGeometry.Scheme.{u}) :
    (AffineSpace.neg n S).IsOver S :=
  ⟨AffineSpace.neg_over n S⟩

namespace AlgebraicGeometry.WeilComplex

open AffineSpace

/-- The bookkeeping of Fourier inversion for abstract functors: the integral of the convolution
kernel restricted to a section `γ` of both projections. -/
private theorem nonempty_iso_of_inversion {CV CP CT : Type*} [Category CV] [Category CP]
    [Category CT] {F : CV ⥤ CV} {U₁ : CV ⥤ CP} {U₁₃ : CP ⥤ CT} {TA TB TΦ : CT ⥤ CT}
    {D₁₃ : CT ⥤ CP} {D₂ : CP ⥤ CV} {S tw sh : CV ⥤ CV} {Uγ : CP ⥤ CV} {Dγ : CV ⥤ CP}
    (eK : F ≅ U₁ ⋙ U₁₃ ⋙ TA ⋙ TB ⋙ D₁₃ ⋙ D₂ ⋙ S ⋙ S) (eT : TA ⋙ TB ≅ TΦ)
    (eD : U₁₃ ⋙ TΦ ⋙ D₁₃ ≅ Uγ ⋙ tw ⋙ sh ⋙ Dγ) (eU : U₁ ⋙ Uγ ≅ 𝟭 CV) (eDD : Dγ ⋙ D₂ ≅ 𝟭 CV)
    (eS : sh ⋙ S ⋙ S ≅ 𝟭 CV) : Nonempty (F ≅ tw) := by
  have c₁ : U₁ ⋙ U₁₃ ⋙ TA ⋙ TB ⋙ D₁₃ ⋙ D₂ ⋙ S ⋙ S ≅ U₁ ⋙ (U₁₃ ⋙ TΦ ⋙ D₁₃) ⋙ D₂ ⋙ S ⋙ S :=
    Functor.isoWhiskerLeft (U₁ ⋙ U₁₃) (Functor.isoWhiskerRight eT (D₁₃ ⋙ D₂ ⋙ S ⋙ S))
  have c₂ : U₁ ⋙ (U₁₃ ⋙ TΦ ⋙ D₁₃) ⋙ D₂ ⋙ S ⋙ S ≅ (U₁ ⋙ Uγ) ⋙ tw ⋙ sh ⋙ (Dγ ⋙ D₂) ⋙ S ⋙ S :=
    Functor.isoWhiskerLeft U₁ (Functor.isoWhiskerRight eD (D₂ ⋙ S ⋙ S))
  have c₃ : (U₁ ⋙ Uγ) ⋙ tw ⋙ sh ⋙ (Dγ ⋙ D₂) ⋙ S ⋙ S ≅ tw :=
    Functor.isoWhiskerRight eU (tw ⋙ sh ⋙ (Dγ ⋙ D₂) ⋙ S ⋙ S) ≪≫ Functor.leftUnitor _ ≪≫
      Functor.isoWhiskerLeft tw (Functor.isoWhiskerLeft sh
        (Functor.isoWhiskerRight eDD (S ⋙ S) ≪≫ Functor.leftUnitor _) ≪≫ eS) ≪≫
      Functor.rightUnitor tw
  exact ⟨eK ≪≫ c₁ ≪≫ c₂ ≪≫ c₃⟩

/-- The bookkeeping of the second inversion formula for abstract functors: the integral of the
convolution kernel restricted to the graph `γ` of an automorphism. -/
private theorem nonempty_iso_of_inversion_comp {CV CP CT : Type*} [Category CV] [Category CP]
    [Category CT] {F : CV ⥤ CV} {U₁ : CV ⥤ CP} {U₁₃ : CP ⥤ CT} {TA TB TΦ : CT ⥤ CT}
    {D₁₃ : CT ⥤ CP} {D₂ : CP ⥤ CV} {S tw sh N : CV ⥤ CV} {Uγ : CP ⥤ CV} {Dγ : CV ⥤ CP}
    (eK : F ≅ U₁ ⋙ U₁₃ ⋙ TA ⋙ TB ⋙ D₁₃ ⋙ D₂ ⋙ S ⋙ S) (eT : TA ⋙ TB ≅ TΦ)
    (eD : U₁₃ ⋙ TΦ ⋙ D₁₃ ≅ Uγ ⋙ tw ⋙ sh ⋙ Dγ) (eU : U₁ ⋙ Uγ ≅ 𝟭 CV) (eDD : Dγ ⋙ D₂ ≅ N)
    (cs : sh ⋙ N ≅ N ⋙ sh) (ct : tw ⋙ N ≅ N ⋙ tw) (eS : sh ⋙ S ⋙ S ≅ 𝟭 CV) :
    Nonempty (F ≅ N ⋙ tw) := by
  have c₁ : U₁ ⋙ U₁₃ ⋙ TA ⋙ TB ⋙ D₁₃ ⋙ D₂ ⋙ S ⋙ S ≅ U₁ ⋙ (U₁₃ ⋙ TΦ ⋙ D₁₃) ⋙ D₂ ⋙ S ⋙ S :=
    Functor.isoWhiskerLeft (U₁ ⋙ U₁₃) (Functor.isoWhiskerRight eT (D₁₃ ⋙ D₂ ⋙ S ⋙ S))
  have c₂ : U₁ ⋙ (U₁₃ ⋙ TΦ ⋙ D₁₃) ⋙ D₂ ⋙ S ⋙ S ≅ (U₁ ⋙ Uγ) ⋙ tw ⋙ sh ⋙ (Dγ ⋙ D₂) ⋙ S ⋙ S :=
    Functor.isoWhiskerLeft U₁ (Functor.isoWhiskerRight eD (D₂ ⋙ S ⋙ S))
  have c₃ : (U₁ ⋙ Uγ) ⋙ tw ⋙ sh ⋙ (Dγ ⋙ D₂) ⋙ S ⋙ S ≅ tw ⋙ (sh ⋙ N) ⋙ S ⋙ S :=
    Functor.isoWhiskerRight eU (tw ⋙ sh ⋙ (Dγ ⋙ D₂) ⋙ S ⋙ S) ≪≫ Functor.leftUnitor _ ≪≫
      Functor.isoWhiskerLeft (tw ⋙ sh) (Functor.isoWhiskerRight eDD (S ⋙ S))
  have c₄ : tw ⋙ (sh ⋙ N) ⋙ S ⋙ S ≅ N ⋙ tw :=
    Functor.isoWhiskerLeft tw (Functor.isoWhiskerRight cs (S ⋙ S)) ≪≫
      Functor.isoWhiskerRight ct (sh ⋙ S ⋙ S) ≪≫
      Functor.isoWhiskerLeft (N ⋙ tw) eS ≪≫ Functor.rightUnitor _
  exact ⟨eK ≪≫ c₁ ≪≫ c₂ ≪≫ c₃ ≪≫ c₄⟩

/-- Shifting by `-2r` and then twice by `r` is the identity. -/
private noncomputable def shiftFunctorNegTwoMulCompIso {C : Type*} [Category C]
    [HasShift C ℤ] (r : ℤ) :
    shiftFunctor C (-(2 * r)) ⋙ shiftFunctor C r ⋙ shiftFunctor C r ≅ 𝟭 C :=
  Functor.isoWhiskerRight (shiftFunctorAdd' C (-(2 * r)) r (-r) (by ring)).symm
      (shiftFunctor C r) ≪≫ shiftFunctorCompIsoId C (-r) r (by ring)

/-- Fourier inversion with the inverse additive character: `F_{ψ⁻¹} ∘ F_ψ` is the Tate twist by
`-r`, where `r` is the rank of the affine space, naturally in the Weil complex. -/
theorem nonempty_iso_affineFourierTransform_comp_inv
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n]
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (affineFourierTransform k₀ l n ψ ⋙ affineFourierTransform k₀ l n ψ⁻¹ ≅
      tateTwist k₀ l (AffineSpace n (Spec (CommRingCat.of k₀))) (-(Fintype.card n : ℤ))) := by
  let S₀ := Spec (CommRingCat.of k₀)
  let πV := 𝔸(n; S₀) ↘ S₀
  let pr₁ := pullback.fst πV πV
  let pr₂ := pullback.snd πV πV
  let r₁₂ := pullback.fst pr₂ pr₁
  let r₂₃ := pullback.snd pr₂ pr₁
  let r₁₃ := pullback.tripleProj₁₃ πV πV πV
  let Δ := pullback.diagonal πV
  have : (sub n S₀).IsOver S₀ := ⟨(sub_over n S₀).trans pullback.condition⟩
  have : Δ.IsOver S₀ := ⟨pullback.diagonal_snd_assoc _ _⟩
  obtain ⟨eK⟩ := nonempty_iso_affineFourierTransform_comp_affineFourierTransform (l := l) n ψ ψ⁻¹
  obtain ⟨eSub⟩ := nonempty_iso_tensorLisse_artinSchreierOf_sub (l := l) ψ
    (r₁₂.appTop (stdPairing n S₀)) (r₂₃.appTop (stdPairing n S₀))
  obtain ⟨eΦ⟩ := nonempty_iso_tensorLisse_of_iso
    (eqToIso (congrArg (artinSchreierOf ψ) (appTop_stdPairing_sub_appTop_stdPairing n S₀)))
    (isLisse_artinSchreierOf ψ _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eD⟩ := nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_sum (l := l) ψ hψ n
    (sub n S₀) r₁₃ (r₁₂ ≫ pr₂) (isPullback_tripleProj₁₃ n S₀) Δ (isPullback_diagonal_sub n S₀)
  obtain ⟨dΔ⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) Δ pr₂
  obtain ⟨dId⟩ := nonempty_iso_derivedLowerShriek_id (k₀ := k₀) (l := l) (X := 𝔸(n; S₀))
  exact nonempty_iso_of_inversion eK (eSub ≪≫ eΦ) eD
    ((upperStarCompIso Δ pr₁).symm ≪≫ upperStarCongrIso (pullback.diagonal_fst πV) ≪≫
      upperStarIdIso _)
    (dΔ.symm ≪≫ derivedLowerShriekIsoOfEq (pullback.diagonal_snd πV) ≪≫ dId)
    (shiftFunctorNegTwoMulCompIso _)

/-- The same-character Fourier square is negation pullback followed by the rank Tate twist
`(-r)`, naturally in the Weil complex. -/
theorem nonempty_iso_affineFourierTransform_comp_self
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n]
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (affineFourierTransform k₀ l n ψ ⋙ affineFourierTransform k₀ l n ψ ≅
      upperStar (l := l) (AffineSpace.neg n (Spec (CommRingCat.of k₀))) ⋙
        tateTwist k₀ l (AffineSpace n (Spec (CommRingCat.of k₀))) (-(Fintype.card n : ℤ))) := by
  let S₀ := Spec (CommRingCat.of k₀)
  let πV := 𝔸(n; S₀) ↘ S₀
  let pr₁ := pullback.fst πV πV
  let pr₂ := pullback.snd πV πV
  let r₁₂ := pullback.fst pr₂ pr₁
  let r₂₃ := pullback.snd pr₂ pr₁
  let r₁₃ := pullback.tripleProj₁₃ πV πV πV
  let γ := pullback.diagonal πV ≫ prodNeg n S₀
  have : (add n S₀).IsOver S₀ := ⟨(add_over n S₀).trans pullback.condition⟩
  have : (prodNeg n S₀).IsOver S₀ := ⟨by
    change prodNeg n S₀ ≫ pr₂ ≫ πV = pr₂ ≫ πV
    rw [prodNeg_snd_assoc, neg_over]⟩
  have : (pullback.diagonal πV).IsOver S₀ := ⟨pullback.diagonal_snd_assoc _ _⟩
  have : IsClosedImmersion γ :=
    MorphismProperty.of_isPullback (isPullback_diagonal_prodNeg_add n S₀) inferInstance
  have hγ₁ : γ ≫ pr₁ = 𝟙 _ := by
    change pullback.diagonal (𝔸(n; S₀) ↘ S₀) ≫ prodNeg n S₀ ≫
      pullback.fst (𝔸(n; S₀) ↘ S₀) (𝔸(n; S₀) ↘ S₀) = _
    simp
  have hγ₂ : γ ≫ pr₂ = neg n S₀ := by
    change pullback.diagonal (𝔸(n; S₀) ↘ S₀) ≫ prodNeg n S₀ ≫
      pullback.snd (𝔸(n; S₀) ↘ S₀) (𝔸(n; S₀) ↘ S₀) = _
    simp
  have : IsIso (neg n S₀) := ⟨⟨neg n S₀, neg_comp_neg n S₀, neg_comp_neg n S₀⟩⟩
  let negIso : 𝔸(n; S₀) ≅ 𝔸(n; S₀) := ⟨neg n S₀, neg n S₀, neg_comp_neg n S₀, neg_comp_neg n S₀⟩
  have : negIso.hom.IsOver S₀ := isOver_neg n S₀
  have : negIso.inv.IsOver S₀ := isOver_neg n S₀
  obtain ⟨eK⟩ := nonempty_iso_affineFourierTransform_comp_affineFourierTransform (l := l) n ψ ψ
  obtain ⟨eAdd⟩ := nonempty_iso_tensorLisse_artinSchreierOf_add (l := l) ψ
    (r₁₂.appTop (stdPairing n S₀)) (r₂₃.appTop (stdPairing n S₀))
  obtain ⟨eΦ⟩ := nonempty_iso_tensorLisse_of_iso
    (eqToIso (congrArg (artinSchreierOf ψ) (appTop_stdPairing_add_appTop_stdPairing n S₀)))
    (isLisse_artinSchreierOf ψ _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eD⟩ := nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_sum (l := l) ψ hψ n
    (add n S₀) r₁₃ (r₁₂ ≫ pr₂) (isPullback_tripleProj₁₃ n S₀) γ
    (isPullback_diagonal_prodNeg_add n S₀)
  obtain ⟨dγ⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) γ pr₂
  obtain ⟨dNeg⟩ := nonempty_iso_derivedLowerShriek_hom_upperStar_inv (k₀ := k₀) (l := l) negIso
  exact nonempty_iso_of_inversion_comp eK (eAdd ≪≫ eΦ) eD
    ((upperStarCompIso γ pr₁).symm ≪≫ upperStarCongrIso hγ₁ ≪≫ upperStarIdIso _)
    (dγ.symm ≪≫ derivedLowerShriekIsoOfEq hγ₂ ≪≫ dNeg)
    ((upperStar (neg n S₀)).commShiftIso _) (tateTwistCompUpperStarIso (neg n S₀) _)
    (shiftFunctorNegTwoMulCompIso _)

end AlgebraicGeometry.WeilComplex
