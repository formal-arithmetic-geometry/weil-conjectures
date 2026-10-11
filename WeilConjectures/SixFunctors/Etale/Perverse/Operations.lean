/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeHomology
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Flat
public import WeilConjectures.SixFunctors.Etale.Perverse.Basic

/-!
# The perverse classes under the operations

This file records how the perverse classes `ᵖD^{≤n}` and `ᵖD^{≥n}` of
`WeilConjectures.SixFunctors.Etale.Perverse.Basic` behave under the tensor product with a
lisse sheaf, under smooth pullback and under compactly supported pushforward along an affine
morphism. Together they bound the perverse amplitude of the Fourier–Deligne transform, see
`WeilConjectures.FourierTransform.Perverse`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.IsLisse`: a lisse complex of finite rank, a locally
  constant sheaf placed in degree zero which is dualizable and constructible of finite Tor
  amplitude.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_verdierDual_tensor`: the Verdier dual
  of a tensor product with a dualizable complex, `𝔻(K ⊗ᴸ L) ≅ L^∨ ⊗ᴸ 𝔻K`
  (blueprint `lem-per-dual-lisse-tensor`).
- `AlgebraicGeometry.Etale.DerivedCategory.isPerverseLE_tensor`,
  `AlgebraicGeometry.Etale.DerivedCategory.isPerverseGE_tensor`: permanence of the perverse
  classes under a lisse tensor (blueprint `lem-per-lisse-tensor-permanence`).
- `AlgebraicGeometry.Etale.DerivedCategory.isPerverseLE_upperStar`,
  `AlgebraicGeometry.Etale.DerivedCategory.isPerverseGE_upperStar`: smooth pullback is
  perverse up to the shift by the relative dimension
  (blueprint `lem-per-smooth-pullback-t-exact`).
- `AlgebraicGeometry.Etale.DerivedCategory.isPerverseLE_lowerShriek`,
  `AlgebraicGeometry.Etale.DerivedCategory.isPerverseGE_lowerShriek`: Artin–Gabber, the
  compactly supported pushforward along an affine morphism with fibres of dimension at most `d`
  has perverse amplitude `d` (blueprint `lem-per-artin-gabber-affine-curve`).

## Implementation notes

The blueprint states the lemmas on `ᵖD^{≤0}` and `ᵖD^{≥0}` and notes that the shifted
classes follow, the functors commuting with shifts. The smooth pullback and Artin–Gabber
lemmas are stated for every `ᵖD^{≤n}` and `ᵖD^{≥n}` directly, since the shifted
constructibility hypotheses would need the stability of `Dctf` under shifts, which the
repository does not record. For the lisse tensor the shifted statements are derived
from the unshifted support estimate, the tensor product commuting with shifts
(`AlgebraicGeometry.Etale.DerivedCategory.shiftTensorIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.DerivedCategory

section Tensor

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X S : Scheme.{u}}

/-- The derived tensor product commutes with shifts: `K[n] ⊗ᴸ L ≅ (K ⊗ᴸ L)[n]`. -/
noncomputable def shiftTensorIso
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (n : ℤ) : K⟦n⟧ ⊗ L ≅ (K ⊗ L)⟦n⟧ :=
  (((derivedTensor _ X).flip.obj L).commShiftIso n).app K

variable (a : X ⟶ S) [HasCompactification a] [(R(a)_![A]).IsLeftAdjoint]

/-- **Dual of a lisse tensor.** For a dualizable complex `L`, with coefficient dual `L^∨`,
the Verdier dual of `K ⊗ᴸ L` is `L^∨ ⊗ᴸ 𝔻K`: the tensor–hom adjunction gives
`RHom(K ⊗ᴸ L, ω) ≅ RHom(L, RHom(K, ω))`, and the internal hom out of the dualizable `L` is the
tensor product with `L^∨`. The blueprint writes the factors in the other order.
(blueprint: `lem-per-dual-lisse-tensor`) -/
theorem nonempty_iso_verdierDual_tensor
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (hL : IsDualizable L) :
    Nonempty ((verdierDual A a).obj (op (K ⊗ L)) ≅
      (coefficientDual A X).obj (op L) ⊗
        (verdierDual A a).obj (op K)) := by
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor hL
    ((verdierDual A a).obj (op K))
  have adj : tensorLeft (K ⊗ L) ⊣ ihom K ⋙ ihom L :=
    ((ihom.adjunction L).comp (ihom.adjunction K)).ofNatIsoLeft (tensorLeftTensor K L).symm
  exact ⟨((ihom.adjunction (K ⊗ L)).rightAdjointUniq adj).app
    (dualizingComplex A a) ≪≫ e.symm⟩

variable {a}

/-- Tensoring with a complex of Tor amplitude in `[0, 0]` preserves the vanishing of a
cohomology sheaf on an open: `L ⊗ᴸ -` commutes with the restriction to the open and is
t-exact there. -/
lemma isZero_upperStar_homologyFunctor_tensor
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hL : torAmplitudeIn A X 0 0 L)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (n : ℤ) (U : X.Opens)
    (hK : IsZero (((U.ι)^*[A]).obj ((_root_.DerivedCategory.homologyFunctor _ n).obj K))) :
    IsZero (((U.ι)^*[A]).obj ((_root_.DerivedCategory.homologyFunctor _ n).obj (L ⊗ K))) := by
  have hL' := torAmplitudeIn_leftDerivedUpperStar A U.ι 0 0 hL
  have hK' := hK.of_iso ((leftDerivedUpperStarHomologyFunctorIso A U.ι n).app K).symm
  refine (_root_.DerivedCategory.isZero_homologyFunctor_tensor_of_torAmplitudeIn hL' _ n
    hK').of_iso ?_
  exact (leftDerivedUpperStarHomologyFunctorIso A U.ι n).app (L ⊗ K) ≪≫
    (_root_.DerivedCategory.homologyFunctor _ n).mapIso (leftDerivedUpperStarTensorIso A U.ι L K)

/-- The support estimate behind `lem-per-lisse-tensor-permanence`: tensoring, on either side,
with a complex of Tor amplitude in `[0, 0]` (for instance a lisse complex) preserves the support
condition, the cohomology sheaves of `K ⊗ᴸ L` being supported in those of `K`.
(blueprint: `lem-per-lisse-tensor-permanence`) -/
theorem SupportCondition.tensor
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : SupportCondition K) (hL : torAmplitudeIn A X 0 0 L) :
    SupportCondition (K ⊗ L) ∧ SupportCondition (L ⊗ K) := by
  have h : SupportCondition (L ⊗ K) := hK.of_sheafSupport_subset fun i ↦
    sheafSupport_subset_of_isZero fun U ↦ isZero_upperStar_homologyFunctor_tensor hL K (-i) U
  obtain ⟨β⟩ := nonempty_iso_derivedTensor_flip A X
  exact ⟨h.of_iso ((β.app L).app K), h⟩

/-- The coefficient dual of a dualizable complex of Tor amplitude in `[0, 0]` has Tor amplitude
in `[0, 0]`. -/
theorem torAmplitudeIn_coefficientDual
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hL : IsDualizable L)
    (hL' : torAmplitudeIn A X 0 0 L) :
    torAmplitudeIn A X 0 0 ((coefficientDual A X).obj (op L)) := by
  obtain ⟨_⟩ := hL
  obtain ⟨_⟩ := nonempty_exactPairing_swap L Lᘁ
  exact (torAmplitudeIn A X 0 0).prop_of_iso (coefficientDualIsoOfExactPairing Lᘁ L).symm
    (_root_.DerivedCategory.torAmplitudeIn_of_exactPairing (K := L) (L := Lᘁ) hL')

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- A complex `L` on `X` is *lisse of finite rank* if it is a locally constant sheaf placed in
degree zero which is dualizable, bounded constructible and of Tor amplitude in `[0, 0]`: étale
locally a finite projective coefficient module. The Tor amplitude `[0, 0]` makes the stalks flat;
without it a dualizable sheaf in degree zero need not have its dual in degree zero (over `ℤ`,
the constant sheaf `ℤ/ℓ` is dualizable with dual `ℤ/ℓ[-1]`). -/
def IsLisse (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Prop :=
  IsDualizable L ∧ constructibleFiniteTor A X L ∧ torAmplitudeIn A X 0 0 L ∧
    ∃ L₀ : Sheaf X.smallEtaleTopology A, Scheme.IsLocallyConstantSheaf L₀ ∧
      Nonempty (L ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj L₀)

/-- **Permanence under a lisse tensor**, support side: `K ∈ ᵖD^{≤n}` implies
`K ⊗ᴸ L ∈ ᵖD^{≤n}` for a lisse `L`. (blueprint: `lem-per-lisse-tensor-permanence`) -/
theorem isPerverseLE_tensor {n : ℤ}
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : IsPerverseLE n K) (hL : IsLisse L) : IsPerverseLE n (K ⊗ L) :=
  (SupportCondition.tensor hK hL.2.2.1).1.of_iso (shiftTensorIso K L n)

/-- **Permanence under a lisse tensor**, cosupport side: `K ∈ ᵖD^{≥n}` implies
`K ⊗ᴸ L ∈ ᵖD^{≥n}` for a lisse `L`: by `lem-per-dual-lisse-tensor` the Verdier dual of
`K[n] ⊗ᴸ L` is `L^∨ ⊗ᴸ 𝔻(K[n])`, and `L^∨` again has Tor amplitude in `[0, 0]`.
(blueprint: `lem-per-lisse-tensor-permanence`) -/
theorem isPerverseGE_tensor {n : ℤ}
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : IsPerverseGE a n K) (hL : IsLisse L) : IsPerverseGE a n (K ⊗ L) :=
  CosupportCondition.of_iso (shiftTensorIso K L n)
    ((SupportCondition.tensor hK (torAmplitudeIn_coefficientDual hL.1 hL.2.2.1)).2.of_iso
      (nonempty_iso_verdierDual_tensor a _ L hL.1).some.symm)

end Tensor

section Pullback

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]
variable {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [IsSeparated aY]
  [QuasiCompact aY] [HasCompactification aY]

include aY in
/-- **Smooth pullback is perverse up to the shift**, support side: for a smooth morphism
`f : X ⟶ Y` of relative dimension `d` between separated schemes of finite type over `k`, the
pullback carries `ᵖD^{≤n}(Y)` into `ᵖD^{≤n+d}(X)`; that is, `f^*[d]` preserves `ᵖD^{≤n}`.
(blueprint: `lem-per-smooth-pullback-t-exact`) -/
theorem isPerverseLE_upperStar (d : ℕ) (f : X ⟶ Y) [SmoothOfRelativeDimension d f] {n : ℤ}
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsPerverseLE n K) :
    IsPerverseLE (n + d) ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  -- TODO(adic): the support of a pullback is the preimage, of dimension raised by `d`
  sorry

/-- **Smooth pullback is perverse up to the shift**, cosupport side: for `f` smooth of
relative dimension `d`, the pullback carries `ᵖD^{≥n}(Y) ∩ Dctf(Y)` into `ᵖD^{≥n+d}(X)`, by
the Verdier exchange `𝔻_X f^* ≅ f^! 𝔻_Y` and smooth purity `f^! ≅ f^*(d)[2d]`.
(blueprint: `lem-per-smooth-pullback-t-exact`) -/
theorem isPerverseGE_upperStar (d : ℕ) (f : X ⟶ Y) [SmoothOfRelativeDimension d f]
    [HasCompactification (f ≫ aY)] {n : ℤ}
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsPerverseGE aY n K) (hK' : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    IsPerverseGE (f ≫ aY) (n + d) ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  -- TODO(adic): Verdier exchange for `f` and smooth purity
  sorry

end Pullback

section LowerShriek

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]
variable {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [IsSeparated aY]
  [QuasiCompact aY] [HasCompactification aY]

include aY in
/-- **Artin–Gabber**, support side: for an affine morphism `f : X ⟶ Y` of finite type between
separated schemes of finite type over `k`, whose fibres have dimension at most `d`, the
compactly supported pushforward carries `ᵖD^{≤n}(X) ∩ Dctf(X)` into `ᵖD^{≤n+d}(Y)`.
(blueprint: `lem-per-artin-gabber-affine-curve`) -/
theorem isPerverseLE_lowerShriek (d : ℕ) (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f]
    [HasCompactification f] [QuasiCompact f]
    (hf : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : ℕ∞)) {n : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsPerverseLE n K) (hK' : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsPerverseLE (n + d) ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) :=
  -- TODO(adic): the fibrewise cohomological dimension bound and the generating blocks
  sorry

/-- **Artin–Gabber**, cosupport side: under the hypotheses of `isPerverseLE_lowerShriek`, the
compactly supported pushforward carries `ᵖD^{≥n}(X) ∩ Dctf(X)` into `ᵖD^{≥n-d}(Y)`, by Verdier
exchange `𝔻_Y Rf_! ≅ Rf_* 𝔻_X` and the support estimate for `Rf_*`.
(blueprint: `lem-per-artin-gabber-affine-curve`) -/
theorem isPerverseGE_lowerShriek (d : ℕ) (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f]
    [HasCompactification f] [QuasiCompact f] [HasCompactification (f ≫ aY)]
    (hf : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : ℕ∞)) {n : ℤ}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsPerverseGE (f ≫ aY) n K) (hK' : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsPerverseGE aY (n - d) ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) :=
  -- TODO(adic): Verdier exchange and the support estimate for `Rf_*`
  sorry

end LowerShriek

end AlgebraicGeometry.Etale.DerivedCategory
