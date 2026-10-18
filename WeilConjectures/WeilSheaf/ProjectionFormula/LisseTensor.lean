/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.WeilSheaf.TensorHomAdjunction

/-!
# The tensor product with a lisse sheaf is exact

For a lisse sheaf `L` of `ℚ̄_ℓ,X`-modules, the tensor product `- ⊗ L` is exact
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesFiniteLimits_tensorLeft`): it is right
exact as a left adjoint, and it preserves monomorphisms since this can be checked after pullback
along the members of a pro-étale cover trivialising `L`, where `L` becomes `ℚ̄_ℓⁿ` and
`- ⊗ ℚ̄_ℓⁿ = (-)ⁿ` (`CategoryTheory.Mod.mono_tensorLeft_map_of_iso_biproduct`). The same holds for
the tensor product with a pro-étale Weil sheaf with lisse underlying sheaf
(`AlgebraicGeometry.ProEtaleWeilSheaf.preservesFiniteLimits_tensorFunctor`), so that the internal
hom out of it preserves K-injective complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.preservesKInjectiveComplexes_ihomFunctor`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] {A : C}
  [MonObj A] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]

attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

/-- `- ⊗_A M` as an additive map in `M`. -/
@[simps]
noncomputable def tensorLeftMapAddHom (M M' : Mod C A) :
    (M ⟶ M') →+ (tensorLeft M ⟶ tensorLeft M') where
  toFun := tensorLeftMap
  map_zero' := by
    have h := tensorLeftMap_add (0 : M ⟶ M') 0
    rwa [add_zero, left_eq_add] at h
  map_add' := tensorLeftMap_add

lemma sum_tensorLeftMap_π_comp_tensorLeftMap_ι {n : ℕ} (M : Fin n → Mod C A) :
    ∑ i, tensorLeftMap (biproduct.π M i) ≫ tensorLeftMap (biproduct.ι M i) =
      𝟙 (tensorLeft (⨁ M)) := by
  simp_rw [← tensorLeftMap_comp]
  calc ∑ i, tensorLeftMap (biproduct.π M i ≫ biproduct.ι M i) =
      tensorLeftMapAddHom (⨁ M) (⨁ M) (∑ i, biproduct.π M i ≫ biproduct.ι M i) := by
        rw [map_sum]; rfl
    _ = 𝟙 _ := by rw [biproduct.total]; exact tensorLeftMap_id _

/-- `- ⊗_A ⨁ᵢ Mᵢ` preserves monomorphisms if each `- ⊗_A Mᵢ` does. -/
lemma mono_tensorLeft_biproduct_map {n : ℕ} (M : Fin n → Mod C A) {N N' : Mod C A}
    (f : N ⟶ N') (h : ∀ i, Mono ((tensorLeft (M i)).map f)) :
    Mono ((tensorLeft (⨁ M)).map f) := by
  refine Preadditive.mono_of_cancel_zero _ fun {Z} g hg ↦ ?_
  have htot := sum_tensorLeftMap_π_comp_tensorLeftMap_ι M
  have hi (i : Fin n) : g ≫ (tensorLeftMap (biproduct.π M i)).app N = 0 := by
    have := h i
    rw [← cancel_mono ((tensorLeft (M i)).map f), Category.assoc,
      ← (tensorLeftMap (biproduct.π M i)).naturality, ← Category.assoc, hg, zero_comp,
      zero_comp]
  rw [← Category.comp_id g, ← NatTrans.id_app, ← htot, NatTrans.app_sum, Preadditive.comp_sum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [NatTrans.comp_app, ← Category.assoc, hi, zero_comp]

/-- `- ⊗_A M` preserves monomorphisms for `M` free of finite rank. -/
lemma mono_tensorLeft_map_of_iso_biproduct {M : Mod C A} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ regular A) {N N' : Mod C A} (f : N ⟶ N') [Mono f] :
    Mono ((tensorLeft M).map f) := by
  have : Mono ((tensorLeft (⨁ fun _ : Fin n ↦ regular A)).map f) :=
    mono_tensorLeft_biproduct_map _ f fun _ ↦ by
      rw [← NatIso.naturality_2 tensorLeftRegularIso f]
      infer_instance
  rw [← NatIso.naturality_2 (tensorLeftMapIso e) f]
  infer_instance

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- **The tensor product with a lisse sheaf preserves monomorphisms**: after pullback along a
member `g` of a pro-étale cover trivialising `F`, it becomes the tensor product with `ℚ̄_ℓⁿ`. -/
theorem IsAdicLisseSheaf.mono_tensorLeft_map {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F)
    {M N : AdicSheaf l X} (f : M ⟶ N) [Mono f] : Mono ((Mod.tensorLeft F).map f) := by
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine Preadditive.mono_of_isZero_kernel _
    (AdicSheaf.isZero_of_isZero_upperStar g hR fun i ↦ ?_)
  obtain ⟨n, ⟨e⟩⟩ := hRF (g i) (.mk i)
  have : Mono ((g i)^*ᵃ[l].map ((Mod.tensorLeft F).map f)) := by
    have key := NatIso.naturality_2 (adicUpperStarTensorLeftIso l (g i) F) f
    rw [← Functor.comp_map, ← key]
    have := Mod.mono_tensorLeft_map_of_iso_biproduct e ((g i)^*ᵃ[l].map f)
    exact mono_comp' inferInstance (mono_comp' this inferInstance)
  exact (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (g i)^*ᵃ[l] _)

/-- **The tensor product with a lisse sheaf is exact**: it is right exact as a left adjoint and
preserves monomorphisms (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.mono_tensorLeft_map`). -/
theorem IsAdicLisseSheaf.preservesFiniteLimits_tensorLeft {F : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) : PreservesFiniteLimits (Mod.tensorLeft F) := by
  have := (Mod.ihomAdjunction F).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (Mod.tensorLeft F) := inferInstance
  have : (Mod.tensorLeft F).PreservesZeroMorphisms := inferInstance
  have : PreservesBinaryBiproducts (Mod.tensorLeft F) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (Mod.tensorLeft F).Additive := Functor.additive_of_preservesBinaryBiproducts _
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun S hS ↦ ?_
  have := hS.mono_f
  have h := (Functor.preservesFiniteColimits_tfae (Mod.tensorLeft F)).out 3 0
  exact ⟨(h.1 ‹_› S hS).1, hF.mono_tensorLeft_map S.f⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- The tensor product with a pro-étale Weil sheaf, followed by the forgetful functor, is the
tensor product of the underlying sheaves. -/
noncomputable def tensorFunctorCompForgetIso (A : ProEtaleWeilSheaf k₀ l X) :
    tensorFunctor k₀ l X A ⋙ IsoAlgebra.forget _ ≅
      IsoAlgebra.forget _ ⋙ Mod.tensorLeft A.carrier :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The tensor product with a pro-étale Weil sheaf is right exact, being a left adjoint. -/
instance (A : ProEtaleWeilSheaf k₀ l X) : PreservesFiniteColimits (tensorFunctor k₀ l X A) :=
  have : (tensorFunctor k₀ l X A).IsLeftAdjoint := (tensorIhomAdjunction k₀ l X A).isLeftAdjoint
  inferInstance

/-- The tensor product with a pro-étale Weil sheaf is additive. -/
instance (A : ProEtaleWeilSheaf k₀ l X) : (tensorFunctor k₀ l X A).Additive :=
  have : (tensorFunctor k₀ l X A).IsLeftAdjoint := (tensorIhomAdjunction k₀ l X A).isLeftAdjoint
  have : (tensorFunctor k₀ l X A).PreservesZeroMorphisms := inferInstance
  have : PreservesBinaryBiproducts (tensorFunctor k₀ l X A) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The tensor product with a pro-étale Weil sheaf with lisse underlying sheaf is exact
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesFiniteLimits_tensorLeft`). -/
theorem preservesFiniteLimits_tensorFunctor (A : ProEtaleWeilSheaf k₀ l X)
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) :
    PreservesFiniteLimits (tensorFunctor k₀ l X A) := by
  have := hA.preservesFiniteLimits_tensorLeft
  have : PreservesFiniteLimits (tensorFunctor k₀ l X A ⋙ IsoAlgebra.forget _) :=
    preservesFiniteLimits_of_natIso (tensorFunctorCompForgetIso k₀ l X A).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (IsoAlgebra.forget _)

/-- The internal hom out of a pro-étale Weil sheaf with lisse underlying sheaf preserves
K-injective complexes: its left adjoint, the tensor product, is exact. -/
theorem preservesKInjectiveComplexes_ihomFunctor (A : ProEtaleWeilSheaf k₀ l X)
    (hA : ProEtale.IsAdicLisseSheaf A.carrier) :
    (ihomFunctor k₀ l X A).PreservesKInjectiveComplexes :=
  have := preservesFiniteLimits_tensorFunctor A hA
  (tensorIhomAdjunction k₀ l X A).preservesKInjectiveComplexes

end AlgebraicGeometry.ProEtaleWeilSheaf
