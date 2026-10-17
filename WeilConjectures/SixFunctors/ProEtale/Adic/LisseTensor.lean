/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom

/-!
# Lisse `ℓ`-adic sheaves are flat

The tensor product `- ⊗_{ℚ̄_ℓ,X} C` with a lisse sheaf `C` preserves monomorphisms
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesMonomorphisms_tensorLeft`). Indeed, this
can be checked after pullback along the members of a pro-étale cover trivialising `C`, pullback
commuting with tensor products; and the tensor product with a finite free module preserves
monomorphisms (`CategoryTheory.Mod.preservesMonomorphisms_tensorLeft_of_iso_biproduct`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C] {A : C} [MonObj A] [BraidedCategory C]
  [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

/-- The tensor product `- ⊗_A M` as an additive function of `M`. -/
noncomputable def tensorLeftMapAddHom (M : Mod C A) : (M ⟶ M) →+ (tensorLeft M ⟶ tensorLeft M) where
  toFun := tensorLeftMap
  map_zero' := by
    have h := tensorLeftMap_add (0 : M ⟶ M) 0
    rw [add_zero] at h
    have h' := congrArg (· - tensorLeftMap (0 : M ⟶ M)) h
    simpa using h'.symm
  map_add' := tensorLeftMap_add

/-- **The tensor product with a finite free module preserves monomorphisms.** -/
theorem preservesMonomorphisms_tensorLeft_of_iso_biproduct {M : Mod C A} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ regular A) : (tensorLeft M).PreservesMonomorphisms := by
  refine ⟨fun {P Q} f _ ↦ Preadditive.mono_of_cancel_zero _ fun {T} x hx ↦ ?_⟩
  set π : Fin n → (M ⟶ regular A) := fun j ↦ e.hom ≫ biproduct.π (fun _ : Fin n ↦ regular A) j
  set ι : Fin n → (regular A ⟶ M) := fun j ↦ biproduct.ι (fun _ : Fin n ↦ regular A) j ≫ e.inv
  have htot : ∑ j, π j ≫ ι j = 𝟙 M := by
    calc ∑ j, π j ≫ ι j = ∑ j, e.hom ≫ ((biproduct.π (fun _ : Fin n ↦ regular A) j ≫
          biproduct.ι (fun _ : Fin n ↦ regular A) j) ≫ e.inv) := by
          simp only [π, ι, Category.assoc]
      _ = e.hom ≫ ((∑ j, biproduct.π (fun _ : Fin n ↦ regular A) j ≫
          biproduct.ι (fun _ : Fin n ↦ regular A) j) ≫ e.inv) := by
          rw [Preadditive.sum_comp, Preadditive.comp_sum]
      _ = 𝟙 M := by rw [biproduct.total, Category.id_comp, e.hom_inv_id]
  have hmono : Mono ((tensorLeft (regular A)).map f) := by
    have h : (tensorLeft (regular A)).map f =
        (tensorLeftRegularIso (A := A)).hom.app P ≫ f ≫ (tensorLeftRegularIso (A := A)).inv.app Q := by
      rw [← NatIso.naturality_2 (tensorLeftRegularIso (A := A)) f]
      simp
    rw [h]
    infer_instance
  have hj (j : Fin n) : x ≫ (tensorLeftMap (π j)).app P = 0 := by
    rw [← cancel_mono ((tensorLeft (regular A)).map f), Category.assoc,
      ← (tensorLeftMap (π j)).naturality f, reassoc_of% hx, zero_comp, zero_comp]
  have h1 : x = x ≫ (tensorLeftMap (𝟙 M)).app P := by
    rw [tensorLeftMap_id]
    exact (Category.comp_id x).symm
  rw [h1, ← htot]
  change x ≫ (tensorLeftMapAddHom M (∑ j, π j ≫ ι j)).app P = 0
  rw [map_sum, NatTrans.app_sum, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  change x ≫ (tensorLeftMap (π j ≫ ι j)).app P = 0
  rw [tensorLeftMap_comp, NatTrans.comp_app, reassoc_of% (hj j), zero_comp]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

attribute [local instance] Abelian.hasFiniteBiproducts

/-- **Lisse sheaves are flat**: the tensor product with a lisse sheaf preserves monomorphisms. -/
theorem IsAdicLisseSheaf.preservesMonomorphisms_tensorLeft {C : AdicSheaf l X}
    (hC : IsAdicLisseSheaf C) : (Mod.tensorLeft C).PreservesMonomorphisms := by
  refine ⟨fun {P Q} f _ ↦ ?_⟩
  obtain ⟨R, hR, hRC⟩ := hC
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine Preadditive.mono_of_isZero_kernel _
    (AdicSheaf.isZero_of_isZero_upperStar g hR fun i ↦ ?_)
  obtain ⟨n, ⟨e⟩⟩ := hRC (g i) (.mk i)
  have := Mod.preservesMonomorphisms_tensorLeft_of_iso_biproduct e
  have hm : Mono ((g i)^*ᵃ[l].map ((Mod.tensorLeft C).map f)) := by
    have key := NatIso.naturality_2 (adicUpperStarTensorLeftIso l (g i) C) f
    change Mono ((Mod.tensorLeft C ⋙ (g i)^*ᵃ[l]).map f)
    rw [← key]
    have : Mono ((g i)^*ᵃ[l].map f) := inferInstance
    infer_instance
  exact (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (g i)^*ᵃ[l] _)

/-- **The internal hom out of a lisse sheaf preserves vanishing after pullback**: if `k^* N = 0`
then `k^* 𝓗om(B, N) = 0`, for `B` lisse and any morphism `k`. On the base change of a cover
trivialising `B`, `𝓗om(B, N)` becomes a finite direct sum of copies of `N`. -/
theorem IsAdicLisseSheaf.isZero_upperStar_ihom {T : Scheme.{u}} (k : T ⟶ X)
    {B N : AdicSheaf l X} (hB : IsAdicLisseSheaf B) (hN : IsZero ((k)^*ᵃ[l].obj N)) :
    IsZero ((k)^*ᵃ[l].obj ((AdicSheaf.ihom B).obj N)) := by
  obtain ⟨R, hR, hRB⟩ := hB
  obtain ⟨κ, V, g, rfl⟩ := R.exists_eq_ofArrows
  have hc := Precoverage.mem_coverings_of_isPullback g hR k (fun t ↦ pullback.fst k (g t))
    (fun t ↦ pullback.snd k (g t)) fun t ↦ IsPullback.of_hasPullback k (g t)
  have (t : κ) : WeaklyEtale (pullback.fst k (g t)) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hc (.mk t)
  refine AdicSheaf.isZero_of_isZero_upperStar (fun t ↦ pullback.fst k (g t)) hc fun t ↦ ?_
  have := Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk t)
  obtain ⟨n, ⟨e⟩⟩ := hRB (g t) (.mk t)
  let p := pullback.fst k (g t)
  let q := pullback.snd k (g t)
  have hpq : p ≫ k = q ≫ g t := pullback.condition
  let c (M : AdicSheaf l X) : (p)^*ᵃ[l].obj ((k)^*ᵃ[l].obj M) ≅ (q)^*ᵃ[l].obj ((g t)^*ᵃ[l].obj M) :=
    (adicUpperStarComp l p k).symm.app _ ≪≫ (adicUpperStarCongr l hpq).app _ ≪≫
      (adicUpperStarComp l q (g t)).app _
  have hz : IsZero ((q)^*ᵃ[l].obj ((g t)^*ᵃ[l].obj N)) :=
    ((p)^*ᵃ[l].map_isZero hN).of_iso (c N).symm
  refine IsZero.of_iso ?_ (c _ ≪≫ (q)^*ᵃ[l].mapIso ((adicUpperStarIhomIso l (g t) B).app N ≪≫
    (Mod.ihomMapIso e).symm.app _ ≪≫ Mod.ihomBiproductIso _ _ ≪≫
    biproduct.mapIso fun _ ↦ Mod.ihomRegularIso.app _) ≪≫ (q)^*ᵃ[l].mapBiproduct _)
  rw [IsZero.iff_id_eq_zero, ← biproduct.total]
  exact Finset.sum_eq_zero fun j _ ↦ by
    erw [hz.eq_of_tgt (biproduct.π (fun _ : Fin n ↦ (q)^*ᵃ[l].obj ((g t)^*ᵃ[l].obj N)) j) 0,
      zero_comp]

end AlgebraicGeometry.ProEtale
