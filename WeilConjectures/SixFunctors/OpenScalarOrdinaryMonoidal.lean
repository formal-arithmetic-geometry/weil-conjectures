/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarTensorData
import all WeilConjectures.AlgebraicGeometry.ProEtaleProjectionFormulaArrows
import WeilConjectures.AlgebraicGeometry.ProEtaleOrdinaryTensorPullbackNaturalComparison
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Strong monoidal ordinary pro-etale inverse image

Source: Stacks Project, Modules on Sites, Tag 03EL.
(blueprint: lem-sp-open-scalar-ordinary-monoidal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

attribute [local instance] SheafOfModules.monoidalCategory


private theorem left_unit_of_right {B : Type*} [Category* B] [MonoidalCategory B]
    [BraidedCategory B] {A : Type*} [Category* A] [MonoidalCategory A]
    [BraidedCategory A] (F : B ⥤ A)
    (μ : ∀ X Y : B, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (a : F.obj (𝟙_ B) ⟶ 𝟙_ A)
    (hβ : ∀ X Y : B, F.map (β_ X Y).hom ≫ μ Y X =
      μ X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (hr : ∀ X : B, μ X (𝟙_ B) ≫ F.obj X ◁ a ≫ (ρ_ (F.obj X)).hom =
      F.map (ρ_ X).hom) (X : B) :
    μ (𝟙_ B) X ≫ a ▷ F.obj X ≫ (λ_ (F.obj X)).hom = F.map (λ_ X).hom := by
  calc
    _ = μ (𝟙_ B) X ≫ (β_ (F.obj (𝟙_ B)) (F.obj X)).hom ≫
        F.obj X ◁ a ≫ (ρ_ (F.obj X)).hom := by
      rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]
    _ = F.map (β_ (𝟙_ B) X).hom ≫ μ X (𝟙_ B) ≫
        F.obj X ◁ a ≫ (ρ_ (F.obj X)).hom := by
      rw [← reassoc_of% (hβ (𝟙_ B) X)]
    _ = _ := by rw [hr, ← F.map_comp, braiding_rightUnitor]

private theorem ordinary_symmetry {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M N : proEtaleRingModules Y R) :
    let L := proEtaleRingModulePullback f R S c
    let μ := proEtaleOrdinaryTensorPullback f R S c
    L.map (β_ M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (β_ (L.obj M) (L.obj N)).hom := by
  let L := proEtaleRingModulePullback f R S c
  let μ := proEtaleOrdinaryTensorPullback f R S c
  let adj := proEtaleRingModuleAdjunction f R S c
  have hμ (A B : proEtaleRingModules Y R) (U : Y.ProEt)
      (x : A.val.obj (Opposite.op U)) (y : B.val.obj (Opposite.op U)) :
      (μ A B).hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          ((adj.unit.app (A ⊗ B)).val.app (Opposite.op U)
            (proEtaleTensorPair Y R A B (Opposite.op U) x y)) =
        proEtaleTensorPair X S (L.obj A) (L.obj B)
          (Opposite.op ((proEtaleBaseChange f).obj U))
          ((adj.unit.app A).val.app (Opposite.op U) x)
          ((adj.unit.app B).val.app (Opposite.op U) y) := by
    simpa only [μ, adj, L, proEtaleOrdinaryTensorPullback, proEtaleOrdinaryTensor,
      curriedTensor] using
      (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists.choose_spec.2
        A B U x y
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  rw [← Category.assoc, adj.unit_naturality]
  apply proEtaleTensorPair_hom_ext Y R
  intro U x y
  let V := Opposite.op ((proEtaleBaseChange f).obj U.unop)
  change (μ N M).hom.val.app V
      ((adj.unit.app (N ⊗ M)).val.app U
        ((β_ M N).hom.val.app U (proEtaleTensorPair Y R M N U x y))) =
    (β_ (L.obj M) (L.obj N)).hom.val.app V
      ((μ M N).hom.val.app V
        ((adj.unit.app (M ⊗ N)).val.app U (proEtaleTensorPair Y R M N U x y)))
  have hb : (β_ M N).hom.val.app U (proEtaleTensorPair Y R M N U x y) =
      proEtaleTensorPair Y R N M U y x := by
    exact CochainPullback.moduleTmul_braiding M N U x y
  rw [hb]
  change (μ N M).hom.val.app V
      ((adj.unit.app (N ⊗ M)).val.app U (proEtaleTensorPair Y R N M U y x)) = _
  rw [hμ N M U.unop y x, hμ M N U.unop x y]
  exact (show (β_ (L.obj M) (L.obj N)).hom.val.app V
    (proEtaleTensorPair X S (L.obj M) (L.obj N) V _ _) = _ from
      CochainPullback.moduleTmul_braiding (L.obj M) (L.obj N) V _ _).symm

/-- The canonical ordinary pro-etale inverse image is strong monoidal, with
its inverse tensorator given by the specified ordinary pullback comparison.
Source: Stacks Project, Modules on Sites, Tag 03EL
(blueprint: lem-sp-open-scalar-ordinary-monoidal).

Proof: take the natural ordinary tensor comparison and the inverse-image unit
comparison. Their known associativity and right-unit formulas give the corresponding
oplax coherence identities. The ordinary tensor comparison preserves the symmetry:
transpose through the module adjunction and evaluate on pure tensors, where both
routes swap the two generators. Symmetry then gives left-unit coherence from the
right-unit identity. Invert these isomorphisms to build a strong monoidal core.
Its oplax tensorator is, by construction, the original comparison. -/
theorem ordinary_monoidal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    ∃ n : (proEtaleRingModulePullback f R S c).Monoidal, letI := n
      ∀ M N : proEtaleRingModules Y R,
        Functor.OplaxMonoidal.δ (proEtaleRingModulePullback f R S c) M N =
          (proEtaleOrdinaryTensorPullback f R S c M N).hom := by
  let L := proEtaleRingModulePullback f R S c
  obtain ⟨ν, hν, hα⟩ := proEtaleOrdinaryTensorPullbackNaturalComparison f R S c
  obtain ⟨j, hj, _⟩ := proEtaleProjectionUnit_existsUnique f R S c
  have hr (M : proEtaleRingModules Y R) :
      ν.hom.app (M, 𝟙_ _) ≫ (L.obj M ◁ j.hom) ≫ (ρ_ (L.obj M)).hom =
        L.map (ρ_ M).hom := by
    rw [hν]
    have hh := hj M
    change (proEtaleOrdinaryTensorPullback f R S c M (𝟙_ _)).hom ≫
      (𝟙 (L.obj M) ⊗ₘ j.hom) ≫ (ρ_ (L.obj M)).hom = L.map (ρ_ M).hom at hh
    rw [CategoryTheory.MonoidalCategory.id_tensorHom (L.obj M) j.hom] at hh
    exact hh
  have hβ (M N : proEtaleRingModules Y R) :
      L.map (β_ M N).hom ≫ ν.hom.app (N, M) =
        ν.hom.app (M, N) ≫ (β_ (L.obj M) (L.obj N)).hom := by
    rw [hν, hν]
    exact ordinary_symmetry f R S c M N
  have hl := left_unit_of_right L
    (fun M N ↦ ν.hom.app (M, N)) j.hom hβ (fun M ↦ by
      simpa only [L, Functor.prod_obj, id_tensorHom] using hr M)
  let core : L.CoreMonoidal := Functor.CoreMonoidal.mk'
    j.symm (fun M N ↦ (ν.app (M,N)).symm)
    (by
      intro M N g H
      have h := ν.hom.naturality (Prod.mkHom g (𝟙 H))
      change L.map (g ⊗ₘ 𝟙 H) ≫ (ν.app (N,H)).hom =
        (ν.app (M,H)).hom ≫ (L.map g ⊗ₘ L.map (𝟙 H)) at h
      have hid : L.map (𝟙 H) = 𝟙 (L.obj H) := L.map_id H
      erw [hid] at h
      have ht : L.map g ⊗ₘ 𝟙 (L.obj H) = L.map g ▷ L.obj H :=
        CategoryTheory.MonoidalCategory.tensorHom_id (L.map g) (L.obj H)
      rw [ht] at h
      rw [tensorHom_id] at h
      exact h.symm)
    (by
      intro M N H g
      have h := ν.hom.naturality (Prod.mkHom (𝟙 H) g)
      change L.map (𝟙 H ⊗ₘ g) ≫ (ν.app (H,N)).hom =
        (ν.app (H,M)).hom ≫ (L.map (𝟙 H) ⊗ₘ L.map g) at h
      have hid : L.map (𝟙 H) = 𝟙 (L.obj H) := L.map_id H
      erw [hid] at h
      have ht : 𝟙 (L.obj H) ⊗ₘ L.map g = L.obj H ◁ L.map g :=
        CategoryTheory.MonoidalCategory.id_tensorHom (L.obj H) (L.map g)
      rw [ht] at h
      rw [id_tensorHom] at h
      exact h.symm)
    (by
      intro M N H
      change ν.hom.app (M ⊗ N,H) ≫ (ν.hom.app (M,N) ▷ L.obj H) ≫
        (α_ (L.obj M) (L.obj N) (L.obj H)).hom =
        L.map (α_ M N H).hom ≫ ν.hom.app (M,N ⊗ H) ≫
          (L.obj M ◁ ν.hom.app (N,H))
      simpa only [← tensorHom_id, ← id_tensorHom] using (hα M N H).symm)
    (by
      intro M
      apply (cancel_mono (λ_ (L.obj M)).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Iso.symm_inv, Iso.app_hom]
      rw [hl, ← L.map_comp, Iso.inv_hom_id, L.map_id])
    (by
      intro M
      apply (cancel_mono (ρ_ (L.obj M)).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Iso.symm_inv, Iso.app_hom]
      rw [hr, ← L.map_comp, Iso.inv_hom_id, L.map_id])
  refine ⟨core.toMonoidal, ?_⟩
  intro M N
  change ν.hom.app (M,N) = (proEtaleOrdinaryTensorPullback f R S c M N).hom
  exact hν M N

end AlgebraicGeometry.ProEtale.OpenScalarTensor
