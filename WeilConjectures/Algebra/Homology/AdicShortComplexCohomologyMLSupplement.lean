/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.Algebra.Homology.AdicShortComplexCohomologyML

/-! # Mittag--Leffler cohomology of adic quotient complexes

Source: Stacks Project, Tag 09C5; the Artin--Rees argument is Tag 00IN.
(blueprint: lem-sfb-adic-short-complex-cohomology-ml).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AdicCohomology

variable {R : Type u} [CommRing R] (I : Ideal R)

instance (n : ℕ) : (quotient I n).Additive where
  map_add := by
    intro M N f g
    ext x
    exact Submodule.Quotient.induction_on _ x (fun _ ↦ rfl)

/-- The canonical map from a module to its quotient.
Source: Stacks Project, Tag 09C5.
(blueprint: lem-sfb-adic-short-complex-cohomology-ml). -/
def projection (n : ℕ) : 𝟭 (ModuleCat.{u} R) ⟶ quotient I n where
  app M := ModuleCat.ofHom (power I M n).mkQ
  naturality := by
    intro M N f
    ext x; rfl

private theorem cycle_correction [IsNoetherianRing R]
    {M N : ModuleCat.{u} R} [Module.Finite R N] (d : M ⟶ N) :
    ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m → ∀ z : M,
      d z ∈ power I N m → ∃ x : M, d x = 0 ∧ z - x ∈ power I M n := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range d.hom)
  refine ⟨c, fun n m hnm z hz ↦ ?_⟩
  have hc' : c ≤ m := by omega
  have hdz : d z ∈ I ^ (m - c) • LinearMap.range d.hom := by
    have hmem : d z ∈ power I N m ⊓ LinearMap.range d.hom := ⟨hz, ⟨z, rfl⟩⟩
    rw [hc m hc'] at hmem
    exact (show I ^ (m - c) • (I ^ c • ⊤ ⊓ LinearMap.range d.hom) ≤
      I ^ (m - c) • LinearMap.range d.hom from smul_mono_right _ inf_le_right) hmem
  have hdz' : d z ∈ (power I M n).map d.hom := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact (Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (show n ≤ m - c by omega))) hdz
  obtain ⟨y, hy, he⟩ := hdz'
  refine ⟨z - y, ?_, ?_⟩
  · simp only [map_sub, he, sub_self]
  · rw [sub_sub_cancel]
    exact hy

private def cycle (S : ShortComplex (ModuleCat.{u} R)) (x : S.X₂) (hx : S.g x = 0) :
    S.cycles :=
  S.moduleCatCyclesIso.inv ⟨x, hx⟩

private theorem cycle_i (S : ShortComplex (ModuleCat.{u} R)) (x : S.X₂)
    (hx : S.g x = 0) : S.iCycles (cycle S x hx) = x := by
  change (S.moduleCatCyclesIso.inv ≫ S.iCycles) ⟨x, hx⟩ = x
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl

private def cl (S : ShortComplex (ModuleCat.{u} R)) (x : S.X₂) (hx : S.g x = 0) :
    S.homology := S.homologyπ (cycle S x hx)

private theorem class_surjective (S : ShortComplex (ModuleCat.{u} R)) (a : S.homology) :
    ∃ (x : S.X₂) (hx : S.g x = 0), cl S x hx = a := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance a
  refine ⟨S.iCycles z, ?_, ?_⟩
  · have h := congrArg (fun f ↦ f z) S.iCycles_g
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
  · change S.homologyπ (cycle _ _ _) = S.homologyπ z
    apply congrArg (fun w ↦ S.homologyπ w)
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    exact cycle_i _ _ _

private theorem cl_naturality {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T)
    (x : S.X₂) (hx : S.g x = 0) (hy : T.g (f.τ₂ x) = 0) :
    ShortComplex.homologyMap f (cl S x hx) = cl T (f.τ₂ x) hy := by
  have hcyc : ShortComplex.cyclesMap f (cycle S x hx) = cycle T (f.τ₂ x) hy := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [cycle_i, ← ModuleCat.comp_apply, ShortComplex.cyclesMap_i,
      ModuleCat.comp_apply, cycle_i]
  dsimp only [cl]
  rw [← ModuleCat.comp_apply, ShortComplex.homologyπ_naturality,
    ModuleCat.comp_apply, hcyc]

variable {S₀ : Type u} [CommRing S₀]

private theorem map_range_le (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S₀)
    [F.Additive] [F.PreservesHomology]
    {M N P : ModuleCat.{u} R} (f : M ⟶ P) (g : N ⟶ P)
    (h : Set.range f ⊆ Set.range g) : Set.range (F.map f) ⊆ Set.range (F.map g) := by
  let C := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  have he : C.Exact := ShortComplex.cokernelSequence_exact g
  have he' := he.map F
  have hz : f ≫ cokernel.π g = 0 := by
    ext x
    obtain ⟨y, hy⟩ := h (Set.mem_range_self x)
    rw [ModuleCat.comp_apply, ← hy]
    exact congrArg (fun k ↦ k y) (cokernel.condition g)
  rintro _ ⟨x, rfl⟩
  apply (ShortComplex.moduleCat_exact_iff (C.map F)).mp he'
  change (F.map (cokernel.π g)) ((F.map f) x) = 0
  have hzero := congrArg (fun k ↦ k x) (F.congr_map hz)
  simpa only [Functor.map_comp, Functor.map_zero, ModuleCat.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] using hzero

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

instance (U : C) : (sections (R := R) J U).Additive := by
  dsimp [sections]
  infer_instance

end AdicCohomology
