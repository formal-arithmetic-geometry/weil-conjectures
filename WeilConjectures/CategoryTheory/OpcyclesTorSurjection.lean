/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.OpcyclesTorKernelIso
import WeilConjectures.CategoryTheory.TensorHomologyImageKernelEpi

/-!
# Tor of an opcycle cokernel

Source: Stacks Project, More on Algebra, Lemma 15.59.2 (Tag 0653), Tor argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- For a complex of flat modules,
the cohomology one degree before an opcycle cokernel surjects naturally onto its first Tor.
Source: Stacks Project, More on Algebra, Tag 0653. -/
theorem exists_epi_homology_tensor_to_tor_opcycles
    (A : Type u) [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : ℤ) (hflat : ∀ i : ℤ, Module.Flat A (P.X i)) :
    ∃ τ : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0 ⋙
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).map₂CochainComplex).obj P ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) (a - 1)) ⟶
        (Tor' (ModuleCat.{u} A) 1).obj (P.opcycles a),
      ∀ N : ModuleCat.{u} A, Epi (τ.app N) := by
  obtain ⟨e⟩ := nonempty_tor_opcycles_tensor_image_kernel_iso A P a (hflat a)
  obtain ⟨σ, hσ⟩ := exists_epi_tensor_homology_to_image_kernel A P a
  refine ⟨σ ≫ e.inv, fun N ↦ ?_⟩
  have : Epi (σ.app N) := hσ N
  change Epi (σ.app N ≫ e.inv.app N)
  infer_instance

end CategoryTheory
