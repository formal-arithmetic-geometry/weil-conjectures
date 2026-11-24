/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteEpimorphism
import WeilConjectures.AlgebraicGeometry.FreeEtaleModuleShriekComparison
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSupport
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.Topology.SpectralConstructibleFiniteIntersection
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Finite presentations of constructible etale module sheaves

## References

* Stacks Project, Tag 095N
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A constructible module sheaf on a qcqs scheme has a presentation by finite sums of
extensions by zero from affine etale objects. The project's `ModuleCat Λ` encoding
of modules over the constant ring sheaf is used; in it `P W` is the sheafification of
`V ↦ Λ[Hom(V,W)]`, with restriction by precomposition; it is `j_{W!} Λ_W`.
(Stacks, Tag 095N) -/
theorem exists_affine_free_etale_presentation
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale),
      (∀ i : Fin n, IsAffine (U i).left) ∧ (∀ j : Fin m, IsAffine (V j).left) ∧
      ∃ (f : (∐ fun j : Fin m => P (V j)) ⟶ (∐ fun i : Fin n => P (U i)))
        (g : (∐ fun i : Fin n => P (U i)) ⟶ F)
        (w : f ≫ g = 0), Nonempty (IsColimit (CokernelCofork.ofπ g w)) := by
  classical
  let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W ↦
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
  have hP (W : X.Etale) (hW : IsAffine W.left) :
      IsConstructibleSheaf (P W) := by
    have : IsAffine W.left := hW
    obtain ⟨e⟩ := free_etale_module_shriek_comparison X Λ W
    have hc := isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant
      (X := X) (U := W.left) W.hom (ModuleCat.of Λ Λ)
    have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hc
    exact IsConstructibleSheaf.of_iso e.symm
  obtain ⟨n, U, hU, g, hg⟩ := exists_affine_free_etale_epimorphism X Λ F hF
  have : Epi g := hg
  have : ∀ i : Fin n, IsConstructibleSheaf (P (U i)) := fun i ↦ hP (U i) (hU i)
  have := Abelian.hasFiniteBiproducts
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have := IsConstructibleSheaf.biproduct (fun i : Fin n ↦ P (U i))
  have := IsConstructibleSheaf.of_iso
    (biproduct.isoCoproduct (fun i : Fin n ↦ P (U i)))
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  have := IsConstructibleSheaf.kernel g
  have hK := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf (kernel g)).mpr
    (inferInstance : IsConstructibleSheaf (kernel g))
  obtain ⟨m, V, hV, h, hh⟩ := exists_affine_free_etale_epimorphism X Λ (kernel g) hK
  have : Epi h := hh
  refine ⟨n, m, U, V, hU, hV, h ≫ kernel.ι g, g, ?_, ?_⟩
  · simp
  · exact ⟨isCokernelEpiComp
      (Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι g) (kernel.condition g)) (kernelIsKernel g)) h rfl⟩

end AlgebraicGeometry.Scheme
