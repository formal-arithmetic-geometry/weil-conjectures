/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleArrowDescent
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePresentation
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of constructible module sheaves along inverse limits

## References

* Stacks Project, Tag 09YU (3)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A constructible etale sheaf of modules over a finite commutative ring on the limit
of a directed inverse system of qcqs schemes with affine transitions descends to a
constructible module sheaf at one stage, up to module-sheaf isomorphism.
(Stacks, Tag 09YU (3), essential surjectivity) -/
theorem exists_constructible_etaleModuleSheaf_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    ∃ (i : I) (Fᵢ : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsConstructibleEtaleModuleSheaf Fᵢ ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj Fᵢ ≅ F) := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let i₀ : I := Classical.choice inferInstance
  have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app D c hc (op i₀)
  have : QuasiSeparatedSpace c.pt :=
    quasiSeparatedSpace_of_quasiSeparated (c.π.app (op i₀))
  obtain ⟨n, m, U, V, hU, hV, f, g, w, ⟨hg⟩⟩ :=
    exists_affine_free_etale_presentation c.pt Λ F hF
  obtain ⟨i, A, B, a, hA, hB, eA, eB, ha⟩ :=
    exists_affine_free_etaleModule_arrow_descent D c hc Λ n m U V hU hV f
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf A).mp hA
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf B).mp hB
  have hC : IsConstructibleEtaleModuleSheaf (cokernel a) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf (cokernel a)).mpr
      (IsConstructibleSheaf.cokernel a)
  refine ⟨i, cokernel a, hC, ?_⟩
  let L := Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))
  exact ⟨PreservesCokernel.iso L a ≪≫ cokernel.mapIso (L.map a) f eA eB ha ≪≫
    (colimit.isColimit (parallelPair f 0)).coconePointUniqueUpToIso hg⟩

end AlgebraicGeometry.Scheme
