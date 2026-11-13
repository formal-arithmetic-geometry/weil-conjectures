/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.TorsionControlledAlgebraizationDescentGluing
import WeilConjectures.AlgebraicGeometry.TorsionControlledAlgebraizationDescentBound

/-! # Descent of already constructed torsion-controlled triples

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 00AL](https://stacks.math.columbia.edu/tag/00AL)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Local triples on an open cover descend. The hypothesis supplies actual local
algebraizations, not a torsion condition on the original formal map. -/
theorem torsionControlled_algebraization_descent
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (ι : Type u) (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (γ : ∀ i, ((completion X J).obj H).obj ⋙
      Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι) (Hlocal i).obj)
    (hγ : ∀ (i : ι) (n : ℕ),
      (Scheme.Modules.restrictFunctor (U i).ι).map
          (formalModuleQuotientπ J (n + 1) H.obj) ≫ (γ i).hom.app (op n) =
        eqToHom (hHlocal i).symm ≫
          formalModuleQuotientπ (J.comap (U i).ι) (n + 1) (Hlocal i).obj)
    (hlocal : ∀ i, ∃ (F : CoherentModules (U i).toScheme) (a : F ⟶ Hlocal i)
      (β : N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι) F.obj),
      Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor (U i).ι) ≫ (γ i).hom =
        β.hom ≫ formalCompletionMap (J.comap (U i).ι) a.hom ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (cokernel a.hom)))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a.hom))) := by
  obtain ⟨F, a, β, hfactor, hbound⟩ :=
    torsionControlled_algebraization_descent_gluing J H N δ ι U hcover Hlocal hHlocal γ hγ hlocal
  obtain ⟨s, hs, hsk, hsc⟩ :=
    torsionControlled_algebraization_descent_bound J H F a ι U hcover hbound
  exact ⟨F, a, β, hfactor, ⟨s, hs, hsk, hsc⟩⟩

end AlgebraicGeometry
