/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.AlgebraicGeometry.TorsionControlledEasyAlgebraizationBridge
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilated
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Limits
import WeilConjectures.AlgebraicGeometry.Coherent

/-! # Construction of a torsion-controlled algebraization

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0ALK](https://stacks.math.columbia.edu/tag/0ALK)
* [Stacks Project, Tag 05EU](https://stacks.math.columbia.edu/tag/05EU)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Construct one torsion-controlled triple from torsion of the affine limit maps.
This statement has no uniqueness conclusion and does not assert that an arbitrary
algebraization has torsion kernel and cokernel before completion.
-/
theorem torsionControlled_algebraization_construction
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (hlocal : ∀ U : X.affineOpens, ∃ t : ℕ, 1 ≤ t ∧
      J.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight δ.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom) ∧
      J.ideal U ^ t ≤ Module.annihilator Γ(X, U.1)
        (↥(limit (((completion X J).obj H).obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op U.1)) :
          ModuleCat Γ(X, U.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight δ.hom
            (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom)) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))) := by
  have htorsion := ((coherentFormalModule_annihilated_iff X J J N
    ((completion X J).obj H) δ).out 2 1).mp hlocal
  obtain ⟨F, a, β, hδ, ha⟩ :=
    torsionControlled_easy_algebraization_bridge J H N δ htorsion
  exact ⟨F, a, β, hδ, ha⟩

end AlgebraicGeometry
