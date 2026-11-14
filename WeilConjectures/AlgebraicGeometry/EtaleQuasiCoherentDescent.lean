/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsHomComparison

/-!
# Étale descent for sections of quasi-coherent modules

## References

* Stacks Project, Tags 03DR and 03DT
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- The presheaf `u : U ⟶ X ↦ Γ(U, u^*F)`, with pullback restrictions, is a sheaf on
`X.smallEtaleTopology` when `F` is quasi-coherent (Stacks, Tags 03DR and 03DT). -/
theorem isSheaf_etaleTensorSectionsPresheaf {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf X.smallEtaleTopology (etaleTensorSectionsPresheaf F) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat)
  rw [isSheaf_iff_isSheaf_of_type]
  obtain ⟨e⟩ := nonempty_etaleTensorSectionsHomIso F
  exact Presieve.isSheaf_iso _ e.symm
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_etaleHom (unitObj X) F))

end AlgebraicGeometry.Scheme.Modules
