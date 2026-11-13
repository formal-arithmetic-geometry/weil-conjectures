/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality

/-! # Tensor-pullback sections restricted to opens

## References

* Stacks Project, Tags 03DR, 0095 and 0096
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor-pullback sections restricted to open subschemes recover the additive
section presheaf of the original module. Quasi-coherence is not needed
(Stacks, Tags 03DR, 0095 and 0096). -/
theorem nonempty_etaleTensor_openSections_iso
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (F : X.Modules) :
    Nonempty (i.op ⋙ etaleTensorSectionsPresheaf F ≅
      F.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}) := by
  exact ⟨NatIso.ofComponents (etaleTensorOpenSectionIso X i hi F)
    (fun f ↦ etaleTensorOpenSectionIso_naturality X i hi F f)⟩

end AlgebraicGeometry.Scheme.Modules
