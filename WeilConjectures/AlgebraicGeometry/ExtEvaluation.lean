/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor

/-!
# Evaluation for finite locally free module sheaves
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finite locally free module sheaf, the canonical evaluation identifies tensoring
with the dual and internal sheaf Hom, naturally in the coefficient module. -/
theorem dual_tensor_hom_iso (X : Scheme.{u}) (F : X.Modules)
    [F.IsFiniteLocallyFree] :
    ∃ e : (∀ G : X.Modules, Scheme.Modules.tensorObj (dual F) G ≅ homObj F G),
      (∀ G : X.Modules, (e G).hom = dualTensorHom F G) ∧
      ∀ {G H : X.Modules} (g : G ⟶ H),
        (e G).hom ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 F) g =
          (dual F ◁ g) ≫ (e H).hom := by
  refine ⟨fun G ↦ asIso (dualTensorHom F G), fun G ↦ rfl, ?_⟩
  intro G H g
  exact (dualTensorHom_naturality_right F g).symm

end AlgebraicGeometry.Scheme.Modules
