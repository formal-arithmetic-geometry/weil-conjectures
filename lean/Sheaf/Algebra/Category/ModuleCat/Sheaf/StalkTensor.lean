/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings
import Sheaf.Topology.PresheafModuleStalkFunctor

/-!
# Stalk of a tensor product of modules on a ringed space

Source: Stacks Project, Modules, Lemma 17.16.1 (Tag 01CB,
label lemma-stalk-tensor-product) (blueprint: lem-pc-ringed-space-module-stalk-tensor).
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite

universe u

namespace SheafOfModules

set_option autoImplicit false

noncomputable section

/-- The canonical tensor comparison on stalks is linear and natural in both sheaves.
Source: Stacks Project, Modules, Lemma 17.16.1 (Tag 01CB)
(blueprint: lem-pc-ringed-space-module-stalk-tensor).

Proof:
1. Neighbourhoods of `x` are directed. Module stalks are colimits, with scalar action
   on germs as in `def-weil-pbc-module-stalk`; the presheaf tensor is sectionwise
   (`def-pur-sheaf-tensor-product`).
2. The sheafification unit induces an additive isomorphism on stalks
   (`def-weil-presheaf-modules-sheafification`, `lem-weil-pbc-stalk-sheafification-space`).
   Represent a scalar and a vector on a common neighbourhood to see it is linear.
3. Apply `lem-weil-pbc-filtered-colimit-tensor-varying-rings` to the rings and modules
   on neighbourhoods. This identifies the presheaf tensor stalk with the tensor of
   the stalks, sending the germ of a pure tensor to the tensor of its germs.
4. Compose this identification with the inverse of the sheafification stalk map.
   Pure tensor germs generate, so the displayed germ formula characterizes the map.
5. Both sides of the naturality equation send each pure tensor germ to the tensor
   of its image germs (`def-weil-pbc-module-stalk`). Generation gives equality. -/
theorem stalkTensorIso (X : AlgebraicGeometry.RingedSpace.{u}) (x : X) :
    let R := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf
    letI := monoidalCategory X.sheaf
    let S := AlgebraicGeometry.RingedSpace.moduleStalkFunctor X x
    ∃ Φ : ∀ F G : SheafOfModules.{u} R, S.obj (F ⊗ G) ≅ S.obj F ⊗ S.obj G,
      (∀ (F G : SheafOfModules.{u} R) (U : Opens X) (hx : x ∈ U)
        (s : F.val.obj (op U)) (t : G.val.obj (op U)),
        let P := F.val ⊗ G.val
        let θ := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P ≫
          (forget R).map (tensorObjIsoSheafification F G).inv
        (Φ F G).hom (TopCat.Presheaf.germ (F ⊗ G).val.presheaf U x hx
          ((θ.app (op U)) (s ⊗ₜ[X.presheaf.obj (op U)] t))) =
          (TopCat.Presheaf.germ F.val.presheaf U x hx s) ⊗ₜ[X.presheaf.stalk x]
            (TopCat.Presheaf.germ G.val.presheaf U x hx t)) ∧
      (∀ (F G F' G' : SheafOfModules.{u} R) (f : F ⟶ F') (g : G ⟶ G'),
        S.map (f ⊗ₘ g) ≫ (Φ F' G').hom =
          (Φ F G).hom ≫ (S.map f ⊗ₘ S.map g)) := by
  sorry

end

end SheafOfModules
